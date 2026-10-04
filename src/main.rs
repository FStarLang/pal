use std::{
    collections::HashSet,
    path::{Path, PathBuf},
    time::Instant,
};

use crate::{
    diag::{Diagnostic, DiagnosticLevel, Diagnostics},
    ir::Location,
    vfs::{OverlayFS, RealFS, VFS},
};
use clap::Parser;

mod clang;
mod diag;
mod env;
mod hauntedc;
mod ir;
mod layout;
mod layout_info;
mod mayberc;
mod pass;
mod prims;
mod source_range_info;
mod vfs;

#[derive(Parser)]
#[command(about = "Translate C source files to verified Pulse/F* code")]
struct Cli {
    #[arg(long = "tmpdir", help = "Directory for intermediate temporary files")]
    tmpdir: Option<String>,

    #[arg(
        long = "outdir",
        short = 'o',
        help = "Output directory for generated .fst files"
    )]
    outdir: Option<String>,

    #[arg(
        long = "print-ir",
        help = "Print the intermediate representation and exit"
    )]
    print_ir: bool,

    #[arg(
        long = "time-passes",
        help = "Show timing information for each compiler pass"
    )]
    time_passes: bool,

    #[arg(
        long = "old-model",
        help = "Emit against the previous memory model instead of Palow"
    )]
    old_model: bool,

    #[arg(
        long = "palow-permissive",
        help = "Report Palow's untranslated constructs as comments only, not as errors"
    )]
    palow_permissive: bool,

    #[arg(long = "quiet", short = 'q', help = "Suppress diagnostic output")]
    quiet: bool,

    #[arg(short = 'I', help = "Additional include search paths")]
    include_paths: Vec<String>,

    #[arg(
        short = 'D',
        help = "Preprocessor definitions, e.g. -DFOO or -DFOO=bar"
    )]
    defines: Vec<String>,

    #[arg(
        long = "target",
        value_name = "TRIPLE",
        help = "Translate for this target, e.g. mips64-unknown-elf, instead of clang's default"
    )]
    target: Option<String>,

    #[arg(
        long = "clang-arg",
        value_name = "ARG",
        allow_hyphen_values = true,
        help = "Pass an argument to clang unchanged; repeat for several"
    )]
    clang_args: Vec<String>,

    #[arg(help = "C source files to translate")]
    files: Vec<String>,
}

/// On macOS, system headers live in an SDK. Looking up the SDK path using
/// `xcrun` and setting SDKROOT.
#[cfg(target_os = "macos")]
fn set_default_sdkroot() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    if std::env::var_os("SDKROOT").is_some() {
        return;
    }
    let Ok(out) = std::process::Command::new("xcrun")
        .args(["--sdk", "macosx", "--show-sdk-path"])
        .output()
    else {
        return;
    };
    if !out.status.success() {
        return;
    }
    let path = OsStr::from_bytes(out.stdout.trim_ascii());
    if !path.is_empty() {
        // SAFETY: called at the top of main, before any threads exist.
        unsafe { std::env::set_var("SDKROOT", path) };
    }
}

/// Write `contents` to `path` only if the file doesn't already exist with
/// identical contents. This avoids bumping the timestamp and triggering
/// unnecessary F* reverification.
fn write_if_changed(path: &PathBuf, contents: &[u8]) {
    if let Ok(existing) = std::fs::read(path) {
        if existing == contents {
            return;
        }
    }
    std::fs::write(path, contents).unwrap();
}

/// `preprocessor.json`: one record per compilation of an input file, each
/// already JSON (see doc/internals.md).
fn serialize_preprocessor_records(records: &[String]) -> String {
    format!("{{\"units\":[\n{}\n]}}\n", records.join(",\n"))
}

fn serialize_diags(diags: &Diagnostics) -> String {
    use std::collections::{BTreeMap, HashMap};

    // Group diagnostics by source file
    let mut by_file: HashMap<&str, Vec<lsp_types::Diagnostic>> = HashMap::new();
    for diag in &diags.diags {
        by_file
            .entry(&diag.loc.file_name)
            .or_default()
            .push(Diagnostic::to_lsp(diag));
    }

    // Serialize as { "file://...": [...], ... }
    let result: BTreeMap<String, Vec<lsp_types::Diagnostic>> = by_file
        .into_iter()
        .map(|(file, diags)| {
            let uri = if file.starts_with('/') {
                format!("file://{}", file)
            } else {
                format!("file:///{}", file)
            };
            (uri, diags)
        })
        .collect();

    serde_json::to_string_pretty(&result).unwrap()
}

fn same_target(a: &ir::TranslationUnit, b: &ir::TranslationUnit) -> bool {
    a.target_triple == b.target_triple
        && a.big_endian == b.big_endian
        && a.pointer_size == b.pointer_size
}

fn describe_target(tu: &ir::TranslationUnit) -> String {
    format!(
        "`{}` ({}-endian, {}-byte pointers)",
        tu.target_triple,
        if tu.big_endian { "big" } else { "little" },
        tu.pointer_size
    )
}

fn main() {
    #[cfg(target_os = "macos")]
    set_default_sdkroot();

    let cli = Cli::parse();

    if cli.files.is_empty() {
        eprintln!("error: no input files");
        std::process::exit(1);
    }

    let mut vfs: Box<dyn VFS>;
    match &cli.tmpdir {
        Some(tmpdir) => {
            let mut overlayfs = OverlayFS::new(RealFS::new());
            let tmpdir = Path::new(tmpdir);
            for file in &cli.files {
                let file_name = std::path::absolute(file)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned();
                let contents = String::from_utf8(
                    std::fs::read(tmpdir.join(Path::new(&file_name).file_name().unwrap())).unwrap(),
                )
                .unwrap();
                overlayfs.add_overlay(file_name, contents);
            }
            vfs = Box::new(overlayfs);
        }
        None => {
            vfs = Box::new(RealFS::new());
        }
    }

    // Parse all input files and combine into a single TranslationUnit
    let mut combined_tu = ir::TranslationUnit {
        main_file_names: Vec::new(),
        decls: Vec::new(),
        layouts: ir::LayoutTable::new(),
        pointer_size: 8,
        target_triple: "".into(),
        big_endian: false,
    };
    let mut diags = Diagnostics::empty();
    let mut preprocessor_records: Vec<String> = Vec::new();

    // A source can be translated for either memory model, and hand-written
    // Pulse in it names predicates only one of them has. `PALOW` lets the
    // source say which fragment is which.
    // The source's own `-D` flags, and on top of them the one that says which
    // memory model this is. `--palow` defines `PALOW`, so hand-written Pulse
    // that names predicates only one of the two models has can be written
    // twice in the one file.
    let mut defines: Vec<String> = cli.defines.clone();
    if !cli.old_model {
        defines.push("PALOW".to_string());
    }

    let parse_start = Instant::now();
    for file in &cli.files {
        let file_name = std::path::absolute(file)
            .unwrap()
            .to_string_lossy()
            .into_owned();

        if let Err(error) = vfs.read_vfs_file(&file_name) {
            eprintln!("Cannot open {}: {}", file_name, error);
            std::process::exit(1);
        }

        let (tu, file_diags, records) = clang::parse_file(
            &file_name,
            &cli.include_paths,
            &defines,
            cli.target.as_deref(),
            &cli.clang_args,
            &mut *vfs,
        );
        // The files become one translation unit with one layout table, so they
        // have to have been compiled for one target. Each finds its own
        // compilation database, and two databases can disagree. A file clang
        // gave up on before choosing a target has already said why.
        if !tu.target_triple.is_empty() {
            if combined_tu.target_triple.is_empty() {
                combined_tu.target_triple = tu.target_triple.clone();
                combined_tu.big_endian = tu.big_endian;
                combined_tu.pointer_size = tu.pointer_size;
            } else if !same_target(&combined_tu, &tu) {
                eprintln!(
                    "error: {} was compiled for {}, but {} for {}; pass --target to choose one",
                    combined_tu.main_file_names[0],
                    describe_target(&combined_tu),
                    file_name,
                    describe_target(&tu)
                );
                std::process::exit(1);
            }
        }
        combined_tu
            .main_file_names
            .push(tu.main_file_names[0].clone());
        combined_tu.decls.extend(tu.decls);
        combined_tu.layouts.extend(tu.layouts);
        diags.merge(file_diags);
        preprocessor_records.extend(records);
    }
    if cli.time_passes {
        eprintln!(
            "  parse ({} files, {} decls): {:.3}s",
            cli.files.len(),
            combined_tu.decls.len(),
            parse_start.elapsed().as_secs_f64()
        );
    }

    // Before `prune`, which keeps only what the output uses: see layout_info.
    let layout_snapshot = (!cli.old_model).then(|| layout_info::Snapshot::take(&combined_tu));

    // Run passes
    let t = Instant::now();
    pass::prune::prune(&mut combined_tu);
    if cli.time_passes {
        eprintln!(
            "  prune ({} decls): {:.3}s",
            combined_tu.decls.len(),
            t.elapsed().as_secs_f64()
        );
    }

    let t = Instant::now();
    pass::merge::merge(&mut diags, &mut combined_tu, !cli.old_model);
    if cli.time_passes {
        eprintln!(
            "  merge ({} decls): {:.3}s",
            combined_tu.decls.len(),
            t.elapsed().as_secs_f64()
        );
    }

    // Scope checking waits until after `merge`, because a definition and its
    // declaration are separate declarations until then. C lets the two name
    // their parameters differently, and `_Use_decl_annotations_` gives the
    // definition the declaration's annotations, so between parsing and merging
    // a parameter refinement can legitimately mention a name the enclosing
    // declaration does not bind. `merge` is what reconciles the two.
    let t = Instant::now();
    pass::check::check(&mut diags, &mut combined_tu, "merge", false);
    if cli.time_passes {
        eprintln!("  check (post-merge): {:.3}s", t.elapsed().as_secs_f64());
    }

    let t = Instant::now();
    pass::restructure_goto::restructure_goto(&mut diags, &mut combined_tu);
    if cli.time_passes {
        eprintln!("  restructure_goto: {:.3}s", t.elapsed().as_secs_f64());
    }

    let t = Instant::now();
    pass::decay::decay(&mut combined_tu);
    if cli.time_passes {
        eprintln!("  decay: {:.3}s", t.elapsed().as_secs_f64());
    }

    let t = Instant::now();
    pass::elab::elab(&mut diags, &mut combined_tu);
    if cli.time_passes {
        eprintln!("  elab: {:.3}s", t.elapsed().as_secs_f64());
    }

    let t = Instant::now();
    pass::normalize_casts::normalize_casts(&mut combined_tu);
    if cli.time_passes {
        eprintln!("  normalize_casts: {:.3}s", t.elapsed().as_secs_f64());
    }

    let t = Instant::now();
    pass::check::check(&mut diags, &mut combined_tu, "normalize_casts", true);
    if cli.time_passes {
        eprintln!(
            "  check (post-normalize_casts): {:.3}s",
            t.elapsed().as_secs_f64()
        );
    }

    let t = Instant::now();
    pass::elim_cis::elim_simple_cis(&mut diags, &mut combined_tu);
    if cli.time_passes {
        eprintln!("  elim_cis: {:.3}s", t.elapsed().as_secs_f64());
    }

    let t = Instant::now();
    pass::check::check(&mut diags, &mut combined_tu, "elim_cis", true);
    if cli.time_passes {
        eprintln!("  check (post-elim_cis): {:.3}s", t.elapsed().as_secs_f64());
    }

    if cli.print_ir {
        println!("{}", combined_tu);
        return;
    }

    if !cli.old_model {
        // Palow's pointers and `size_t` are eight bytes. For a target whose
        // are not, the model would describe a different program from the one
        // the compiler builds, so there is no translation to give. The byte
        // order is the target's either way: the translation states it, in
        // `Pulse.Lib.C.Palow.Target`.
        if !combined_tu.target_triple.is_empty() && combined_tu.pointer_size != 8 {
            eprintln!(
                "error: the target is {}, and Palow models only targets with 8-byte pointers",
                describe_target(&combined_tu)
            );
            std::process::exit(1);
        }
        // A test whose hand-written Pulse is written against the *old* memory
        // model marks itself, and Palow leaves those fragments alone rather
        // than splicing text that names predicates it does not have.
        //
        // There are two such markers and the difference between them is the
        // whole point. `palow-old-annotations` is a backlog: the fragment
        // could be written in this model and has not been yet, so the count is
        // meant to reach zero. `palow-model-specific` is not: the test exists
        // to exercise something the old model has and this one deliberately
        // does not -- `_core_ref`, the `$fold`/`$unfold` antiquotations that
        // name generated struct helpers -- so it will carry its marker for as
        // long as the old emitter is around. Counting the two together would
        // make a permanent floor look like unfinished work.
        let marked = |name: &str| {
            cli.files
                .first()
                .map(|f| {
                    Path::new(f)
                        .parent()
                        .unwrap_or(Path::new("."))
                        .join(name)
                        .exists()
                })
                .unwrap_or(false)
        };
        let model_specific = marked("palow-model-specific");
        let splice_inline = !marked("palow-old-annotations") && !model_specific;
        let modules = pass::emit_palow::emit_palow(&combined_tu, splice_inline, model_specific);
        // A gap the generated file owns up to is still a gap. While the
        // translation was being built, saying so in a comment was the point:
        // the comment is what made the coverage measurable, and turning a
        // missing feature into a hard failure would have stopped the whole
        // suite on the first one. There is nothing left to measure, so the
        // comment becomes an error -- a specification that is quietly weaker
        // than the one the user wrote is the failure mode this model exists to
        // rule out, and it should not be possible to get one by accident.
        // `--palow-permissive` is for a measurement run, which wants the
        // comments and the count back.
        if !cli.palow_permissive {
            for module in &modules {
                for why in pass::emit_palow::weakenings(module) {
                    let loc = match &module.origin {
                        Some(o) => Location {
                            file_name: o.file.clone(),
                            range: o.range,
                        },
                        None => {
                            let z = crate::ir::Position {
                                line: 1,
                                character: 1,
                            };
                            Location {
                                file_name: cli.files.first().cloned().unwrap_or_default().into(),
                                range: crate::ir::Range { start: z, end: z },
                            }
                        }
                    };
                    diags.report(Diagnostic {
                        loc,
                        level: DiagnosticLevel::Error,
                        msg: format!("`{}`: {}", module.module_name, why),
                    });
                }
            }
        }
        if let Some(outdir) = &cli.outdir {
            let outdir = Path::new(&outdir).to_path_buf();
            std::fs::create_dir_all(&outdir).unwrap();
            let mut generated_files: HashSet<PathBuf> = HashSet::new();
            for module in &modules {
                let path = outdir.join(format!("{}.fst", module.module_name));
                write_if_changed(&path, module.code.as_bytes());
                generated_files.insert(path);
                if let Some(iface) = &module.iface {
                    let path = outdir.join(format!("{}.fsti", module.module_name));
                    write_if_changed(&path, iface.as_bytes());
                    generated_files.insert(path);
                }
            }
            // The same three files the old translator writes, for the same
            // reason: an IDE pointed at the output directory expects to find
            // them, and `TranslationErrors` is what makes a translation
            // failure a *verification* failure rather than a silent gap.
            let errors_path = outdir.join("TranslationErrors.fst");
            write_if_changed(
                &errors_path,
                {
                    let mut errors_code = "module TranslationErrors\n".to_string();
                    if diags.has_errors() {
                        errors_code += "let _ = assert False\n";
                    }
                    errors_code
                }
                .as_bytes(),
            );
            generated_files.insert(errors_path);
            std::fs::write(
                outdir.join("source_range_info.json"),
                source_range_info::serialize_palow(&modules),
            )
            .unwrap();
            if let Some(snapshot) = &layout_snapshot {
                std::fs::write(outdir.join("layout_table.json"), snapshot.serialize()).unwrap();
            }
            std::fs::write(
                outdir.join("preprocessor.json"),
                serialize_preprocessor_records(&preprocessor_records),
            )
            .unwrap();
            std::fs::write(outdir.join("diagnostics.json"), &serialize_diags(&diags)).unwrap();
            // A module that is no longer generated has to go, or the next
            // verification run picks up a stale one and succeeds on code that
            // no longer exists.
            if let Ok(entries) = std::fs::read_dir(&outdir) {
                for entry in entries.flatten() {
                    let path = entry.path();
                    if let Some(ext) = path.extension() {
                        if (ext == "fst" || ext == "fsti") && !generated_files.contains(&path) {
                            let _ = std::fs::remove_file(&path);
                        }
                    }
                }
            }
        } else {
            for module in &modules {
                println!("{}", module.code);
            }
        }
        if !cli.quiet {
            diags.print_to_stderr(&mut *vfs);
        }
        return;
    }

    // Emit per-declaration modules
    let t = Instant::now();
    let modules = pass::emit::emit_multifile(&mut diags, &combined_tu);
    if cli.time_passes {
        eprintln!(
            "  emit ({} modules): {:.3}s",
            modules.len(),
            t.elapsed().as_secs_f64()
        );
    }

    if let Some(outdir) = &cli.outdir {
        let outdir = Path::new(&outdir).to_path_buf();
        std::fs::create_dir_all(&outdir).unwrap();

        // Track which .fst/.fsti files we generate this run
        let mut generated_files: HashSet<PathBuf> = HashSet::new();

        for module in &modules {
            let fst_path = outdir.join(format!("{}.fst", module.module_name));
            write_if_changed(&fst_path, module.code.as_bytes());
            generated_files.insert(fst_path);
            if let Some(fsti_code) = &module.fsti_code {
                let fsti_path = outdir.join(format!("{}.fsti", module.module_name));
                write_if_changed(&fsti_path, fsti_code.as_bytes());
                generated_files.insert(fsti_path);
            }
        }

        // Write TranslationErrors.fst — asserts False when there are errors so
        // that F* reports a failure, but individual modules remain verifiable.
        let errors_path = outdir.join("TranslationErrors.fst");
        write_if_changed(
            &errors_path,
            {
                let mut errors_code = "module TranslationErrors\n".to_string();
                if diags.has_errors() {
                    errors_code += "let _ = assert False\n";
                }
                errors_code
            }
            .as_bytes(),
        );
        generated_files.insert(errors_path);

        // Write single unified source_range_info.json
        std::fs::write(
            outdir.join("source_range_info.json"),
            source_range_info::serialize(&modules),
        )
        .unwrap();

        std::fs::write(
            outdir.join("preprocessor.json"),
            serialize_preprocessor_records(&preprocessor_records),
        )
        .unwrap();

        // Write diagnostics
        std::fs::write(outdir.join("diagnostics.json"), &serialize_diags(&diags)).unwrap();

        // Remove stale .fst/.fsti files from previous runs
        if let Ok(entries) = std::fs::read_dir(&outdir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if let Some(ext) = path.extension() {
                    if (ext == "fst" || ext == "fsti") && !generated_files.contains(&path) {
                        let _ = std::fs::remove_file(&path);
                    }
                }
            }
        }
    } else {
        eprintln!("Not saving generated Pulse output, specify --outdir to create files");
    }

    if !cli.quiet {
        diags.print_to_stderr(&mut *vfs);
    }
    if diags.has_errors() {
        std::process::exit(0)
    }
}
