use std::{
    collections::HashSet,
    path::{Path, PathBuf},
    time::Instant,
};

use crate::{
    diag::{Diagnostic, Diagnostics},
    vfs::{OverlayFS, RealFS, VFS},
};
use clap::Parser;

mod clang;
mod diag;
mod env;
mod hauntedc;
mod ir;
mod mayberc;
mod pass;
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

    #[arg(long = "quiet", short = 'q', help = "Suppress diagnostic output")]
    quiet: bool,

    #[arg(short = 'I', help = "Additional include search paths")]
    include_paths: Vec<String>,

    #[arg(help = "C source files to translate")]
    files: Vec<String>,
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

fn main() {
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
    };
    let mut diags = Diagnostics::empty();

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

        let (tu, file_diags) = clang::parse_file(&file_name, &cli.include_paths, &mut *vfs);
        combined_tu
            .main_file_names
            .push(tu.main_file_names[0].clone());
        combined_tu.decls.extend(tu.decls);
        diags.merge(file_diags);
    }
    if cli.time_passes {
        eprintln!(
            "  parse ({} files, {} decls): {:.3}s",
            cli.files.len(),
            combined_tu.decls.len(),
            parse_start.elapsed().as_secs_f64()
        );
    }

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
    pass::check::check(&mut diags, &mut combined_tu, "prune", false);
    if cli.time_passes {
        eprintln!("  check (post-prune): {:.3}s", t.elapsed().as_secs_f64());
    }

    let t = Instant::now();
    pass::merge::merge(&mut diags, &mut combined_tu);
    if cli.time_passes {
        eprintln!(
            "  merge ({} decls): {:.3}s",
            combined_tu.decls.len(),
            t.elapsed().as_secs_f64()
        );
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
    pass::check::check(&mut diags, &mut combined_tu, "elab", true);
    if cli.time_passes {
        eprintln!("  check (post-elab): {:.3}s", t.elapsed().as_secs_f64());
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
