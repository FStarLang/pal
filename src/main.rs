use std::{path::Path, time::Instant};

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

    #[arg(long = "outdir", help = "Output directory for generated .fst files")]
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

fn serialize_diags(diags: &Diagnostics) -> String {
    use std::collections::BTreeMap;

    // Group diagnostics by source file
    let mut by_file: BTreeMap<&str, Vec<lsp_types::Diagnostic>> = BTreeMap::new();
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
    pass::restructure_goto::restructure_goto(&mut combined_tu);
    if cli.time_passes {
        eprintln!("  restructure_goto: {:.3}s", t.elapsed().as_secs_f64());
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

    let outdir = match &cli.outdir {
        Some(outdir) => Path::new(outdir).to_path_buf(),
        None => match &cli.tmpdir {
            Some(tmpdir) => Path::new(tmpdir).to_path_buf(),
            None => {
                let first_file = std::path::absolute(&cli.files[0])
                    .unwrap()
                    .to_string_lossy()
                    .into_owned();
                Path::new(&first_file).parent().unwrap().to_path_buf()
            }
        },
    };
    std::fs::create_dir_all(&outdir).unwrap();

    for module in &modules {
        let mut code = module.code.clone();
        if diags.has_errors() {
            code = format!("{}\n\nlet _ = assert False\n", code);
        }
        std::fs::write(outdir.join(format!("{}.fst", module.module_name)), &code).unwrap();
        if let Some(fsti_code) = &module.fsti_code {
            std::fs::write(
                outdir.join(format!("{}.fsti", module.module_name)),
                fsti_code,
            )
            .unwrap();
        }
    }

    // Write single unified source_range_info.json
    std::fs::write(
        outdir.join("source_range_info.json"),
        source_range_info::serialize(&modules),
    )
    .unwrap();

    // Write diagnostics
    std::fs::write(outdir.join("diagnostics.json"), &serialize_diags(&diags)).unwrap();

    if !cli.quiet {
        diags.print_to_stderr(&mut *vfs);
    }
    if diags.has_errors() {
        std::process::exit(0)
    }
}
