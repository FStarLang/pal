use std::{path::Path, rc::Rc, time::Instant};

use crate::{
    diag::{Diagnostic, Diagnostics},
    ir::{Location, Position, Range},
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
struct Cli {
    #[arg(long = "tmpdir")]
    tmpdir: Option<String>,

    #[arg(long = "outdir")]
    outdir: Option<String>,

    #[arg(long = "print-ir")]
    print_ir: bool,

    #[arg(long = "time-passes")]
    time_passes: bool,

    #[arg(short = 'I')]
    include_paths: Vec<String>,

    files: Vec<String>,
}

fn serialize_diags(for_file: &str, diags: &Diagnostics) -> String {
    let for_file = Rc::from(for_file);
    serde_json::to_string_pretty(
        &diags
            .diags
            .iter()
            .map(Diagnostic::clone)
            .map(|mut diag| {
                if diag.loc.file_name == for_file {
                    diag
                } else {
                    let pos0 = Position {
                        line: 0,
                        character: 0,
                    };
                    diag.loc = Location {
                        file_name: for_file.clone(),
                        range: Range {
                            start: pos0,
                            end: pos0,
                        },
                    };
                    diag
                }
            })
            .map(|diag| Diagnostic::to_lsp(&diag))
            .collect::<Vec<_>>(),
    )
    .unwrap()
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

    for module in &modules {
        let mut code = module.code.clone();
        if diags.has_errors() {
            code = format!("{}\n\nlet _ = assert False\n", code);
        }
        std::fs::write(outdir.join(format!("{}.fst", module.module_name)), &code).unwrap();
        std::fs::write(
            outdir.join(format!("{}_source_range_info.json", module.module_name)),
            source_range_info::serialize(&module.range_map),
        )
        .unwrap();
    }

    // Write diagnostics for the first file (for LSP compatibility)
    let first_file = std::path::absolute(&cli.files[0])
        .unwrap()
        .to_string_lossy()
        .into_owned();
    std::fs::write(
        outdir.join(format!(
            "{}_diagnostics.json",
            Path::new(&first_file)
                .file_stem()
                .unwrap()
                .to_string_lossy()
        )),
        &serialize_diags(&first_file, &diags),
    )
    .unwrap();

    diags.print_to_stderr(&mut *vfs);
    if diags.has_errors() {
        std::process::exit(0)
    }
}
