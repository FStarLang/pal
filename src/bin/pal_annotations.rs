use clap::{ArgGroup, Parser};
use std::path::PathBuf;

#[path = "../annotations/mod.rs"]
mod annotations;

#[derive(Parser)]
#[command(
    about = "Move PAL annotations between C sources and a reversible TOML overlay",
    group(ArgGroup::new("operation").required(true).args(["extract", "apply"]))
)]
struct Cli {
    #[arg(
        long,
        help = "Extract annotations from the supplied C and header files"
    )]
    extract: bool,

    #[arg(
        long,
        requires = "extract",
        help = "Keep declaration specifications inline"
    )]
    proofs_only: bool,

    #[arg(
        short = 'I',
        requires = "extract",
        help = "Root-relative include directory for supplied headers"
    )]
    include_dirs: Vec<PathBuf>,

    #[arg(long, value_name = "ANNOTATIONS", help = "Apply an annotation overlay")]
    apply: Option<PathBuf>,

    #[arg(
        short,
        long,
        requires = "extract",
        value_name = "ANNOTATIONS",
        help = "Extraction output (default: out.annotations)"
    )]
    output: Option<PathBuf>,

    #[arg(
        long,
        default_value = ".",
        help = "Root for source paths in the overlay"
    )]
    root: PathBuf,

    #[arg(
        long,
        requires = "apply",
        help = "Check applicability and source preservation without writing"
    )]
    check: bool,

    #[arg(
        requires = "extract",
        required_if_eq("extract", "true"),
        help = "C/header paths relative to --root"
    )]
    files: Vec<PathBuf>,
}

fn main() {
    let cli = Cli::parse();
    let result = if cli.extract {
        annotations::extract_files(
            &cli.root,
            &cli.files,
            &cli.output.unwrap_or_else(|| "out.annotations".into()),
            cli.proofs_only,
            &cli.include_dirs,
        )
    } else {
        annotations::apply_files(&cli.root, &cli.apply.unwrap(), cli.check)
    };
    match result {
        Ok(message) => println!("{message}"),
        Err(error) => {
            eprintln!("pal_annotations: {error}");
            std::process::exit(1);
        }
    }
}
