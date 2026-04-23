#![feature(decl_macro)]
#![feature(backtrace_frames)]

use std::{
    os::unix::ffi::OsStrExt,
    path::{Path, PathBuf},
};

use clap::{CommandFactory, Parser as ClapParser, error::ErrorKind};

use crate::{
    backend::{
        CodegenOptions, OutputKind, codegen_module, ssa_destruction::destruct_ssa, targets::Target,
    },
    frontend::{SourceFile, SourceFileOrigin, parser::Parser},
    middle::{
        hir::ast_lowering::lower_to_hir,
        lir::{hir_lowering::lower_to_lir, pretty_print::pretty_print_lir},
        optimization::pre_ssa::perform_pre_ssa_optimizations,
        type_check::type_check_module,
    },
};

mod backend;
mod frontend;
mod index;
mod middle;

#[derive(Debug, ClapParser)]
#[command(version, about, long_about = None)]
pub struct Args {
    #[arg(short = 'e', value_enum)]
    emit: Option<EmitFormat>,
    #[arg(short = 'O', value_enum, default_value_t = Default::default())]
    optimization_level: OptimizationLevel,

    #[arg(short = 'o')]
    output_path: Option<PathBuf>,
    source_files: Vec<PathBuf>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum EmitFormat {
    #[value(name = "obj")]
    Object,
    #[value(name = "asm")]
    Assembly,
    #[value(name = "lir_no_phi")]
    LirNoPhi,
    #[value(name = "lir")]
    Lir,
    #[value(name = "hir")]
    Hir,
    #[value(name = "ast")]
    Ast,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
pub enum OptimizationLevel {
    #[default]
    #[value(name = "0")]
    Zero,
    #[value(name = "1")]
    One,
    #[value(name = "2")]
    Two,
    #[value(name = "3")]
    Three,
}

fn main() {
    let args = Args::parse();

    if args.source_files.is_empty() {
        Args::command()
            .error(ErrorKind::MissingRequiredArgument, "Missing source files!")
            .exit();
    }

    for source_file in &args.source_files {
        if !source_file.exists() {
            Args::command()
                .error(
                    ErrorKind::InvalidValue,
                    format!("Source file '{}' does not exist!", source_file.display()),
                )
                .exit()
        }

        if !source_file.is_file() {
            Args::command()
                .error(
                    ErrorKind::InvalidValue,
                    format!("Input path '{}' is not a file!", source_file.display()),
                )
                .exit()
        }
    }

    /* Read in source files */

    let source_files = args
        .source_files
        .into_iter()
        .map(|path| {
            let contents = std::fs::read_to_string(&path)
                .expect("Failed to read input file (or invalid UTF-8)");

            SourceFile {
                contents,
                origin: SourceFileOrigin::File(path),
            }
        })
        .collect::<Vec<_>>();

    for source_file in &source_files {
        // Construct AST from the source code
        let ast = Parser::parse_module(source_file);

        if args.emit == Some(EmitFormat::Ast) {
            println!("{ast:#?}");
            return;
        }

        // Index AST and resolve names to produce HIR
        let hir = lower_to_hir(&ast);

        if args.emit == Some(EmitFormat::Hir) {
            println!("{hir:#?}");
            return;
        }

        let types = type_check_module(&hir, source_file);
        let mut lir = lower_to_lir(&hir, &types);

        if args.optimization_level > OptimizationLevel::Zero {
            for function in lir.function_definitions.values_mut() {
                perform_pre_ssa_optimizations(function);
                // pretty_print_lir(&function);
            }
        }

        if args.emit == Some(EmitFormat::Lir) {
            for function in lir.function_definitions.values() {
                pretty_print_lir(function);
            }
            return;
        }

        for function in lir.function_definitions.values_mut() {
            destruct_ssa(function);
        }

        if args.emit == Some(EmitFormat::LirNoPhi) {
            for function in lir.function_definitions.values() {
                pretty_print_lir(function);
            }
            return;
        }

        // If an emit format is specified, we have to use that. Otherwise we
        // infer based on the output name
        let specified_output_kind = args.emit.map(|e| match e {
            EmitFormat::Assembly => OutputKind::Assembly,
            EmitFormat::Object => OutputKind::Object,
            _ => unreachable!(),
        });

        let cwd = std::env::current_dir().unwrap();

        let (output_directory, output_file) = match &args.output_path {
            Some(path) if path.is_dir() => (path.to_owned(), None),
            Some(path) => match path.parent() {
                Some(parent) => (
                    parent.to_path_buf(),
                    Some(PathBuf::from(path.file_name().unwrap())),
                ),
                None => (cwd, Some(PathBuf::from(path.file_name().unwrap()))),
            },
            None => (std::env::current_dir().unwrap(), None),
        };

        // If the output name is specified, use that. Otherwise compute the
        // correct name based on the input file.
        let (output_kind, output_file) = match output_file {
            Some(n) => {
                // if an output path is specified, and no explicit format is
                // given, infer based on the extension or default to an
                // executable

                let output_kind = specified_output_kind.unwrap_or_else(|| {
                    match n.extension().map(|e| e.as_bytes()) {
                        Some(b"s" | b"S" | b"asm" | b"nasm") => OutputKind::Assembly,
                        Some(b"o") => OutputKind::Object,
                        Some(b"a") => OutputKind::StaticLib,
                        Some(b"so") => OutputKind::SharedLib,
                        _ => OutputKind::Executable,
                    }
                });

                (output_kind, n.clone())
            }
            None => {
                let base_name = Path::new("a");
                let output_kind = specified_output_kind.unwrap_or(OutputKind::Executable);

                (
                    output_kind,
                    match output_kind {
                        OutputKind::Executable => base_name.with_extension("out"),
                        OutputKind::Object => base_name.with_extension("o"),
                        OutputKind::Assembly => base_name.with_extension("S"),
                        _ => unreachable!(),
                    },
                )
            }
        };

        if !output_directory.exists() {
            eprintln!(
                "output directory `{}` does not exist",
                output_directory.display()
            );
            std::process::exit(1);
        }

        codegen_module(
            &lir,
            &output_directory.join(output_file),
            &CodegenOptions {
                target: Some(Target::x86_64LinuxGnu),
                output_kind,
                emit_debug_info: true,
                verbose: true,
            },
        )
        .expect("codegen failed");
    }
}
