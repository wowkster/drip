//! parsing of crate roots (core and bin) may happen in parallel
//!
//! as source files are parsed, additional mod directives can queue more
//! files to be parsed. all files get inserted into a module tree
//!
//! once all files are parsed, we start at the root of the dependency graph
//! (core) and run the definition collector on the entire crate, collecting
//! all of the definitions
//!
//! once all of the definitions are collected, we can for each module resolve
//! all of the imports from other modules in the same crate and combine them
//! with the definitions in just that module to create the global namespace
//! for the late resolver
//!
//! for each type definition in the module, resolve all of the field types
//! based on global namespace.
//!
//! for each body in the module, resolve all of the types, functions, local
//! variables, to DefIds
//!
//! once all modules are resolved, all of the ast lowering can happen in
//! parallel
//! 
//! once all of the modules are lowered to hir, the ast can be thrown out
//!
//! type checking needs some special care. all of the environment indexing
//! needs to run first (can happen in parallel), and then all of the type
//! checking, hir lowering, optimization, and codegen can then happen in
//! parallel

#![feature(decl_macro)]
#![feature(backtrace_frames)]

use std::{
    collections::VecDeque,
    os::unix::ffi::OsStrExt,
    path::{Path, PathBuf},
    rc::Rc,
};

use clap::{CommandFactory, Parser as ClapParser, error::ErrorKind};

use crate::{
    backend::{
        CodegenOptions, OutputKind, codegen_module, ssa_destruction::destruct_ssa, targets::Target,
    },
    frontend::{
        SourceFile, SourceFileOrigin,
        parser::{ParsingCtx, parse_crate},
    },
    middle::{
        hir::ast_lowering::lower_to_hir,
        lir::{hir_lowering::lower_to_lir, pretty_print::pretty_print_lir},
        optimization::pre_ssa::perform_pre_ssa_optimizations,
        resolve::Resolver,
        type_check::type_check_module,
    },
    session::Session,
};

mod backend;
mod frontend;
mod index;
mod middle;
mod session;

#[derive(Debug, ClapParser)]
#[command(version, about, long_about = None)]
pub struct Args {
    #[arg(short = 'e', value_enum)]
    emit: Option<EmitFormat>,
    #[arg(short = 'O', value_enum, default_value_t = Default::default())]
    optimization_level: OptimizationLevel,

    /// Specifies the path to the directory which holds the core library's
    /// source code.
    #[arg(short = 'c')]
    core_path: Option<PathBuf>,

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

    let mut session = Session::new();

    // parse modules and load in declared submodules as needed to build the
    // module tree

    let core_path = args
        .core_path
        .unwrap_or_else(|| PathBuf::from("./core/lib.drip"));

    let krate = parse_crate(&mut session, "core", core_path);

    // run name resolution over the entire crate

    let mut resolver = Resolver::new(&session, &krate.modules);

    // resolve all of the definitions (DefCollector) in each module and allocate
    // LocalDefIds for each one.

    for id in krate.modules.indices() {
        resolver.collect_definitions(id);
    }

    // for each module, resolve all of the imports and add them to the
    // definitions collected within that module to create a global value and
    // type scope and then resolve all of the bodies within that module using it

    for id in krate.modules.indices() {
        resolver.resolve_names(id);
    }

    // lower the AST to HIR using the output of name resoultion

    let resolution_map = resolver.into_outputs();

    let hir = lower_to_hir(&session, &krate, &resolution_map);

    /* Read in source files */

    // for source_file in &source_files {
    //     // Construct AST from the source code
    //     let ast = Parser::parse_module(source_file);

    //     if args.emit == Some(EmitFormat::Ast) {
    //         println!("{ast:#?}");
    //         return;
    //     }-

    //     // Index AST and resolve names to produce HIR
    //     let hir = lower_to_hir(&ast);

    //     if args.emit == Some(EmitFormat::Hir) {
    //         println!("{hir:#?}");
    //         return;
    //     }

    //     let types = type_check_module(&hir, source_file);
    //     let mut lir = lower_to_lir(&hir, &types);

    //     if args.optimization_level > OptimizationLevel::Zero {
    //         for function in lir.function_definitions.values_mut() {
    //             perform_pre_ssa_optimizations(function);
    //             // pretty_print_lir(&function);
    //         }
    //     }

    //     if args.emit == Some(EmitFormat::Lir) {
    //         for function in lir.function_definitions.values() {
    //             pretty_print_lir(function);
    //         }
    //         return;
    //     }

    //     for function in lir.function_definitions.values_mut() {
    //         destruct_ssa(function);
    //     }

    //     if args.emit == Some(EmitFormat::LirNoPhi) {
    //         for function in lir.function_definitions.values() {
    //             pretty_print_lir(function);
    //         }
    //         return;
    //     }

    //     // If an emit format is specified, we have to use that. Otherwise we
    //     // infer based on the output name
    //     let specified_output_kind = args.emit.map(|e| match e {
    //         EmitFormat::Assembly => OutputKind::Assembly,
    //         EmitFormat::Object => OutputKind::Object,
    //         _ => unreachable!(),
    //     });

    //     let cwd = std::env::current_dir().unwrap();

    //     let (output_directory, output_file) = match &args.output_path {
    //         Some(path) if path.is_dir() => (path.to_owned(), None),
    //         Some(path) => match path.parent() {
    //             Some(parent) => (
    //                 parent.to_path_buf(),
    //                 Some(PathBuf::from(path.file_name().unwrap())),
    //             ),
    //             None => (cwd, Some(PathBuf::from(path.file_name().unwrap()))),
    //         },
    //         None => (std::env::current_dir().unwrap(), None),
    //     };

    //     // If the output name is specified, use that. Otherwise compute the
    //     // correct name based on the input file.
    //     let (output_kind, output_file) = match output_file {
    //         Some(n) => {
    //             // if an output path is specified, and no explicit format is
    //             // given, infer based on the extension or default to an
    //             // executable

    //             let output_kind = specified_output_kind.unwrap_or_else(|| {
    //                 match n.extension().map(|e| e.as_bytes()) {
    //                     Some(b"s" | b"S" | b"asm" | b"nasm") => OutputKind::Assembly,
    //                     Some(b"o") => OutputKind::Object,
    //                     Some(b"a") => OutputKind::StaticLib,
    //                     Some(b"so") => OutputKind::SharedLib,
    //                     _ => OutputKind::Executable,
    //                 }
    //             });

    //             (output_kind, n.clone())
    //         }
    //         None => {
    //             let base_name = Path::new("a");
    //             let output_kind = specified_output_kind.unwrap_or(OutputKind::Executable);

    //             (
    //                 output_kind,
    //                 match output_kind {
    //                     OutputKind::Executable => base_name.with_extension("out"),
    //                     OutputKind::Object => base_name.with_extension("o"),
    //                     OutputKind::Assembly => base_name.with_extension("S"),
    //                     _ => unreachable!(),
    //                 },
    //             )
    //         }
    //     };

    //     if !output_directory.exists() {
    //         eprintln!(
    //             "output directory `{}` does not exist",
    //             output_directory.display()
    //         );
    //         std::process::exit(1);
    //     }

    //     codegen_module(
    //         &lir,
    //         &output_directory.join(output_file),
    //         &CodegenOptions {
    //             target: Some(Target::x86_64LinuxGnu),
    //             output_kind,
    //             emit_debug_info: true,
    //             verbose: true,
    //         },
    //     )
    //     .expect("codegen failed");
    // }
}
