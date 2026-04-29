//! # Middle Pipeline
//!
//! The middle-end of the compiler is made up of several components. Ultimately,
//! its job is to take the parsed AST from the frontend, prove its correctness,
//! perform optimizations on it, and output LIR which can be used by the backend
//! for codegen. This happens through a series of steps which include name
//! resolution, AST lowering, type checking, early HIR optimization passes, HIR
//! lowering, mid-level pre-SSA LIR optimization passes, SSA LIR transformation,
//! SSA LIR optimization passes, Phi elimination, late post-SSA LIR optimization
//! passes.
//!
//! ## Name Resolution
//!
//! The first step in the pipeline after parsing is name resolution. In this
//! step, all top level definitions like functions and structures are assigned a
//! definition id which will identify them within the HIR. Additionally, imports
//! are resolved and all executable bodies are traversed to check that type
//! names and local variable usages are valid. All of these resolutions are
//! added to a map which is used in the next step.
//!
//! ## AST Lowering
//!
//! The next step is AST lowering. In this stage, the AST is indexed and
//! traversed to build up a comprehensive HIR (High-level Itermediate
//! Represenation). In this form, some syntactic sugar is removed, individual
//! pieces of syntax are abstracted away, and executable bodies are seperately
//! collected.
//!
//! ## Type Checking
//!
//! After building up an HIR, we need to check that it is semantically valid.
//! This is done through type checking the program. First, all item definitions
//! are analyzed to determine their types. Second, all executable bodies are
//! traversed to assign a type to each and every node in the HIR. We use a
//! Hindley-Milner style type inference algorithm to allow the types of many
//! expressions to be infered without explicit type hints.
//!
//! ## Early HIR Optimizations
//!
//! After type checking but before HIR lowering, there are several optimizations
//! we can do to simplify and normalize some source level constructs. This
//! includes constant folding, small function inlining, early DCE, algebraic
//! simplification, etc.
//!
//! ## HIR Lowering
//!
//! Once we have a simpler HIR to work with, we can lower the HIR tree structure
//! to flat LIR (Low-level intermediate represenation). This is the form in
//! which the bulk of our optimizations are performed. LIR constrol flow is very
//! explicit and much easier to reason about than the HIR. Lowering includes
//! traversing HIR, allocating registers to hold temporary values, linearizing
//! expression evaluation, and allocating new execution blocks at branch points.
//! The resulting LIR also encodes the body's CFG (Control Flow Graph) which is
//! useful for the remaining stages of the optimization pipeline. LIR
//! immediately after lowering is not yet in SSA form so reassignments are
//! allowed which is the main way that control flow for branching expressions is
//! implemented.
//!
//! ## Mid-level Pre-SSA Optimizations
//!
//! After lowering to a flat LIR, there are several optimizations which we can
//! do to clean up the CFG before transforming to SSA form. These include
//! additional constant folding and propagation (accounting for immutible
//! variable assignments), branch simplification, dead block elimination, jump
//! threading, block merging, etc.
//!
//! ## SSA LIR Transformation
//!
//! With our simplified CFG, the next step is to tranform the flat LIR which
//! contains reassignments into pure SSA form with Phi instructions for merging
//! control flow. This is similar to mem2reg from LLVM and is an important step
//! for further optimizations that are easier to apply if we can guarantee that
//! each register is only assigned once.
//!
//! ## SSA LIR Optimizations
//!
//! In SSA form we can easily perform additional optimizations such as SCCP
//! (sparse conditional constant propagation), SSA-aware DCE, CSE (common
//! subexpression elimination), GVN (global value numbering), copy propagation,
//! LICM (loop invariant code motion), etc.
//!
//! ## Phi Elimination
//!
//! Once all our SSA specific optimizations have been applied, we convert back
//! into a flat codegen-friendly LIR form. This involves replacing all Phi
//! instruction sources with registers shared between all dominating branches.
//!
//! ## Late Post-SSA Optimizations
//!
//! The last step before handing over our LIR to the backend for codegen is
//! performing some final more local optimizations. This includes various
//! general peephole optimizations, reggister allocation, instruction selection,
//! and late DCE.

pub mod hir;
pub mod lir;
pub mod optimization;
pub mod primitive;
pub mod resolve;
pub mod ty;
pub mod type_check;
