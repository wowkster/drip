use hashbrown::{HashMap, HashSet};

use crate::{frontend::ast::BinaryOperatorKind, middle::lir};

// Performs some early LIR optimizations on the provided function like constant
// propagation, block merging, jump threading, and dead block elimination. This
// simplifies the LIR before we build the CFG and convert to SSA form and is
// mostly helpful to eliminate stupid output from lowering.
pub fn perform_pre_ssa_optimizations(function: &mut lir::FunctionDefinition) {
    truncate_after_returns(function);
    // propagate_constants(function);
    eliminate_dead_blocks(function);
    thread_jumps(function);
    merge_blocks(function);
    // propagate_constants(function);
    merge_blocks(function);

    // TODO: re-index all the register and block IDs to remove the gaps created
    // by optimization passes
}

/// Go through blocks which have a return statement, and delete anything
/// after that. Truncates to the index of the first return.
fn truncate_after_returns(function: &mut lir::FunctionDefinition) {
    for block in function.blocks.values_mut() {
        let Some(ret_index) = block
            .instructions
            .iter()
            .position(|i| matches!(i, lir::Instruction::Return { .. }))
        else {
            continue;
        };

        block.instructions.truncate(ret_index + 1);
    }
}

/// Jump threading. Eliminates blocks that are just a jump.
fn thread_jumps(function: &mut lir::FunctionDefinition) {
    for block_id in function.blocks.keys().copied().collect::<Vec<_>>() {
        /* Find the blocks we're looking for */

        if function.blocks[&block_id].instructions.len() != 1 {
            continue;
        }

        let lir::Instruction::Jump {
            destination: new_dest,
        } = *function.blocks[&block_id].instructions.first().unwrap()
        else {
            continue;
        };

        /* Update the CFG */

        let block = function.blocks.get_mut(&block_id).unwrap();
        let predecessors = block.predecessors.clone();

        // Patch any instructions in predecessor blocks that reference this
        // block as the jump target
        for predecessor in &predecessors {
            for instruction in &mut function.blocks.get_mut(predecessor).unwrap().instructions {
                match instruction {
                    lir::Instruction::Branch {
                        positive, negative, ..
                    } => {
                        assert!((*positive == block_id) ^ (*negative == block_id));
                        if *positive == block_id {
                            *positive = new_dest;
                        }
                        if *negative == block_id {
                            *negative = new_dest;
                        }
                    }
                    lir::Instruction::Jump { destination } => {
                        assert_eq!(*destination, block_id);
                        *destination = new_dest;
                    }
                    _ => {}
                }
            }
        }

        // Add all the old block's predeccessors to the new jump destination.
        // This is very important to make sure we preserve the CFG.
        function
            .blocks
            .get_mut(&new_dest)
            .unwrap()
            .predecessors
            .extend(predecessors);

        function.blocks.remove(&block_id);
        for block in function.blocks.values_mut() {
            block.predecessors.remove(&block_id);
        }
    }
}

// /// Analyzes the blocks to see which registers are both loaded with constants
// /// and also never re-assigned. After doing so, all uses of these registers in
// /// the rest of the LIR are replaced with the constant value. This is done
// /// repeatedly until there are no more non-propagated constants.
// fn propagate_constants(function: &mut lir::FunctionDefinition) {
//     let mut constant_map = HashMap::new();

//     // Find all the load immediate calls
//     for block in function.blocks.values() {
//         for instruction in &block.instructions {
//             let lir::Instruction::Move {
//                 destination,
//                 source: lir::Operand::Immediate(value),
//             } = instruction
//             else {
//                 continue;
//             };

//             constant_map.insert(*destination, *value);
//         }
//     }

//     // Remove any entries that are reassigned anywhere
//     let mut usage_map: HashMap<lir::RegisterId, usize> = HashMap::new();

//     for block in function.blocks.values() {
//         for instruction in &block.instructions {
//             match instruction {
//                 lir::Instruction::Move { destination, .. }
//                 | lir::Instruction::UnaryOperation { destination, .. }
//                 | lir::Instruction::BinaryOperation { destination, .. } => {
//                     *usage_map.entry(*destination).or_default() += 1;
//                 }
//                 _ => {}
//             }
//         }
//     }

//     for (reg, count) in usage_map {
//         if count > 1 {
//             constant_map.remove(&reg);
//         }
//     }

//     // If there are no more constant loads that are not reassigned, we're done
//     if constant_map.is_empty() {
//         return;
//     }

//     // Remove the constant registers
//     for block in function.blocks.values_mut() {
//         block.instructions.retain(|instruction| {
//             if let lir::Instruction::Move { destination, .. } = instruction {
//                 !constant_map.contains_key(destination)
//             } else {
//                 true
//             }
//         });
//     }

//     // Replace any usages of constant registers with their immediate values
//     for block in function.blocks.values_mut() {
//         for instruction in &mut block.instructions {
//             match instruction {
//                 lir::Instruction::Move { source, .. } => {
//                     if let lir::Operand::Register(s) = *source {
//                         constant_map
//                             .get(&s)
//                             .inspect(|imm| *source = lir::Operand::Immediate(**imm));
//                     }
//                 }
//                 lir::Instruction::UnaryOperation { operand, .. } => {
//                     if let lir::Operand::Register(s) = *operand {
//                         constant_map
//                             .get(&s)
//                             .inspect(|imm| *operand = lir::Operand::Immediate(**imm));
//                     }
//                 }
//                 lir::Instruction::BinaryOperation { lhs, rhs, .. } => {
//                     if let lir::Operand::Register(s) = *lhs {
//                         constant_map
//                             .get(&s)
//                             .inspect(|imm| *lhs = lir::Operand::Immediate(**imm));
//                     }

//                     if let lir::Operand::Register(s) = *rhs {
//                         constant_map
//                             .get(&s)
//                             .inspect(|imm| *rhs = lir::Operand::Immediate(**imm));
//                     }
//                 }
//                 lir::Instruction::Branch { condition, .. } => {
//                     if let lir::Operand::Register(s) = *condition {
//                         constant_map
//                             .get(&s)
//                             .inspect(|imm| *condition = lir::Operand::Immediate(**imm));
//                     }
//                 }
//                 lir::Instruction::Return { value: Some(value) } => {
//                     if let lir::Operand::Register(v) = *value {
//                         constant_map
//                             .get(&v)
//                             .inspect(|imm| *value = lir::Operand::Immediate(**imm));
//                     }
//                 }
//                 lir::Instruction::FunctionCall {
//                     target, arguments, ..
//                 } => {
//                     if let lir::Operand::Register(v) = *target {
//                         constant_map
//                             .get(&v)
//                             .inspect(|imm| *target = lir::Operand::Immediate(**imm));
//                     }

//                     for arg in arguments {
//                         if let lir::Operand::Register(v) = *arg {
//                             constant_map
//                                 .get(&v)
//                                 .inspect(|imm| *arg = lir::Operand::Immediate(**imm));
//                         }
//                     }
//                 }
//                 _ => {}
//             }
//         }
//     }

//     // Statically evaluate any arithmetic instructions which only contain
//     // constant values
//     for block in function.blocks.values_mut() {
//         for instruction in &mut block.instructions {
//             match instruction {
//                 lir::Instruction::UnaryOperation {
//                     operator,
//                     destination,
//                     operand,
//                 } => {
//                     let value = match (operand, operator) {
//                         (
//                             lir::Operand::Immediate(lir::Immediate::Int(value, width)),
//                             lir::UnaryOperatorKind::BitwiseNot,
//                         ) => lir::Immediate::Int(!*value, *width),
//                         (
//                             lir::Operand::Immediate(lir::Immediate::Int(..)),
//                             lir::UnaryOperatorKind::Negate,
//                         ) => todo!(),
//                         (
//                             lir::Operand::Immediate(lir::Immediate::Bool(value)),
//                             lir::UnaryOperatorKind::LogicalNot,
//                         ) => lir::Immediate::Bool(!*value),
//                         _ => continue,
//                     };

//                     let destination = *destination;
//                     let source = lir::Operand::Immediate(value);

//                     *instruction = lir::Instruction::Move {
//                         destination,
//                         source,
//                     }
//                 }
//                 lir::Instruction::BinaryOperation {
//                     destination,
//                     operator,
//                     lhs: lir::Operand::Immediate(lir::Immediate::Int(lhs, lhs_width)),
//                     rhs: lir::Operand::Immediate(lir::Immediate::Int(rhs, rhs_width)),
//                 } if lhs_width == rhs_width => {
//                     let value = match operator {
//                         BinaryOperatorKind::Add => {
//                             // overflows are handled because any smaller
//                             // integers will just be truncated automatically
//                             lir::Immediate::Int(lhs.wrapping_add(*rhs), *lhs_width)
//                         }
//                         BinaryOperatorKind::Subtract => {
//                             // overflows are handled because any smaller
//                             // integers will just be truncated automatically
//                             lir::Immediate::Int(lhs.wrapping_sub(*rhs), *lhs_width)
//                         }
//                         BinaryOperatorKind::Multiply => {
//                             // overflows are handled because any smaller
//                             // integers will just be truncated automatically
//                             lir::Immediate::Int(lhs.wrapping_mul(*rhs), *lhs_width)
//                         }
//                         BinaryOperatorKind::Equals => lir::Immediate::Bool(*lhs == *rhs),
//                         _ => continue,
//                     };

//                     let destination = *destination;
//                     let source = lir::Operand::Immediate(value);

//                     *instruction = lir::Instruction::Move {
//                         destination,
//                         source,
//                     }
//                 }
//                 _ => {}
//             }
//         }
//     }

//     propagate_constants(function);
// }

/// After constant propagation, there may be conditional branches which are
/// known statically at compile time to only go one way. This pass replaces
/// those branches with unconditional jumps and removes any blocks which no
/// longer have any predecessors as a result.
fn eliminate_dead_blocks(function: &mut lir::FunctionDefinition) {
    let block_ids = function.blocks.keys().copied().collect::<Vec<_>>();
    for block_id in &block_ids {
        if *block_id != lir::BlockId::ZERO
            && function
                .blocks
                .get_mut(block_id)
                .unwrap()
                .predecessors
                .is_empty()
        {
            function.blocks.remove(block_id);
            for block in function.blocks.values_mut() {
                block.predecessors.remove(block_id);
            }
            continue;
        }

        let mut removed_branch = None;

        // Try and replace a branch with a jump
        for instruction in &mut function.blocks.get_mut(block_id).unwrap().instructions {
            let lir::Instruction::Branch {
                condition: lir::Operand::Immediate(imm),
                positive,
                negative,
            } = instruction
            else {
                continue;
            };

            let lir::Immediate::Bool(condition) = imm else {
                unreachable!()
            };

            removed_branch = Some(if !*condition { *positive } else { *negative });
            *instruction = lir::Instruction::Jump {
                destination: if *condition { *positive } else { *negative },
            };
        }

        let Some(removed_branch) = removed_branch else {
            continue;
        };

        // println!("removing predecessor {} from {}", block_id, removed_branch);

        // ensure CFG correctness
        function
            .blocks
            .get_mut(&removed_branch)
            .unwrap()
            .predecessors
            .remove(block_id);
    }
}

/// Analyzes jumps to see if there are any blocks that "fall through" meaning
/// they just jump directly to the next block. In this case the jump is removed
/// and if the successor block has no other predecessors, the blocks are merged
/// into a single block to simplify the CFG.
fn merge_blocks(function: &mut lir::FunctionDefinition) {
    let mut evicted = HashSet::new();

    let block_ids = function.blocks.keys().copied().collect::<Vec<_>>();
    for (i, block_id) in block_ids.iter().copied().enumerate() {
        if i == block_ids.len() - 1 {
            break;
        }

        if evicted.contains(&block_id) {
            continue;
        }

        let lir::Instruction::Jump { destination } =
            function.blocks[&block_id].instructions.last().unwrap()
        else {
            continue;
        };

        let next_block = block_ids[i + 1];

        if *destination == next_block {
            function
                .blocks
                .get_mut(&block_id)
                .unwrap()
                .instructions
                .pop();

            // If the only predecessor is this block, we can safely merge
            if function.blocks[&next_block].predecessors.len() == 1 {
                let mut block = function.blocks.remove(&next_block).unwrap();
                evicted.insert(next_block);

                function
                    .blocks
                    .get_mut(&block_id)
                    .unwrap()
                    .instructions
                    .append(&mut block.instructions);
            }
        }
    }
}
