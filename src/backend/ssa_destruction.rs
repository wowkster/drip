//! Transformation pass which removes phi nodes and replaces them with copies in
//! preceding basic blocks. Also breaks up critical edges in the CFG. After this
//! pass, the LIR is no longer in strict SSA form.

use std::collections::{BTreeMap, BTreeSet};

use crate::{index::Index, middle::lir};

pub fn destruct_ssa(function: &mut lir::FunctionDefinition) {
    // multistep process:
    //
    // 1. remove all critical edges in the CFG
    //
    // 2. insert copy instructions in preceding basic blocks (creating temporary
    // copies to avoid cycles)
    //
    // 3. remove all phi instructions in all blocks

    let highest_block_id = function
        .blocks
        .last_key_value()
        .map(|(id, _)| id)
        .copied()
        .expect("all bodies should have at least one basic block");

    let highest_register_id = function
        .registers
        .last_key_value()
        .map(|(id, _)| id)
        .copied()
        .unwrap_or(lir::RegisterId::new(0));

    // Step 1.1 Find all critical edges
    //
    // A edge is considered critical if it connects a block with multiple
    // successors to a block with multiple predecessors. Critically, a block can
    // only have multiple successors if it ends in a conditional branch
    // instruction (jumps or no branch fallthrough would always have a single
    // successor). For each branch instruction, we check the successor block to
    // check if it has multiple predecessors.

    let mut critical_edges = Vec::new();

    for (id, block) in &function.blocks {
        if let Some(lir::Instruction::Branch {
            positive, negative, ..
        }) = block.instructions.last()
        {
            if function.blocks[positive].predecessors.len() > 1 {
                critical_edges.push((*id, *positive));
            }

            if function.blocks[negative].predecessors.len() > 1 {
                critical_edges.push((*id, *negative));
            }
        }
    }

    // Step 1.2 Remove all critical edges
    //
    // We must create a new block, rewrite the predecessor block to branch to
    // the new block, update the successor's predecessor list, and update all
    // phi instructions in the successor block.

    let mut next_block_id = highest_block_id.plus(1);

    for (pred_id, succ_id) in critical_edges {
        let block_id = next_block_id;
        next_block_id = next_block_id.plus(1);

        let block = lir::Block {
            id: block_id,
            instructions: vec![lir::Instruction::Jump {
                destination: succ_id,
            }],
            predecessors: BTreeSet::from([pred_id]),
        };

        function.blocks.insert(block_id, block);

        let lir::Instruction::Branch {
            positive, negative, ..
        } = function
            .blocks
            .get_mut(&pred_id)
            .unwrap()
            .instructions
            .last_mut()
            .unwrap()
        else {
            unreachable!()
        };

        if *positive == succ_id {
            *positive = block_id;
        } else if *negative == succ_id {
            *negative = block_id;
        }

        let succ = function.blocks.get_mut(&succ_id).unwrap();

        succ.predecessors.remove(&pred_id);
        succ.predecessors.insert(block_id);

        for inst in &mut succ.instructions {
            if let lir::Instruction::Phi { sources, .. } = inst {
                let prev = sources.remove(&pred_id).unwrap();
                sources.insert(block_id, prev);
            }
        }
    }

    let mut next_register_id = highest_register_id.plus(1);

    for block_id in function.blocks.keys().copied().collect::<Vec<_>>() {
        // Step 2.1 Find the location of all of the phi instructions

        let mut phi_instructions: Vec<(lir::RegisterId, BTreeMap<lir::BlockId, lir::Operand>)> =
            Vec::new();

        for inst in &function.blocks[&block_id].instructions {
            if let lir::Instruction::Phi {
                destination,
                sources,
            } = inst
            {
                phi_instructions.push((*destination, sources.clone()));
            }
        }

        // Step 2.2 Insert copy instructions in preceding basic blocks (creating temporary
        // copies to avoid cycles)

        for (dest, sources) in phi_instructions {
            let mut temporary_copies: BTreeMap<lir::BlockId, lir::Operand> = BTreeMap::new();

            for (pred_id, value) in &sources {
                let pred = function.blocks.get_mut(&pred_id).unwrap();

                if let lir::Operand::Register(reg_id) = value {
                    let ty = function.registers[&reg_id].ty.clone();

                    let temp_reg_id = next_register_id;
                    next_register_id = next_register_id.plus(1);

                    let temp_reg = lir::Register {
                        id: temp_reg_id,
                        ty,
                    };

                    function.registers.insert(temp_reg_id, temp_reg);

                    let inst = lir::Instruction::Copy {
                        destination: temp_reg_id,
                        source: *value,
                    };

                    if pred.falls_through() {
                        pred.instructions.push(inst);
                    } else {
                        pred.instructions.insert(pred.instructions.len() - 1, inst);
                    }

                    temporary_copies.insert(*pred_id, lir::Operand::Register(temp_reg_id));
                } else {
                    temporary_copies.insert(*pred_id, *value);
                }
            }

            for (pred_id, _) in &sources {
                let pred = function.blocks.get_mut(&pred_id).unwrap();

                let value = temporary_copies.get(&pred_id).copied().unwrap();

                let inst = lir::Instruction::Copy {
                    destination: dest,
                    source: value,
                };

                if pred.falls_through() {
                    pred.instructions.push(inst);
                } else {
                    pred.instructions.insert(pred.instructions.len() - 1, inst);
                }
            }
        }
    }

    // Step 3. Remove all phi instructions in all blocks

    for block in function.blocks.values_mut() {
        block
            .instructions
            .retain(|inst| !matches!(inst, lir::Instruction::Phi { .. }));
    }
}
