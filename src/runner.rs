use std::{
    collections::HashMap,
    io::{Read, Seek, SeekFrom},
};

use crate::{
    cpu::CPUState,
    decoder::parse_instr,
    globals::{CMD_SIZE, ExecError, ExecResult, Utarget},
    jit::{BasicBlockBuilder, EmitStatus},
};

pub fn interpret<Cmds: Read + Seek>(
    cpu: &mut CPUState,
    cmds: &mut Cmds,
    entry_point: Utarget,
) -> ExecResult {
    cpu.jump_abs(entry_point)?;

    loop {
        // Seek
        cmds.seek(SeekFrom::Start(cpu.pc() as _))
            .map_err(ExecError::IOError)?;

        // Read command
        let mut buf = [0; CMD_SIZE as _];
        cmds.read_exact(&mut buf).map_err(ExecError::IOError)?;

        // Decode command
        let Some(cmd) = parse_instr(Utarget::from_le_bytes(buf)) else {
            return Err(ExecError::InterpretationError {
                msg: "Unknown instruction".into(),
                addr: cpu.pc(),
            });
        };

        // Execute command
        cpu.interpret(cmd)?;
    }
}

pub fn execute<Cmds: Read + Seek>(
    cpu: &mut CPUState,
    cmds: &mut Cmds,
    entry_point: Utarget,
) -> ExecResult {
    let mut bb_cache = HashMap::new();

    cpu.jump_abs(entry_point)?;

    loop {
        let pc = cpu.pc();

        // Check cache
        if let Some(bb) = bb_cache.get(&pc) {
            log::debug!("pc: 0x{:08x} | executing cached basic block", pc);
            let new_pc = cpu.execute(&bb)?;
            log::debug!("pc: 0x{:08x} | exiting cached basic block", new_pc);
            continue;
        }

        // Seek
        cmds.seek(SeekFrom::Start(pc as _))
            .map_err(ExecError::IOError)?;

        let mut bbb = BasicBlockBuilder::new(cpu)?;

        loop {
            // Read command
            let mut buf = [0; CMD_SIZE as _];
            cmds.read_exact(&mut buf).map_err(ExecError::IOError)?;

            // Decode command
            let Some(cmd) = parse_instr(Utarget::from_le_bytes(buf)) else {
                return Err(ExecError::JitExecutionError {
                    msg: "Unknown instruction".into(),
                });
            };

            // Generate Basic Block
            bbb = match bbb.emit(&cmd)? {
                EmitStatus::Accepted(bbb) => bbb,
                EmitStatus::Terminated(bb) => {
                    log::debug!("pc: 0x{:08x} | executing new basic block", pc);
                    let new_pc = cpu.execute(&bb)?;
                    log::debug!("pc: 0x{:08x} | exiting new basic block", new_pc);

                    bb_cache.insert(pc, bb);
                    break;
                }
            }
        }
    }
}
