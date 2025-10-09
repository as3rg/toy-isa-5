use num_enum::TryFromPrimitive;

use crate::globals::{ExecError, ExecResult, Itarget, REGS_CNT, SYSCALL_ARGS_CNT, Utarget};

use crate::memory::Memory;

#[derive(Default, Debug)]
pub struct Reg {
    value: Utarget,
}

impl Reg {
    pub fn read(&self) -> ExecResult<Utarget> {
        Ok(self.value)
    }

    pub fn write(&mut self, value: Utarget) -> ExecResult {
        self.value = value;
        Ok(())
    }
}

#[derive(Default, Debug)]
pub struct CPUState {
    pub(crate) regs: [Reg; REGS_CNT as _],
    pub(crate) mem: Memory,
    pc_value: Utarget,
}

#[derive(Debug, TryFromPrimitive, PartialEq, Eq)]
#[repr(u32)]
pub enum SysCallCode {
    Exit = 60,
}

impl CPUState {
    pub fn reg(&mut self, idx: Utarget) -> ExecResult<&Reg> {
        Ok(&self.regs[idx as usize])
    }

    pub fn reg_mut(&mut self, idx: Utarget) -> ExecResult<&mut Reg> {
        Ok(&mut self.regs[idx as usize])
    }

    pub fn mem(&mut self) -> ExecResult<&Memory> {
        Ok(&self.mem)
    }

    pub fn mem_mut(&mut self) -> ExecResult<&mut Memory> {
        Ok(&mut self.mem)
    }

    pub fn jump_rel(&mut self, diff: Itarget) -> ExecResult<Utarget> {
        self.pc_value = self.pc_value.wrapping_add_signed(diff);
        Ok(self.pc_value)
    }

    pub fn jump_abs(&mut self, addr: Utarget) -> ExecResult<Utarget> {
        self.pc_value = addr;
        Ok(self.pc_value)
    }

    pub fn pc(&self) -> Utarget {
        self.pc_value
    }

    pub fn syscall(
        &mut self,
        code: SysCallCode,
        args: &[Utarget; SYSCALL_ARGS_CNT as _],
    ) -> ExecResult<Utarget> {
        match code {
            SysCallCode::Exit => Err(ExecError::Exit { exit_code: args[0] }),
        }
    }
}
