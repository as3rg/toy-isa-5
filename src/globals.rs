use std::{fmt, io};

pub type Utarget = u32;
pub type Itarget = i32;

pub const REGS_CNT: u32 = 32;
pub const WORD_SIZE: Utarget = size_of::<Utarget>() as _;
pub const CMD_SIZE: Utarget = WORD_SIZE;

pub type TargetBuf = [u8; WORD_SIZE as _];

pub const SYSCALL_ARGS_CNT: Utarget = 8;
pub const SYSCALL_CODE: Utarget = 8;
pub const SYSCALL_ARG0: Utarget = 0;
pub const SYSCALL_ARG1: Utarget = 1;
pub const SYSCALL_ARG2: Utarget = 2;
pub const SYSCALL_ARG3: Utarget = 3;
pub const SYSCALL_ARG4: Utarget = 4;
pub const SYSCALL_ARG5: Utarget = 5;
pub const SYSCALL_ARG6: Utarget = 6;
pub const SYSCALL_ARG7: Utarget = 7;
pub const SYSCALL_RET0: Utarget = 0;

#[derive(Debug)]
pub enum ExecError {
    InterpretationError { msg: String, addr: Utarget },
    JitExecutionError { msg: String },
    IOError(io::Error),
    Exit { exit_code: Utarget },
}

impl fmt::Display for ExecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExecError::InterpretationError { msg, addr } => {
                write!(f, "Interpretation error at address 0x{:x}: {}", addr, msg)
            }
            ExecError::JitExecutionError { msg } => {
                write!(f, "JIT execution error: {}", msg)
            }
            ExecError::IOError(err) => {
                write!(f, "I/O error: {}", err)
            }
            ExecError::Exit { exit_code } => {
                write!(f, "Process exited with code: {}", exit_code)
            }
        }
    }
}

pub type ExecResult<T = ()> = Result<T, ExecError>;
