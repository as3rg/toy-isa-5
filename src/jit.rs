use std::{fmt::Debug, marker::PhantomData, mem};

use dynasmrt::{
    Assembler, AssemblyOffset, DynasmApi, DynasmLabelApi, ExecutableBuffer, dynasm,
    relocations::Relocation, x64::X64Relocation,
};
use num_enum::TryFromPrimitive;

use crate::{
    cmds::*,
    cpu::{CPUState, Reg, SysCallCode},
    globals::{
        CMD_SIZE, ExecError, ExecResult, Itarget, Pc, PcOffset, REGS_CNT, SYSCALL_ARG0,
        SYSCALL_ARG1, SYSCALL_ARG2, SYSCALL_ARG3, SYSCALL_ARG4, SYSCALL_ARG5, SYSCALL_ARG6,
        SYSCALL_ARG7, SYSCALL_CODE, SYSCALL_RET0, Utarget, WORD_SIZE,
    },
    memory::Memory,
};

#[derive(Debug)]
pub struct BasicBlockBuilder<R: Relocation> {
    asm: Assembler<R>,
    start: AssemblyOffset,
    pc: Pc,
}

#[derive(Debug)]
pub struct BasicBlock<R: Relocation> {
    buf: ExecutableBuffer,
    start: AssemblyOffset,
    reloc: PhantomData<R>,
}

#[derive(Debug)]
pub enum EmitStatus<R: Relocation> {
    Accepted(BasicBlockBuilder<R>),
    Terminated(BasicBlock<R>),
}

pub trait Emit<R: Relocation> {
    fn emit(&self, bbb: BasicBlockBuilder<R>) -> ExecResult<EmitStatus<R>>;
}

macro_rules! my_disasm {
    ($asm:ident $($t:tt)*) => {
        dynasm!($asm
                ; .arch x64
                ; .alias a_regs, rdi
                ; .alias a_mem, rsi
                ; .alias a_result, rdx
                $($t)*
                );

    };
}

/// Load guest register to host
macro_rules! load {
    ($asm: ident, $host_reg: ident, $guest_reg: expr) => {
        my_disasm!($asm
                   ; mov $host_reg, [a_regs + ($guest_reg as usize * size_of::<Reg>()) as _]
                   )
    };
}

/// Store host register to guest register
macro_rules! store {
    ($asm: ident, $guest_reg: expr, $host_reg: ident) => {
        my_disasm!($asm
                   ; mov [a_regs + ($guest_reg as usize * size_of::<Reg>()) as _], $host_reg
                   )
    };
}

fn execution_error<T>(msg: String) -> ExecResult<T> {
    Err(ExecError::JitExecutionError { msg })
}

impl<R> BasicBlockBuilder<R>
where
    R: Relocation + Debug,
{
    pub fn new(cpu: &CPUState) -> ExecResult<Self> {
        match Assembler::new() {
            Ok(asm) => Ok({
                let start = asm.offset();
                BasicBlockBuilder {
                    asm,
                    start,
                    pc: cpu.pc(),
                }
            }),
            Err(e) => Err(ExecError::IOError(e)),
        }
    }

    pub fn emit<T: Emit<R>>(self, cmd: &T) -> ExecResult<EmitStatus<R>> {
        match cmd.emit(self) {
            Ok(EmitStatus::Accepted(mut bbb)) => {
                bbb.pc += PcOffset(CMD_SIZE as _);
                Ok(EmitStatus::Accepted(bbb))
            }
            x => x,
        }
    }

    pub fn finilize(self) -> ExecResult<BasicBlock<R>> {
        let mut asm = self.asm;
        my_disasm!(asm
        ; mov eax, (self.pc.0) as _
        ; ret
        );

        Ok(BasicBlock {
            buf: asm.finalize().unwrap(),
            start: self.start,
            reloc: PhantomData,
        })
    }
}

impl<R: Relocation> BasicBlock<R> {
    fn raw_func(&self) -> extern "sysv64" fn(*mut Reg, *mut Memory, *mut ExecResult) -> Utarget {
        unsafe { mem::transmute(self.buf.ptr(self.start)) }
    }

    pub fn executor(&self) -> impl Fn(&mut [Reg], &mut Memory) -> ExecResult<Pc> {
        |regs, mem| {
            let mut result = Ok(());
            let new_pc = self.raw_func()(regs.as_mut_ptr(), mem, &raw mut result);
            let () = result?;
            Ok(Pc(new_pc))
        }
    }
}

impl CPUState {
    pub fn execute(&mut self, bb: &BasicBlock<X64Relocation>) -> ExecResult<Pc> {
        let Self { regs, mem, .. } = self;
        let new_pc = bb.executor()(regs, mem)?;
        self.jump_abs(new_pc)
    }
}

impl Emit<X64Relocation> for Nor {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let asm = &mut bbb.asm;
        my_disasm!(asm
        ;; load!(asm, eax, self.get_rs())
        ;; load!(asm, ecx, self.get_rt())
        ;  or eax, ecx
        ;  not eax
        ;; store!(asm, self.get_rd(), eax)
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for Ldp {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        #[derive(Debug, Default)]
        #[repr(C)]
        struct Pair(Utarget, Utarget);

        fn load_helper_impl(mem: &mut Memory, addr: Utarget) -> ExecResult<(Utarget, Utarget)> {
            if (addr % WORD_SIZE) != 0 {
                return execution_error("Misaligned store".into());
            }

            let mut buf = [0; size_of::<Utarget>()];
            mem.read(addr, &mut buf)?;

            let mut buf2 = [0; size_of::<Utarget>()];
            mem.read(addr + size_of::<Utarget>() as Utarget, &mut buf2)?;

            Ok((Utarget::from_le_bytes(buf), Utarget::from_le_bytes(buf2)))
        }

        unsafe extern "sysv64" fn load_helper(
            _: *mut Reg,
            mem: *mut Memory,
            result: *mut ExecResult,
            addr: Utarget,
        ) -> Pair {
            unsafe {
                match load_helper_impl(mem.as_mut().unwrap(), addr) {
                    Ok((f, s)) => Pair(f, s),
                    Err(err) => {
                        *result = Err(err);
                        Pair::default()
                    }
                }
            }
        }

        let asm = &mut bbb.asm;
        my_disasm!(asm
        ;  push a_regs
        ;  push a_mem
        ;  push a_result

        ;; load!(asm, ecx, self.get_base())
        ;  add ecx, self.get_offset() as _
        ;  mov rax, QWORD load_helper as _
        ;  call rax

        ;  pop a_result
        ;  pop a_mem
        ;  pop a_regs
        ;; store!(asm, self.get_rt1(), eax)
        ;  shr rax, Utarget::BITS as _
        ;; store!(asm, self.get_rt2(), eax)
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for Cbit {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let asm = &mut bbb.asm;
        let mask: Utarget = !(1 << self.get_imm5());
        my_disasm!(asm
        ;; load!(asm, eax, self.get_rs())
        ;  and eax, mask as _
        ;; store!(asm, self.get_rd(), eax)
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for Bdep {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let asm = &mut bbb.asm;
        my_disasm!(asm
        ;; load!(asm, r8d, self.get_rs1())
        ;; load!(asm, r9d, self.get_rs2())

        ;  xor eax, eax         // result
        ;  test r9d, r9d
        ;  jz ->finish

        ;  ->iter:
        ;  blsi r10d, r9d       // lowest bit mask
        ;  sub  r9d, r10d

        ;  mov r11d, r8d        // value lower bit
        ;  and r11d, 1
        ;  neg r11d
        ;  shr r8d, 1

        ;  and r10d, r11d
        ;  or eax, r10d

        ;  test r9d, r9d
        ;  jnz ->iter

        ;  ->finish:
        ;; store!(asm, self.get_rd(), eax)
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for Add {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let asm = &mut bbb.asm;
        my_disasm!(asm
        ;; load!(asm, eax, self.get_rs())
        ;; load!(asm, ecx, self.get_rt())
        ;  add eax, ecx
        ;; store!(asm, self.get_rd(), eax)
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for Ssat {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let asm = &mut bbb.asm;
        let bits = self.get_imm5();
        let min_bound = Itarget::min_value().unbounded_shr(Itarget::BITS - bits);
        let max_bound = Itarget::max_value().unbounded_shr(Itarget::BITS - bits);

        my_disasm!(asm
        ;; load!(asm, eax, self.get_rs())
        ;  mov ecx, min_bound as _
        ;  cmp eax, ecx
        ;  cmovl eax, ecx
        ;  mov ecx, max_bound as _
        ;  cmp eax, ecx
        ;  cmovg eax, ecx
        ;; store!(asm, self.get_rd(), eax)
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for St {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        fn store_helper_impl(mem: &mut Memory, addr: Utarget, value: Utarget) -> ExecResult {
            if (addr % WORD_SIZE) != 0 {
                return execution_error("Misaligned store".into());
            }

            let buf = value.to_le_bytes();
            mem.write(addr, &buf)
        }

        unsafe extern "sysv64" fn store_helper(
            _: *mut Reg,
            mem: *mut Memory,
            result: *mut ExecResult,
            addr: Utarget,
            value: Utarget,
        ) {
            unsafe {
                match store_helper_impl(mem.as_mut().unwrap(), addr, value) {
                    Ok(v) => v,
                    Err(err) => {
                        *result = Err(err);
                    }
                }
            }
        }

        let asm = &mut bbb.asm;
        my_disasm!(asm
        ;  push a_regs
        ;  push a_mem
        ;  push a_result

        ;; load!(asm, ecx, self.get_base())
        ;  add ecx, self.get_offset() as _
        ;; load!(asm, r8d, self.get_rt())
        ;  mov rax, QWORD store_helper as _
        ;  call rax

        ;  pop a_result
        ;  pop a_mem
        ;  pop a_regs
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for Clz {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let asm = &mut bbb.asm;
        my_disasm!(asm
        ;; load!(asm, eax, self.get_rs())
        ;  lzcnt eax, eax
        ;; store!(asm, self.get_rd(), eax)
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for Bne {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let asm = &mut bbb.asm;
        let new_pc = bbb.pc + PcOffset(self.get_offset() * CMD_SIZE.cast_signed());
        my_disasm!(asm
        ;; load!(asm, ecx, self.get_rs())
        ;; load!(asm, r8d, self.get_rt())
        ;  cmp ecx, r8d
        ;  je ->bfalse
        ;  mov eax, new_pc.0 as _
        ;  ret
        ;  ->bfalse:
        );

        bbb.pc += PcOffset(CMD_SIZE as _);
        bbb.finilize().map(EmitStatus::Terminated)
    }
}

impl Emit<X64Relocation> for Ld {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        fn load_helper_impl(mem: &mut Memory, addr: Utarget) -> ExecResult<Utarget> {
            if (addr % WORD_SIZE) != 0 {
                return execution_error("Misaligned store".into());
            }

            let mut buf = [0; size_of::<Utarget>()];
            mem.read(addr, &mut buf)?;

            Ok(Utarget::from_le_bytes(buf))
        }

        unsafe extern "sysv64" fn load_helper(
            _: *mut Reg,
            mem: *mut Memory,
            result: *mut ExecResult,
            addr: Utarget,
        ) -> Utarget {
            unsafe {
                match load_helper_impl(mem.as_mut().unwrap(), addr) {
                    Ok(v) => v,
                    Err(err) => {
                        *result = Err(err);
                        Utarget::default()
                    }
                }
            }
        }

        let asm = &mut bbb.asm;
        my_disasm!(asm
        ;  push a_regs
        ;  push a_mem
        ;  push a_result

        ;; load!(asm, ecx, self.get_base())
        ;  add ecx, self.get_offset() as _
        ;  mov rax, QWORD load_helper as _
        ;  call rax

        ;  pop a_result
        ;  pop a_mem
        ;  pop a_regs
        ;; store!(asm, self.get_rt(), eax)
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for Xor {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let asm = &mut bbb.asm;
        my_disasm!(asm
        ;; load!(asm, eax, self.get_rs())
        ;; load!(asm, ecx, self.get_rt())
        ;  xor eax, ecx
        ;; store!(asm, self.get_rd(), eax)
        );

        Ok(EmitStatus::Accepted(bbb))
    }
}

impl Emit<X64Relocation> for Syscall {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        fn syscall_helper_impl(regs: &mut [Reg], _: &mut Memory) -> ExecResult<Utarget> {
            let code_num = regs[SYSCALL_CODE as usize].read()?;
            let Ok(code) = SysCallCode::try_from_primitive(code_num) else {
                return execution_error(format!("Unknown syscall with code 0x{:x}", code_num));
            };
            let args = [
                regs[SYSCALL_ARG0 as usize].read()?,
                regs[SYSCALL_ARG1 as usize].read()?,
                regs[SYSCALL_ARG2 as usize].read()?,
                regs[SYSCALL_ARG3 as usize].read()?,
                regs[SYSCALL_ARG4 as usize].read()?,
                regs[SYSCALL_ARG5 as usize].read()?,
                regs[SYSCALL_ARG6 as usize].read()?,
                regs[SYSCALL_ARG7 as usize].read()?,
            ];

            let res = code.call(&args)?;
            regs[SYSCALL_RET0 as usize].write(res)?;

            Ok(res)
        }

        unsafe extern "sysv64" fn syscall_helper(
            regs: *mut Reg,
            mem: *mut Memory,
            result: *mut ExecResult,
        ) -> Utarget {
            unsafe {
                match syscall_helper_impl(
                    std::slice::from_raw_parts_mut(regs, REGS_CNT as _),
                    mem.as_mut().unwrap(),
                ) {
                    Ok(v) => v,
                    Err(err) => {
                        *result = Err(err);
                        Utarget::default()
                    }
                }
            }
        }

        let asm = &mut bbb.asm;
        my_disasm!(asm
        ;  mov rax, QWORD syscall_helper as _
        ;  jmp rax
        );

        bbb.finilize().map(EmitStatus::Terminated)
    }
}

impl Emit<X64Relocation> for Beq {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let asm = &mut bbb.asm;
        let new_pc = bbb.pc + PcOffset(self.get_offset() * CMD_SIZE.cast_signed());
        my_disasm!(asm
        ;; load!(asm, ecx, self.get_rs())
        ;; load!(asm, r8d, self.get_rt())
        ;  cmp ecx, r8d
        ;  jne ->bfalse
        ;  mov eax, new_pc.0 as _
        ;  ret
        ;  ->bfalse:
        );

        bbb.pc += PcOffset(CMD_SIZE as _);
        bbb.finilize().map(EmitStatus::Terminated)
    }
}

impl Emit<X64Relocation> for J {
    fn emit(
        &self,
        mut bbb: BasicBlockBuilder<X64Relocation>,
    ) -> ExecResult<EmitStatus<X64Relocation>> {
        let pc = bbb.pc;
        let mask = 0b00001111111111111111111111111111;
        let new_addr = Pc(pc.0 & !mask | (self.get_index() * CMD_SIZE) & mask);

        bbb.pc = new_addr;
        bbb.finilize().map(EmitStatus::Terminated)
    }
}

impl Emit<X64Relocation> for Instr {
    fn emit(&self, bbb: BasicBlockBuilder<X64Relocation>) -> ExecResult<EmitStatus<X64Relocation>> {
        match self {
            Instr::Nor(cmd) => cmd.emit(bbb),
            Instr::Ldp(cmd) => cmd.emit(bbb),
            Instr::Cbit(cmd) => cmd.emit(bbb),
            Instr::Bdep(cmd) => cmd.emit(bbb),
            Instr::Add(cmd) => cmd.emit(bbb),
            Instr::Ssat(cmd) => cmd.emit(bbb),
            Instr::St(cmd) => cmd.emit(bbb),
            Instr::Clz(cmd) => cmd.emit(bbb),
            Instr::Bne(cmd) => cmd.emit(bbb),
            Instr::Ld(cmd) => cmd.emit(bbb),
            Instr::Xor(cmd) => cmd.emit(bbb),
            Instr::Syscall(cmd) => cmd.emit(bbb),
            Instr::Beq(cmd) => cmd.emit(bbb),
            Instr::J(cmd) => cmd.emit(bbb),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        globals::Itarget,
        helpers::{bit_deposit, saturate_signed},
    };

    use super::*;

    fn execute_accepted<T: Emit<X64Relocation>>(cpu: &mut CPUState, cmd: &T) {
        let bbb = BasicBlockBuilder::new(cpu).unwrap();

        if let EmitStatus::Accepted(bbb) = bbb.emit(cmd).unwrap() {
            let bb = bbb.finilize().unwrap();
            let pc = cpu.pc();
            assert_eq!(cpu.execute(&bb).unwrap(), pc + PcOffset(4));
            assert_eq!(cpu.pc(), pc + PcOffset(4));
        } else {
            panic!("Accepted status expected");
        }
    }

    fn execute_accepted_fail<T: Emit<X64Relocation>>(cpu: &mut CPUState, cmd: &T) {
        let bbb = BasicBlockBuilder::new(cpu).unwrap();
        if let EmitStatus::Accepted(bbb) = bbb.emit(cmd).unwrap() {
            let bb = bbb.finilize().unwrap();
            assert!(cpu.execute(&bb).is_err());
        } else {
            panic!("Accepted status expected");
        }
    }

    fn execute_terminated<T: Emit<X64Relocation>>(cpu: &mut CPUState, cmd: &T, new_pc: Pc) {
        let bbb = BasicBlockBuilder::new(cpu).unwrap();
        if let EmitStatus::Terminated(bb) = bbb.emit(cmd).unwrap() {
            assert_eq!(cpu.execute(&bb).unwrap(), new_pc);
            assert_eq!(cpu.pc(), new_pc);
        } else {
            panic!("Terminated status expected");
        }
    }

    fn execute_terminated_fail<T: Emit<X64Relocation>>(cpu: &mut CPUState, cmd: &T) {
        let bbb = BasicBlockBuilder::new(cpu).unwrap();
        if let EmitStatus::Terminated(bb) = bbb.emit(cmd).unwrap() {
            assert!(cpu.execute(&bb).is_err());
        } else {
            panic!("Terminated status expected");
        }
    }

    fn create_cpu() -> CPUState {
        CPUState::default()
    }

    #[test]
    fn test_nor_instruction() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RD_IDX: Utarget = 3;
        const RS_VALUE: Utarget = 0xFFFF0000;
        const RT_VALUE: Utarget = 0x0000FFFF;
        const EXPECTED_RESULT: Utarget = 0x00000000;

        let mut cpu = create_cpu();

        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let nor = Nor::from_fields(RD_IDX, RT_IDX, RS_IDX);
        execute_accepted(&mut cpu, &nor);

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_ldp_instruction() {
        const BASE_IDX: Utarget = 1;
        const RT1_IDX: Utarget = 2;
        const RT2_IDX: Utarget = 3;
        const BASE_ADDR: Utarget = 0x1000;
        const VALUE1: Utarget = 0x12345678;
        const VALUE2: Utarget = 0x9ABCDEF0;
        const OFFSET: Itarget = -16;

        let mut cpu = create_cpu();

        cpu.mem_mut()
            .unwrap()
            .write(BASE_ADDR.wrapping_add_signed(OFFSET), &VALUE1.to_le_bytes())
            .unwrap();
        cpu.mem_mut()
            .unwrap()
            .write(
                BASE_ADDR.wrapping_add_signed(OFFSET).wrapping_add(4),
                &VALUE2.to_le_bytes(),
            )
            .unwrap();
        cpu.reg_mut(BASE_IDX).unwrap().write(BASE_ADDR).unwrap();

        let ldp = Ldp::from_fields(OFFSET, RT2_IDX, RT1_IDX, BASE_IDX);
        execute_accepted(&mut cpu, &ldp);

        let value1 = cpu.reg(RT1_IDX).unwrap().read().unwrap();
        let value2 = cpu.reg(RT2_IDX).unwrap().read().unwrap();

        assert_eq!(value1, VALUE1);
        assert_eq!(value2, VALUE2);
    }

    #[test]
    fn test_ldp_misaligned() {
        const BASE_IDX: Utarget = 1;
        const RT1_IDX: Utarget = 2;
        const RT2_IDX: Utarget = 3;
        const MISALIGNED_ADDR: Utarget = 0x1001;
        const OFFSET: Itarget = 0;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX)
            .unwrap()
            .write(MISALIGNED_ADDR)
            .unwrap();

        let ldp = Ldp::from_fields(OFFSET, RT2_IDX, RT1_IDX, BASE_IDX);
        execute_accepted_fail(&mut cpu, &ldp);
    }

    #[test]
    fn test_ldp_misaligned_2() {
        const BASE_IDX: Utarget = 1;
        const RT1_IDX: Utarget = 2;
        const RT2_IDX: Utarget = 3;
        const MISALIGNED_ADDR: Utarget = 0x1000;
        const OFFSET: Itarget = 3;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX)
            .unwrap()
            .write(MISALIGNED_ADDR)
            .unwrap();

        let ldp = Ldp::from_fields(OFFSET, RT2_IDX, RT1_IDX, BASE_IDX);
        execute_accepted_fail(&mut cpu, &ldp);
    }

    #[test]
    fn test_ldp_not_misaligned() {
        const BASE_IDX: Utarget = 1;
        const RT1_IDX: Utarget = 2;
        const RT2_IDX: Utarget = 3;
        const MISALIGNED_ADDR: Utarget = 0x1003;
        const OFFSET: Itarget = 1;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX)
            .unwrap()
            .write(MISALIGNED_ADDR)
            .unwrap();

        let ldp = Ldp::from_fields(OFFSET, RT2_IDX, RT1_IDX, BASE_IDX);
        execute_accepted(&mut cpu, &ldp);
    }

    #[test]
    fn test_cbit_instruction() {
        const RS_IDX: Utarget = 1;
        const RD_IDX: Utarget = 2;
        const BIT_TO_CLEAR: Utarget = 1;
        const RS_VALUE: Utarget = 0b1010;
        const EXPECTED_RESULT: Utarget = 0b1000;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();

        let cbit = Cbit::from_fields(BIT_TO_CLEAR, RS_IDX, RD_IDX);
        execute_accepted(&mut cpu, &cbit);

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_cbit_instruction_2() {
        const RS_IDX: Utarget = 1;
        const RD_IDX: Utarget = 2;
        const BIT_TO_CLEAR: Utarget = 2;
        const RS_VALUE: Utarget = 0b1010;
        const EXPECTED_RESULT: Utarget = 0b1010;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();

        let cbit = Cbit::from_fields(BIT_TO_CLEAR, RS_IDX, RD_IDX);
        execute_accepted(&mut cpu, &cbit);

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_bdep_instruction() {
        const RS1_IDX: Utarget = 1;
        const RS2_IDX: Utarget = 2;
        const RD_IDX: Utarget = 3;
        let params: &[(Utarget, Utarget)] = &[
            (239, 0),
            (0, 239),
            (0xffffffff, 0),
            (0, 0xffffffff),
            (0b101010, 0b010101),
            (0b101, 0b1001001),
            (0x239, 0xffffffff),
            (0x239, 0x00ff00ff),
        ];
        let mut cpu = create_cpu();
        for (value, mask) in params.into_iter().copied() {
            cpu.reg_mut(RS1_IDX).unwrap().write(value).unwrap();
            cpu.reg_mut(RS2_IDX).unwrap().write(mask).unwrap();

            let bdep = Bdep::from_fields(RS2_IDX, RS1_IDX, RD_IDX);
            execute_accepted(&mut cpu, &bdep);

            let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
            assert_eq!(result, bit_deposit(value, mask));
        }
    }

    #[test]
    fn test_add_instruction() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RD_IDX: Utarget = 3;
        const RS_VALUE: Utarget = 10;
        const RT_VALUE: Utarget = 20;
        const EXPECTED_RESULT: Utarget = 30;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let add = Add::from_fields(RD_IDX, RT_IDX, RS_IDX);

        execute_accepted(&mut cpu, &add);

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_add_overflow() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RD_IDX: Utarget = 3;
        const RS_VALUE: Utarget = u32::MAX;
        const RT_VALUE: Utarget = 1;
        const EXPECTED_RESULT: Utarget = 0;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let add = Add::from_fields(RD_IDX, RT_IDX, RS_IDX);

        execute_accepted(&mut cpu, &add);

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_ssat_instruction() {
        let params: &[(Itarget, Utarget)] = &[
            (Itarget::MIN, 31),
            (Itarget::MAX, 31),
            (Itarget::MIN, 16),
            (Itarget::MAX, 16),
            (Itarget::MIN, 2),
            (Itarget::MAX, 2),
            (Itarget::MIN, 1),
            (Itarget::MAX, 1),
            (Itarget::MIN, 0),
            (Itarget::MAX, 0),
        ];

        let mut cpu = create_cpu();
        for (val, bits) in params.iter().copied() {
            const RS_IDX: Utarget = 1;
            const RD_IDX: Utarget = 2;

            cpu.reg_mut(RS_IDX)
                .unwrap()
                .write(val.cast_unsigned())
                .unwrap();

            let ssat = Ssat::from_fields(bits, RS_IDX, RD_IDX);
            execute_accepted(&mut cpu, &ssat);

            let result = cpu.reg(RD_IDX).unwrap().read().unwrap().cast_signed();
            assert_eq!(result, saturate_signed(val, bits));
        }
    }

    #[test]
    fn test_st_instruction() {
        const BASE_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const BASE_ADDR: Utarget = 0x1000;
        const STORE_VALUE: Utarget = 0xDEADBEEF;
        const OFFSET: Itarget = -16;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX).unwrap().write(BASE_ADDR).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(STORE_VALUE).unwrap();

        let st = St::from_fields(OFFSET, RT_IDX, BASE_IDX);
        execute_accepted(&mut cpu, &st);

        let mut buffer = [0u8; 4];
        cpu.mem()
            .unwrap()
            .read(BASE_ADDR.wrapping_add_signed(OFFSET), &mut buffer)
            .unwrap();
        let stored_value = u32::from_le_bytes(buffer);

        assert_eq!(stored_value, STORE_VALUE);
    }

    #[test]
    fn test_st_misaligned() {
        const BASE_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const MISALIGNED_ADDR: Utarget = 0x1001;
        const OFFSET: Itarget = 0;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX)
            .unwrap()
            .write(MISALIGNED_ADDR)
            .unwrap();

        let st = St::from_fields(OFFSET, RT_IDX, BASE_IDX);
        execute_accepted_fail(&mut cpu, &st);
    }

    #[test]
    fn test_st_misaligned_2() {
        const BASE_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const MISALIGNED_ADDR: Utarget = 0x1000;
        const OFFSET: Itarget = 3;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX)
            .unwrap()
            .write(MISALIGNED_ADDR)
            .unwrap();

        let st = St::from_fields(OFFSET, RT_IDX, BASE_IDX);
        execute_accepted_fail(&mut cpu, &st);
    }

    #[test]
    fn test_st_not_misaligned() {
        const BASE_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const MISALIGNED_ADDR: Utarget = 0x1001;
        const OFFSET: Itarget = 3;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX)
            .unwrap()
            .write(MISALIGNED_ADDR)
            .unwrap();

        let st = St::from_fields(OFFSET, RT_IDX, BASE_IDX);
        execute_accepted(&mut cpu, &st);
    }

    #[test]
    fn test_clz_instruction() {
        const RS_IDX: Utarget = 1;
        const RD_IDX: Utarget = 2;
        const RS_VALUE: Utarget = 0x00000001;
        const EXPECTED_RESULT: Utarget = 31;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();

        let clz = Clz::from_fields(RS_IDX, RD_IDX);
        execute_accepted(&mut cpu, &clz);

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_clz_all_zeros() {
        const RS_IDX: Utarget = 1;
        const RD_IDX: Utarget = 2;
        const RS_VALUE: Utarget = 0x00000000;
        const EXPECTED_RESULT: Utarget = 32;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();

        let clz = Clz::from_fields(RS_IDX, RD_IDX);
        execute_accepted(&mut cpu, &clz);

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_clz_all_ones() {
        const RS_IDX: Utarget = 1;
        const RD_IDX: Utarget = 2;
        const RS_VALUE: Utarget = 0xffffffff;
        const EXPECTED_RESULT: Utarget = 0;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();

        let clz = Clz::from_fields(RS_IDX, RD_IDX);
        execute_accepted(&mut cpu, &clz);

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_bne_instruction_taken() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RS_VALUE: Utarget = 10;
        const RT_VALUE: Utarget = 20;
        const OFFSET: Itarget = 4;

        let mut cpu = create_cpu();
        let initial_pc = cpu.pc();
        let next_pc = initial_pc + PcOffset(OFFSET << 2);
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let bne = Bne::from_fields(OFFSET, RT_IDX, RS_IDX);
        execute_terminated(&mut cpu, &bne, next_pc);
    }

    #[test]
    fn test_bne_instruction_not_taken() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RS_VALUE: Utarget = 10;
        const RT_VALUE: Utarget = 10;
        const OFFSET: Itarget = 4;

        let mut cpu = create_cpu();
        let next_pc = Pc(4);
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let bne = Bne::from_fields(OFFSET, RT_IDX, RS_IDX);
        execute_terminated(&mut cpu, &bne, next_pc);
    }

    #[test]
    fn test_bne_instruction_self_jump() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RS_VALUE: Utarget = 10;
        const RT_VALUE: Utarget = 20;
        const OFFSET: Itarget = 0;

        let mut cpu = create_cpu();
        let initial_pc = cpu.pc();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let bne = Bne::from_fields(OFFSET, RT_IDX, RS_IDX);
        execute_terminated(&mut cpu, &bne, initial_pc);
    }

    #[test]
    fn test_ld_instruction() {
        const BASE_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const BASE_ADDR: Utarget = 0x1000;
        const MEM_VALUE: Utarget = 0x12345678;
        const OFFSET: Itarget = -16;

        let mut cpu = create_cpu();
        cpu.mem_mut()
            .unwrap()
            .write(
                BASE_ADDR.wrapping_add_signed(OFFSET),
                &MEM_VALUE.to_le_bytes(),
            )
            .unwrap();
        cpu.reg_mut(BASE_IDX).unwrap().write(BASE_ADDR).unwrap();

        let ld = Ld::from_fields(OFFSET, RT_IDX, BASE_IDX);
        execute_accepted(&mut cpu, &ld);

        let result = cpu.reg(RT_IDX).unwrap().read().unwrap();
        assert_eq!(result, MEM_VALUE);
    }

    #[test]
    fn test_ld_misaligned() {
        const BASE_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const BASE_ADDR: Utarget = 0x1003;
        const OFFSET: Itarget = 0;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX).unwrap().write(BASE_ADDR).unwrap();

        let ld = Ld::from_fields(OFFSET, RT_IDX, BASE_IDX);
        execute_accepted_fail(&mut cpu, &ld);
    }

    #[test]
    fn test_ld_misaligned_2() {
        const BASE_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const BASE_ADDR: Utarget = 0x1000;
        const OFFSET: Itarget = 1;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX).unwrap().write(BASE_ADDR).unwrap();

        let ld = Ld::from_fields(OFFSET, RT_IDX, BASE_IDX);
        execute_accepted_fail(&mut cpu, &ld);
    }

    #[test]
    fn test_ld_not_misaligned() {
        const BASE_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const BASE_ADDR: Utarget = 0x1003;
        const OFFSET: Itarget = 1;

        let mut cpu = create_cpu();
        cpu.reg_mut(BASE_IDX).unwrap().write(BASE_ADDR).unwrap();

        let ld = Ld::from_fields(OFFSET, RT_IDX, BASE_IDX);
        execute_accepted(&mut cpu, &ld);
    }

    #[test]
    fn test_xor_instruction() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RD_IDX: Utarget = 3;
        const RS_VALUE: Utarget = 0b1100;
        const RT_VALUE: Utarget = 0b1010;
        const EXPECTED_RESULT: Utarget = 0b0110;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let xor = Xor::from_fields(RD_IDX, RT_IDX, RS_IDX);
        execute_accepted(&mut cpu, &xor);

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_syscall_instruction() {
        let mut cpu = create_cpu();
        let syscall = Syscall::from_fields(0);
        execute_terminated_fail(&mut cpu, &syscall);
    }

    #[test]
    fn test_beq_instruction_taken() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RS_VALUE: Utarget = 10;
        const RT_VALUE: Utarget = 10;
        const OFFSET: Itarget = 4;

        let mut cpu = create_cpu();
        let initial_pc = cpu.pc();
        let next_pc = initial_pc + PcOffset(OFFSET << 2);
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let beq = Beq::from_fields(OFFSET, RT_IDX, RS_IDX);
        execute_terminated(&mut cpu, &beq, next_pc);
    }

    #[test]
    fn test_beq_instruction_self_jump() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RS_VALUE: Utarget = 10;
        const RT_VALUE: Utarget = 10;
        const OFFSET: Itarget = 0;

        let mut cpu = create_cpu();
        let initial_pc = cpu.pc();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let beq = Beq::from_fields(OFFSET, RT_IDX, RS_IDX);
        execute_terminated(&mut cpu, &beq, initial_pc);
    }

    #[test]
    fn test_beq_instruction_not_taken() {
        const RS_IDX: Utarget = 1;
        const RT_IDX: Utarget = 2;
        const RS_VALUE: Utarget = 10;
        const RT_VALUE: Utarget = 20;
        const OFFSET: Itarget = 4;

        let mut cpu = create_cpu();
        let next_pc = Pc(4);
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();
        cpu.reg_mut(RT_IDX).unwrap().write(RT_VALUE).unwrap();

        let beq = Beq::from_fields(OFFSET, RT_IDX, RS_IDX);
        execute_terminated(&mut cpu, &beq, next_pc);
    }

    #[test]
    fn test_j_instruction() {
        let mut cpu = create_cpu();
        {
            const JUMP_INDEX: u32 = 0x3ffffff;
            const EXPECTED_ADDR: Pc = Pc(0xffffffc);

            let j = J::from_fields(JUMP_INDEX);
            execute_terminated(&mut cpu, &j, EXPECTED_ADDR);
        }
        {
            let xor = Xor::from_fields(0, 0, 0);
            execute_accepted(&mut cpu, &xor);
        }
        {
            const JUMP_INDEX: u32 = 0x3ffffff;
            const EXPECTED_ADDR: Pc = Pc(0x1ffffffc);

            let j = J::from_fields(JUMP_INDEX);
            execute_terminated(&mut cpu, &j, EXPECTED_ADDR);
        }
        {
            const JUMP_INDEX: u32 = 0x0;
            const EXPECTED_ADDR: Pc = Pc(0x10000000);

            let j = J::from_fields(JUMP_INDEX);
            execute_terminated(&mut cpu, &j, EXPECTED_ADDR);
        }
    }

    #[test]
    fn test_j_instruction_self_jump() {
        const JUMP_INDEX: u32 = 0x0;
        const EXPECTED_ADDR: Pc = Pc(0x0);

        let mut cpu = create_cpu();
        let j = J::from_fields(JUMP_INDEX);
        execute_terminated(&mut cpu, &j, EXPECTED_ADDR);
    }
}
