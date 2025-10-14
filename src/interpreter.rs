use num_enum::TryFromPrimitive;

use crate::cmds::*;
use crate::cpu::{CPUState, SysCallCode};
use crate::globals::*;
use crate::helpers::{bit_deposit, saturate_signed};

impl CPUState {
    pub fn interpret<T: Interpret>(&mut self, cmd: T) -> ExecResult<Pc> {
        cmd.interpret(self)?;
        Ok(self.pc())
    }
}

macro_rules! finish_cmd {
    ($cpu: expr) => {
        $cpu.jump_rel(PcOffset(CMD_SIZE.cast_signed())).map(|_| ())
    };
}

pub fn interpretation_error<T>(cpu: &mut CPUState, msg: String) -> ExecResult<T> {
    Err(ExecError::InterpretationError {
        msg,
        addr: cpu.pc(),
    })
}

pub trait Interpret {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult;
}

impl Interpret for Nor {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let rs = cpu.reg(self.get_rs())?.read()?;
        let rt = cpu.reg(self.get_rt())?.read()?;
        let result = !(rs | rt);
        cpu.reg_mut(self.get_rd())?.write(result)?;

        log::debug!(
            "pc: 0x{:08x} | r{} (0x{:x}) <- r{} (0x{:x}) nor r{} (0x{:x})",
            pc.0,
            self.get_rd(),
            result,
            self.get_rs(),
            rs,
            self.get_rt(),
            rt
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for Ldp {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let base = cpu.reg(self.get_base())?.read()?;
        let addr = base.wrapping_add_signed(self.get_offset());

        if (addr % WORD_SIZE) != 0 {
            return interpretation_error(cpu, "Misaligned store".into());
        }

        let mut value1 = TargetBuf::default();
        cpu.mem()?.read(addr, &mut value1)?;

        let mut value2 = TargetBuf::default();
        cpu.mem()?.read(addr.wrapping_add(4), &mut value2)?;

        let val1 = Utarget::from_le_bytes(value1);
        let val2 = Utarget::from_le_bytes(value2);

        cpu.reg_mut(self.get_rt1())?.write(val1)?;
        cpu.reg_mut(self.get_rt2())?.write(val2)?;

        log::debug!(
            "pc: 0x{:08x} | r{} (0x{:x}), r{} (0x{:x}) <- [r{} (0x{:x}) + {}]",
            pc.0,
            self.get_rt1(),
            val1,
            self.get_rt2(),
            val2,
            self.get_base(),
            base,
            self.get_offset()
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for Cbit {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let rs = cpu.reg(self.get_rs())?.read()?;
        let mask = 1 << self.get_imm5();
        let result = rs & !mask;
        cpu.reg_mut(self.get_rd())?.write(result)?;

        log::debug!(
            "pc: 0x{:08x} | r{} (0x{:x}) <- r{} (0x{:x}) & !(1 << {})",
            pc.0,
            self.get_rd(),
            result,
            self.get_rs(),
            rs,
            self.get_imm5()
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for Bdep {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let rs1 = cpu.reg(self.get_rs1())?.read()?;
        let rs2 = cpu.reg(self.get_rs2())?.read()?;
        let result = bit_deposit(rs1, rs2);
        cpu.reg_mut(self.get_rd())?.write(result)?;

        log::debug!(
            "pc: 0x{:08x} | r{} (0x{:x}) <- bit_deposit(r{} (0x{:x}), r{} (0x{:x}))",
            pc.0,
            self.get_rd(),
            result,
            self.get_rs1(),
            rs1,
            self.get_rs2(),
            rs2
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for Add {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let rs = cpu.reg(self.get_rs())?.read()?;
        let rt = cpu.reg(self.get_rt())?.read()?;
        let result = rs.wrapping_add(rt);
        cpu.reg_mut(self.get_rd())?.write(result)?;

        log::debug!(
            "pc: 0x{:08x} | r{} (0x{:x}) <- r{} (0x{:x}) + r{} (0x{:x})",
            pc.0,
            self.get_rd(),
            result,
            self.get_rs(),
            rs,
            self.get_rt(),
            rt
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for Ssat {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let rs = cpu.reg(self.get_rs())?.read()?;
        let saturated = saturate_signed(rs as _, self.get_imm5()) as _;
        cpu.reg_mut(self.get_rd())?.write(saturated)?;

        log::debug!(
            "pc: 0x{:08x} | r{} (0x{:x}) <- saturate_signed(r{} (0x{:x}), 0x{:x})",
            pc.0,
            self.get_rd(),
            saturated,
            self.get_rs(),
            rs,
            self.get_imm5()
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for St {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let base = cpu.reg(self.get_base())?.read()?;
        let rt = cpu.reg(self.get_rt())?.read()?;
        let addr = base.wrapping_add_signed(self.get_offset());

        if (addr % WORD_SIZE) != 0 {
            return interpretation_error(cpu, "Misaligned store".into());
        }

        cpu.mem_mut()?.write(addr, &rt.to_le_bytes())?;

        log::debug!(
            "pc: 0x{:08x} | [r{} (0x{:x}) + {}] <- r{} (0x{:x})",
            pc.0,
            self.get_base(),
            base,
            self.get_offset(),
            self.get_rt(),
            rt
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for Clz {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let rs = cpu.reg(self.get_rs())?.read()?;
        let leading_zeros = rs.leading_zeros();
        cpu.reg_mut(self.get_rd())?.write(leading_zeros)?;

        log::debug!(
            "pc: 0x{:08x} | r{} (0x{:x}) <- leading_zeros(r{} (0x{:x}))",
            pc.0,
            self.get_rd(),
            leading_zeros,
            self.get_rs(),
            rs
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for Bne {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let rs = cpu.reg(self.get_rs())?.read()?;
        let rt = cpu.reg(self.get_rt())?.read()?;

        if rs != rt {
            let new_pc = cpu.jump_rel(PcOffset(self.get_offset() * CMD_SIZE.cast_signed()))?;
            log::debug!(
                "pc: 0x{:08x} | bne: r{} (0x{:x}) != r{} (0x{:x}) -> 0x{:x}",
                pc.0,
                self.get_rs(),
                rs,
                self.get_rt(),
                rt,
                new_pc.0
            );
            Ok(())
        } else {
            log::debug!(
                "pc: 0x{:08x} | bne: r{} (0x{:x}) != r{} (0x{:x})",
                pc.0,
                self.get_rs(),
                rs,
                self.get_rt(),
                rt,
            );

            finish_cmd!(cpu)
        }
    }
}

impl Interpret for Ld {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let base = cpu.reg(self.get_base())?.read()?;
        let addr = base.wrapping_add_signed(self.get_offset());

        if (addr % WORD_SIZE) != 0 {
            return interpretation_error(cpu, "Misaligned load".into());
        }

        let mut value = TargetBuf::default();
        cpu.mem()?.read(addr, &mut value)?;
        let val = Utarget::from_le_bytes(value);

        cpu.reg_mut(self.get_rt())?.write(val)?;

        log::debug!(
            "pc: 0x{:08x} | r{} (0x{:x}) <- [r{} (0x{:x}) + {}]",
            pc.0,
            self.get_rt(),
            val,
            self.get_base(),
            base,
            self.get_offset(),
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for Xor {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let rs = cpu.reg(self.get_rs())?.read()?;
        let rt = cpu.reg(self.get_rt())?.read()?;
        let result = rs ^ rt;
        cpu.reg_mut(self.get_rd())?.write(result)?;

        log::debug!(
            "pc: 0x{:08x} | r{} (0x{:x}) <- r{} (0x{:x}) ^ r{} (0x{:x})",
            pc.0,
            self.get_rd(),
            result,
            self.get_rs(),
            rs,
            self.get_rt(),
            rt
        );

        finish_cmd!(cpu)
    }
}

impl Interpret for Syscall {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let code_num = cpu.reg(SYSCALL_CODE)?.read()?;
        let Ok(code) = SysCallCode::try_from_primitive(code_num) else {
            return interpretation_error(
                cpu,
                format!("Unknown syscall with code 0x{:x}", code_num),
            );
        };
        let args = [
            cpu.reg(SYSCALL_ARG0)?.read()?,
            cpu.reg(SYSCALL_ARG1)?.read()?,
            cpu.reg(SYSCALL_ARG2)?.read()?,
            cpu.reg(SYSCALL_ARG3)?.read()?,
            cpu.reg(SYSCALL_ARG4)?.read()?,
            cpu.reg(SYSCALL_ARG5)?.read()?,
            cpu.reg(SYSCALL_ARG6)?.read()?,
            cpu.reg(SYSCALL_ARG7)?.read()?,
        ];

        log::debug!(
            "pc: 0x{:08x} | syscall: {:?} with args {:?}",
            pc.0,
            code,
            args
        );

        let res = cpu.syscall(code, &args)?;
        cpu.reg_mut(SYSCALL_RET0)?.write(res)?;

        log::debug!("pc: 0x{:08x} | syscall result: 0x{:x}", pc.0, res);

        finish_cmd!(cpu)
    }
}

impl Interpret for Beq {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let rs = cpu.reg(self.get_rs())?.read()?;
        let rt = cpu.reg(self.get_rt())?.read()?;

        if rs == rt {
            let new_pc = cpu.jump_rel(PcOffset(self.get_offset() * CMD_SIZE.cast_signed()))?;
            log::debug!(
                "pc: 0x{:08x} | beq: r{} (0x{:x}) == r{} (0x{:x}) -> 0x{:x}",
                pc.0,
                self.get_rs(),
                rs,
                self.get_rt(),
                rt,
                new_pc.0
            );
            Ok(())
        } else {
            log::debug!(
                "pc: 0x{:08x} | beq: r{} (0x{:x}) == r{} (0x{:x})",
                pc.0,
                self.get_rs(),
                rs,
                self.get_rt(),
                rt,
            );

            finish_cmd!(cpu)
        }
    }
}

impl Interpret for J {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        let pc = cpu.pc();
        let mask = 0b00001111111111111111111111111111;
        let new_addr = Pc(cpu.pc().0 & !mask | (self.get_index() * CMD_SIZE) & mask);

        log::debug!(
            "pc: 0x{:08x} | jump to 0x{:x} (index: {})",
            pc.0,
            new_addr.0,
            self.get_index()
        );

        cpu.jump_abs(new_addr).map(|_| ())
    }
}

impl Interpret for Instr {
    fn interpret(&self, cpu: &mut CPUState) -> ExecResult {
        match self {
            Instr::Nor(cmd) => cmd.interpret(cpu),
            Instr::Ldp(cmd) => cmd.interpret(cpu),
            Instr::Cbit(cmd) => cmd.interpret(cpu),
            Instr::Bdep(cmd) => cmd.interpret(cpu),
            Instr::Add(cmd) => cmd.interpret(cpu),
            Instr::Ssat(cmd) => cmd.interpret(cpu),
            Instr::St(cmd) => cmd.interpret(cpu),
            Instr::Clz(cmd) => cmd.interpret(cpu),
            Instr::Bne(cmd) => cmd.interpret(cpu),
            Instr::Ld(cmd) => cmd.interpret(cpu),
            Instr::Xor(cmd) => cmd.interpret(cpu),
            Instr::Syscall(cmd) => cmd.interpret(cpu),
            Instr::Beq(cmd) => cmd.interpret(cpu),
            Instr::J(cmd) => cmd.interpret(cpu),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::CPUState;

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
        assert_eq!(cpu.interpret(nor).unwrap(), Pc(4));

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
        assert_eq!(cpu.interpret(ldp).unwrap(), Pc(4));

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
        let result = cpu.interpret(ldp);

        assert!(result.is_err());
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
        let result = cpu.interpret(ldp);

        assert!(result.is_err());
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
        let result = cpu.interpret(ldp);

        assert!(!result.is_err());
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
        assert_eq!(cpu.interpret(cbit).unwrap(), Pc(4));

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
        assert_eq!(cpu.interpret(cbit).unwrap(), Pc(4));

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_bdep_instruction() {
        const RS1_IDX: Utarget = 1;
        const RS2_IDX: Utarget = 2;
        const RD_IDX: Utarget = 3;
        const RS1_VALUE: Utarget = 0x239;
        const RS2_VALUE: Utarget = 0x00ff00ff;
        const EXPECTED_RESULT: Utarget = 0x20039;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS1_IDX).unwrap().write(RS1_VALUE).unwrap();
        cpu.reg_mut(RS2_IDX).unwrap().write(RS2_VALUE).unwrap();

        let bdep = Bdep::from_fields(RS2_IDX, RS1_IDX, RD_IDX);
        assert_eq!(cpu.interpret(bdep).unwrap(), Pc(4));

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
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
        assert_eq!(cpu.interpret(add).unwrap(), Pc(4));

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
        assert_eq!(cpu.interpret(add).unwrap(), Pc(4));

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_ssat_instruction() {
        const RS_IDX: Utarget = 1;
        const RD_IDX: Utarget = 2;
        const BIT_COUNT: Utarget = 5;
        const RS_VALUE: Utarget = 1000;
        const EXPECTED_RESULT: Utarget = 15;

        let mut cpu = create_cpu();
        cpu.reg_mut(RS_IDX).unwrap().write(RS_VALUE).unwrap();

        let ssat = Ssat::from_fields(BIT_COUNT, RS_IDX, RD_IDX);
        assert_eq!(cpu.interpret(ssat).unwrap(), Pc(4));

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
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
        assert_eq!(cpu.interpret(st).unwrap(), Pc(4));

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
        let result = cpu.interpret(st);

        assert!(result.is_err());
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
        let result = cpu.interpret(st);

        assert!(result.is_err());
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
        let result = cpu.interpret(st);

        assert!(!result.is_err());
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
        assert_eq!(cpu.interpret(clz).unwrap(), Pc(4));

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
        assert_eq!(cpu.interpret(clz).unwrap(), Pc(4));

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
        assert_eq!(cpu.interpret(clz).unwrap(), Pc(4));

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
        assert_eq!(cpu.interpret(bne).unwrap(), next_pc);
        assert_eq!(cpu.pc(), next_pc);
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
        assert_eq!(cpu.interpret(bne).unwrap(), next_pc);
        assert_eq!(cpu.pc(), next_pc);
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
        assert_eq!(cpu.interpret(bne).unwrap(), initial_pc);
        assert_eq!(cpu.pc(), initial_pc);
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
        assert_eq!(cpu.interpret(ld).unwrap(), Pc(4));

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

        let result = cpu.interpret(ld);
        assert!(result.is_err());
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

        let result = cpu.interpret(ld);
        assert!(result.is_err());
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

        let result = cpu.interpret(ld);
        assert!(!result.is_err());
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
        assert_eq!(cpu.interpret(xor).unwrap(), Pc(4));

        let result = cpu.reg(RD_IDX).unwrap().read().unwrap();
        assert_eq!(result, EXPECTED_RESULT);
    }

    #[test]
    fn test_syscall_instruction() {
        let mut cpu = create_cpu();
        let syscall = Syscall::from_fields(0);
        let result = cpu.interpret(syscall);
        assert!(result.is_err());
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
        assert_eq!(cpu.interpret(beq).unwrap(), next_pc);
        assert_eq!(cpu.pc(), next_pc);
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
        assert_eq!(cpu.interpret(beq).unwrap(), initial_pc);
        assert_eq!(cpu.pc(), initial_pc);
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
        assert_eq!(cpu.interpret(beq).unwrap(), next_pc);
        assert_eq!(cpu.pc(), next_pc);
    }

    #[test]
    fn test_j_instruction() {
        let mut cpu = create_cpu();
        {
            const JUMP_INDEX: u32 = 0x3ffffff;
            const EXPECTED_ADDR: Pc = Pc(0xffffffc);

            let j = J::from_fields(JUMP_INDEX);
            assert_eq!(cpu.interpret(j).unwrap(), EXPECTED_ADDR);
            assert_eq!(cpu.pc(), EXPECTED_ADDR);
        }
        {
            const EXPECTED_ADDR: Pc = Pc(0x10000000);
            let xor = Xor::from_fields(0, 0, 0);
            assert_eq!(cpu.interpret(xor).unwrap(), EXPECTED_ADDR);
        }
        {
            const JUMP_INDEX: u32 = 0x3ffffff;
            const EXPECTED_ADDR: Pc = Pc(0x1ffffffc);

            let j = J::from_fields(JUMP_INDEX);
            assert_eq!(cpu.interpret(j).unwrap(), EXPECTED_ADDR);
            assert_eq!(cpu.pc(), EXPECTED_ADDR);
        }
        {
            const JUMP_INDEX: u32 = 0x0;
            const EXPECTED_ADDR: Pc = Pc(0x10000000);

            let j = J::from_fields(JUMP_INDEX);
            assert_eq!(cpu.interpret(j).unwrap(), EXPECTED_ADDR);
            assert_eq!(cpu.pc(), EXPECTED_ADDR);
        }
    }

    #[test]
    fn test_j_instruction_self_jump() {
        const JUMP_INDEX: u32 = 0x0;
        const EXPECTED_ADDR: Pc = Pc(0x0);

        let mut cpu = create_cpu();
        let j = J::from_fields(JUMP_INDEX);
        assert_eq!(cpu.interpret(j).unwrap(), EXPECTED_ADDR);
        assert_eq!(cpu.pc(), EXPECTED_ADDR);
    }
}
