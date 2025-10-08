use num_enum::TryFromPrimitive;

use crate::cmds::*;

pub fn parse_instr(raw: u32) -> Option<Instr> {
    let generic = Generic::from_raw(raw);

    let Ok(op1) = Op1::try_from_primitive(generic.get_op1()) else {
        return None;
    };

    match op1 {
        Op1::Ssat => Some(Instr::Ssat(Ssat::from_raw(raw))),
        Op1::Ld => Some(Instr::Ld(Ld::from_raw(raw))),
        Op1::Bne => Some(Instr::Bne(Bne::from_raw(raw))),
        Op1::Beq => Some(Instr::Beq(Beq::from_raw(raw))),
        Op1::St => Some(Instr::St(St::from_raw(raw))),
        Op1::J => Some(Instr::J(J::from_raw(raw))),
        Op1::Ldp => Some(Instr::Ldp(Ldp::from_raw(raw))),
        Op1::Cbit => Some(Instr::Cbit(Cbit::from_raw(raw))),

        Op1::Generic => {
            let Ok(op2) = Op2::try_from_primitive(generic.get_op2()) else {
                return None;
            };

            match op2 {
                Op2::Nor => Some(Instr::Nor(Nor::from_raw(raw))),
                Op2::Bdep => Some(Instr::Bdep(Bdep::from_raw(raw))),
                Op2::Add => Some(Instr::Add(Add::from_raw(raw))),
                Op2::Clz => Some(Instr::Clz(Clz::from_raw(raw))),
                Op2::Xor => Some(Instr::Xor(Xor::from_raw(raw))),
                Op2::Syscall => Some(Instr::Syscall(Syscall::from_raw(raw))),
            }
        }
    }
}
