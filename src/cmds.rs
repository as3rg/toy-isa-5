use instr_gen::{gen_instr, gen_instr_set};
use num_enum::TryFromPrimitive;

#[derive(Debug, Clone, Copy, PartialEq, Eq, TryFromPrimitive)]
#[repr(u32)]
pub enum Op1 {
    Generic = 0b000000,
    Ssat = 0b001100,
    Ld = 0b001010,
    Bne = 0b000110,
    Beq = 0b011110,
    St = 0b110010,
    J = 0b110110,
    Ldp = 0b111100,
    Cbit = 0b111001,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, TryFromPrimitive)]
#[repr(u32)]
pub enum Op2 {
    Nor = 0b001101,
    Bdep = 0b110011,
    Add = 0b011010,
    Clz = 0b110101,
    Xor = 0b101001,
    Syscall = 0b111000,
}

gen_instr! {
    Generic {
        op2: u6,
        data: u20 = 0,
        op1: u6,
    }
}

gen_instr_set! {
    Instr {
        Nor {
            op2: u6 = Op2::Nor,
            zeros: u5 = 0,
            rd: u5,
            rt: u5,
            rs: u5,
            op1: u6 = Op1::Generic,
        }

        Ldp {
            offset: i11,
            rt2: u5,
            rt1: u5,
            base: u5,
            op: u6 = Op1::Ldp,
        }

        Cbit {
            zeros: u11 = 0,
            imm5: u5,
            rs: u5,
            rd: u5,
            op: u6 = Op1::Cbit,
        }

        Bdep {
            op2: u6 = Op2::Bdep,
            zeros: u5 = 0,
            rs2: u5,
            rs1: u5,
            rd: u5,
            op1: u6 = Op1::Generic,
        }

        Add {
            op2: u6 = Op2::Add,
            zeros: u5 = 0,
            rd: u5,
            rt: u5,
            rs: u5,
            op1: u6 = Op1::Generic,
        }

        Ssat {
            zeros: u11 = 0,
            imm5: u5,
            rs: u5,
            rd: u5,
            op: u6 = Op1::Ssat,
        }

        St {
            offset: i16,
            rt: u5,
            base: u5,
            op: u6 = Op1::St,
        }

        Clz {
            op2: u6 = Op2::Clz,
            zeros: u10 = 0,
            rs: u5,
            rd: u5,
            op1: u6 = Op1::Generic,
        }

        Bne {
            offset: i16,
            rt: u5,
            rs: u5,
            op: u6 = Op1::Bne,
        }

        Ld {
            offset: i16,
            rt: u5,
            base: u5,
            op: u6 = Op1::Ld,
        }

        Xor {
            op2: u6 = Op2::Xor,
            zeros: u5 = 0,
            rd: u5,
            rt: u5,
            rs: u5,
            op1: u6 = Op1::Generic,
        }

        Syscall {
            op2: u6 = Op2::Syscall,
            code: u20,
            op1: u6 = Op1::Generic,
        }

        Beq {
            offset: i16,
            rt: u5,
            rs: u5,
            op: u6 = Op1::Beq,
        }

        J {
            index: u26,
            op: u6 = Op1::J,
        }
    }
}
