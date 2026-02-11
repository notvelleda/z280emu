use crate::BusAccessor;
use instruction_decoder::decode_instructions;
use log::{info, warn};

pub trait RegisterOrMemoryAccessor<R> {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> R;
    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: R);
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Register {
    A,
    F,
    B,
    C,
    D,
    E,
    H,
    L,
    I,
    R,
    IXH,
    IXL,
    IYH,
    IYL,
    BC,
    DE,
    HL,
    IX,
    IY,
    PC,
    SP,
    USP,
}

impl RegisterOrMemoryAccessor<u8> for Register {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> u8 {
        match self {
            Self::A => cpu_state.register_file.current_af_bank().a,
            Self::F => cpu_state.register_file.current_af_bank().f.into_bits(),
            Self::B => cpu_state.register_file.current_x_bank().b,
            Self::C => cpu_state.register_file.current_x_bank().c,
            Self::D => cpu_state.register_file.current_x_bank().d,
            Self::E => cpu_state.register_file.current_x_bank().e,
            Self::H => (cpu_state.register_file.current_x_bank().hl & 0xff) as u8,
            Self::L => (cpu_state.register_file.current_x_bank().hl >> 8) as u8,
            Self::I => cpu_state.register_file.i,
            Self::R => cpu_state.register_file.r,
            Self::IXH => (cpu_state.register_file.ix & 0xff) as u8,
            Self::IXL => (cpu_state.register_file.ix >> 8) as u8,
            Self::IYH => (cpu_state.register_file.iy & 0xff) as u8,
            Self::IYL => (cpu_state.register_file.iy >> 8) as u8,
            _ => {
                let value: u16 = self.get(cpu_state);
                value as u8
            }
        }
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: u8) {
        match self {
            Self::A => cpu_state.register_file.current_af_bank_mut().a = value,
            Self::F => cpu_state.register_file.current_af_bank_mut().f.set_bits(value),
            Self::B => cpu_state.register_file.current_x_bank_mut().b = value,
            Self::C => cpu_state.register_file.current_x_bank_mut().c = value,
            Self::D => cpu_state.register_file.current_x_bank_mut().d = value,
            Self::E => cpu_state.register_file.current_x_bank_mut().e = value,
            Self::H => {
                let hl = &mut cpu_state.register_file.current_x_bank_mut().hl;
                *hl = (*hl & 0x00ff) | ((value as u16) << 8);
            }
            Self::L => {
                let hl = &mut cpu_state.register_file.current_x_bank_mut().hl;
                *hl = (*hl & 0xff00) | value as u16;
            }
            Self::I => cpu_state.register_file.i = value,
            Self::R => cpu_state.register_file.r = value,
            Self::IXH => {
                let ix = &mut cpu_state.register_file.ix;
                *ix = (*ix & 0x00ff) | ((value as u16) << 8);
            }
            Self::IXL => {
                let ix = &mut cpu_state.register_file.ix;
                *ix = (*ix & 0xff00) | value as u16;
            }
            Self::IYH => {
                let iy = &mut cpu_state.register_file.iy;
                *iy = (*iy & 0x00ff) | ((value as u16) << 8);
            }
            Self::IYL => {
                let iy = &mut cpu_state.register_file.iy;
                *iy = (*iy & 0xff00) | value as u16;
            }
            _ => self.set(cpu_state, value as u16),
        }
    }
}

impl RegisterOrMemoryAccessor<u16> for Register {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> u16 {
        match self {
            Self::BC => {
                let partial_file = cpu_state.register_file.current_x_bank();
                ((partial_file.b as u16) << 8) | (partial_file.c as u16)
            }
            Self::DE => {
                let partial_file = cpu_state.register_file.current_x_bank();
                ((partial_file.d as u16) << 8) | (partial_file.e as u16)
            }
            Self::HL => cpu_state.register_file.current_x_bank().hl,
            Self::IX => cpu_state.register_file.ix,
            Self::IY => cpu_state.register_file.iy,
            Self::PC => cpu_state.register_file.pc,
            Self::SP => *cpu_state.register_file.current_stack_pointer(),
            _ => {
                let value: u8 = self.get(cpu_state);
                value as u16
            }
        }
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: u16) {
        match self {
            Self::BC => {
                let partial_file = cpu_state.register_file.current_x_bank_mut();
                partial_file.b = (value >> 8) as u8;
                partial_file.c = (value & 0xff) as u8;
            }
            Self::DE => {
                let partial_file = cpu_state.register_file.current_x_bank_mut();
                partial_file.d = (value >> 8) as u8;
                partial_file.e = (value & 0xff) as u8;
            }
            Self::HL => cpu_state.register_file.current_x_bank_mut().hl = value,
            Self::IX => cpu_state.register_file.ix = value,
            Self::IY => cpu_state.register_file.iy = value,
            Self::PC => cpu_state.register_file.pc = value,
            Self::SP => *cpu_state.register_file.current_stack_pointer_mut() = value,
            _ => self.set(cpu_state, value as u8),
        }
    }
}

impl RegisterOrMemoryAccessor<i8> for Register {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> i8 {
        let value: u8 = self.get(cpu_state);
        value as i8
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: i8) {
        self.set(cpu_state, value as u8);
    }
}

impl RegisterOrMemoryAccessor<i16> for Register {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> i16 {
        match self {
            Self::BC | Self::DE | Self::HL | Self::IX | Self::IY | Self::PC | Self::SP => {
                let value: u16 = self.get(cpu_state);
                value as i16
            }
            _ => {
                let value: u8 = self.get(cpu_state);
                i16::from(value as i8)
            }
        }
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: i16) {
        self.set(cpu_state, value as u16);
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Memory {
    address: u32,
}

impl RegisterOrMemoryAccessor<u8> for Memory {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> u8 {
        let mut result = [0];

        cpu_state.bus_accessor.read(crate::BusAddressSpace::Memory, self.address, &mut result);

        result[0]
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: u8) {
        cpu_state.bus_accessor.write(crate::BusAddressSpace::Memory, self.address, &[value]);
    }
}

impl RegisterOrMemoryAccessor<u16> for Memory {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> u16 {
        let mut result = [0; 2];

        cpu_state.bus_accessor.read(crate::BusAddressSpace::Memory, self.address, &mut result);

        u16::from_le_bytes(result)
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: u16) {
        cpu_state.bus_accessor.write(crate::BusAddressSpace::Memory, self.address, &value.to_le_bytes());
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Immediate {
    Byte(u8),
    Word(u16),
    UnknownSigned(isize),
    UnknownUnsigned(usize),
}

impl RegisterOrMemoryAccessor<u8> for Immediate {
    fn get<T: BusAccessor>(&self, _cpu_state: &mut super::CPUState<T>) -> u8 {
        match self {
            Self::Byte(value) => *value,
            Self::Word(value) => *value as u8,
            Self::UnknownSigned(value) => *value as u8,
            Self::UnknownUnsigned(value) => *value as u8,
        }
    }

    fn set<T: BusAccessor>(&self, _cpu_state: &mut super::CPUState<T>, _value: u8) {
        unimplemented!()
    }
}

impl RegisterOrMemoryAccessor<u16> for Immediate {
    fn get<T: BusAccessor>(&self, _cpu_state: &mut super::CPUState<T>) -> u16 {
        match self {
            Self::Byte(value) => u16::from(*value),
            Self::Word(value) => *value,
            Self::UnknownSigned(value) => *value as u16,
            Self::UnknownUnsigned(value) => *value as u16,
        }
    }

    fn set<T: BusAccessor>(&self, _cpu_state: &mut super::CPUState<T>, _value: u16) {
        unimplemented!()
    }
}

impl RegisterOrMemoryAccessor<i8> for Immediate {
    fn get<T: BusAccessor>(&self, _cpu_state: &mut super::CPUState<T>) -> i8 {
        match self {
            Self::Byte(value) => *value as i8,
            Self::Word(value) => (*value as i16) as i8,
            Self::UnknownSigned(value) => *value as i8,
            Self::UnknownUnsigned(value) => *value as i8,
        }
    }

    fn set<T: BusAccessor>(&self, _cpu_state: &mut super::CPUState<T>, _value: i8) {
        unimplemented!()
    }
}

impl RegisterOrMemoryAccessor<i16> for Immediate {
    fn get<T: BusAccessor>(&self, _cpu_state: &mut super::CPUState<T>) -> i16 {
        match self {
            Self::Byte(value) => i16::from(*value as i8),
            Self::Word(value) => *value as i16,
            Self::UnknownSigned(value) => *value as i16,
            Self::UnknownUnsigned(value) => *value as i16,
        }
    }

    fn set<T: BusAccessor>(&self, _cpu_state: &mut super::CPUState<T>, _value: i16) {
        unimplemented!()
    }
}

fn indirect<T: BusAccessor>(cpu_state: &mut super::CPUState<T>, lhs: impl RegisterOrMemoryAccessor<u16>, rhs: impl RegisterOrMemoryAccessor<i16>) -> Memory {
    Memory {
        address: lhs.get(cpu_state).wrapping_add_signed(rhs.get(cpu_state)) as u32,
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ConditionCode {
    /// NZ
    NZ,
    /// Z
    Z,
    /// NC
    NC,
    /// C
    C,
    /// PO/NV
    PONV,
    /// PE/V
    PEV,
    /// P/NS
    PNS,
    /// M/S
    MS,
    /// Unconditional
    Always,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum InterruptMode {
    Mode0,
    Mode1,
    Mode2,
    Mode3,
}

decode_instructions! {
    instruction_word_size: 1,
    prefixes: {
        0b11001011 => CBPrefix,
        0b11101101 => EDPrefix,
        0b11011101 => IXOverride (modifier),
        0b11111101 => IYOverride (modifier),
    },
    prefix_combinations: {
        opcode + immediates,
        CBPrefix + opcode + immediates,
        EDPrefix + opcode + immediates,
        IXOverride + opcode + immediates,
        IYOverride + opcode + immediates,
        IXOverride + CBPrefix + immediates + opcode,
        IYOverride + CBPrefix + immediates + opcode,
        IXOverride + EDPrefix + opcode + immediates,
        IYOverride + EDPrefix + opcode + immediates,
    },
    addressing_modes: {
        r: {
            0b000 => Register::B,
            0b001 => Register::C,
            0b010 => Register::D,
            0b011 => Register::E,
            0b100 => Register::H,
            0b101 => Register::L,
            0b111 => Register::A,
        },
        ix_iy_components: {
            IXOverride => {
                0b100 => Register::IXH,
                0b101 => Register::IXL,
            },
            IYOverride => {
                0b100 => Register::IYH,
                0b101 => Register::IYL,
            },
        },
        hl_indirect: {
            0b110 => indirect(Register::HL),
        },
        hl_indirect_overrides: {
            IXOverride => {
                0b110 => indirect(Register::IX + imm8()),
            },
            IYOverride => {
                0b110 => indirect(Register::IY + imm8()),
            },
        },
        hl_indirection: {
            hl_indirect() | hl_indirect_overrides(),
        },
        extended_indirect_modes: {
            IXOverride => {
                0b000 => indirect(Register::SP + imm16()),
                0b001 => indirect(Register::HL + Register::IX),
                0b010 => indirect(Register::HL + Register::IY),
                0b011 => indirect(Register::IX + Register::IY),
                0b111 => indirect(imm16()),
            },
            IYOverride => {
                0b000 => indirect(Register::PC + imm16()),
                0b001 => indirect(Register::IX + imm16()),
                0b010 => indirect(Register::IY + imm16()),
                0b011 => indirect(Register::HL + imm16()),
            },
        },
        // R, RX, IR, DA, X, SX, RA, SR, BX
        src_dst: {
            r() | ix_iy_components() | hl_indirection() | extended_indirect_modes(),
        },
        rr: {
            0b00 => Register::BC,
            0b01 => Register::DE,
            IXOverride => {
                0b10 => Register::IX,
            },
            IYOverride => {
                0b10 => Register::IY,
            },
            0b10 => Register::HL,
            0b11 => Register::SP,
        },
        rr_ix_expansion: {
            IXOverride => {
                0b00 => indirect(Register::HL),
                0b01 => indirect(imm16()),
                0b11 => indirect(Register::PC + imm16()),
            },
        },
        rr_iy_expansion: {
            IYOverride => {
                0b00 => indirect(Register::IX + imm16()),
                0b01 => indirect(Register::IY + imm16()),
                0b10 => Register::IY,
                0b11 => imm16(),
            },
        },
        rr_expanded: {
            rr() | rr_ix_expansion() | rr_iy_expansion()
        },
        hl: {
            IXOverride => {
                Register::IX,
            },
            IYOverride => {
                Register::IY,
            },
            Register::HL,
        },
        hl_indirect_sx: {
            IXOverride => {
                indirect(Register::IX + imm8()),
            },
            IYOverride => {
                indirect(Register::IY + imm8()),
            },
            indirect(Register::HL),
        },
        cc: {
            0b000 => ConditionCode::NZ,
            0b001 => ConditionCode::Z,
            0b010 => ConditionCode::NC,
            0b011 => ConditionCode::C,
            0b100 => ConditionCode::PONV,
            0b101 => ConditionCode::PEV,
            0b110 => ConditionCode::PNS,
            0b111 => ConditionCode::MS,
        },
        cc_simplified: {
            0b011 => ConditionCode::Always,
            0b100 => ConditionCode::NZ,
            0b101 => ConditionCode::Z,
            0b110 => ConditionCode::NC,
            0b111 => ConditionCode::C,
        },
        // IR, DA, RA
        call_addr: {
            IXOverride => {
                indirect(Register::HL),
            },
            IYOverride => {
                indirect(Register::PC + imm16())
            },
            imm16(),
        },
        lda_extended: {
            0b000 => indirect(Register::SP + imm16()),
            0b001 => indirect(Register::HL + Register::IX),
            0b010 => indirect(Register::HL + Register::IY),
            0b011 => indirect(Register::IX + Register::IY),
            0b100 => indirect(Register::PC + imm16()),
            0b101 => indirect(Register::IX + imm16()),
            0b110 => indirect(Register::IY + imm16()),
            0b111 => indirect(Register::HL + imm16()),
        },
    },
    instructions: {
        "ADC (byte form)": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_001_***", src: src_dst(0..3),
            // IM
            "11_001_110", src: imm8(),
        ] => {
            info!("ADC (byte form), src: {src:?}");
        },
        "ADC (word form)": ["01_**1_010" (EDPrefix), src: rr(4..6), dst: hl()] => {
            info!("ADC (word form), src: {src:?}, dst: {dst:?}");
        },
        "ADD": ["01_101_101" (EDPrefix), dst: hl()] => {
            info!("ADD, dst: {dst:?}");
        },
        "ADD (byte form)": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_000_***", src: src_dst(0..3),
            // IM
            "11_000_110", src: imm8(),
        ] => {
            info!("ADD (byte form), src: {src:?}");
        },
        "ADD (word form)": ["00_**1_001", src: rr(4..6), dst: hl()] => {
            info!("ADD (word form), src: {src:?}, dst: {dst:?}");
        },
        "ADDW": ["11_**0_110" (EDPrefix), src: rr_expanded(4..6)] => {
            info!("ADDW, src: {src:?}");
        },
        "AND": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_100_***", src: src_dst(0..3),
            // IM
            "11_100_110", src: imm8(),
        ] => {
            info!("AND, src: {src:?}");
        },
        "BIT": ["01_***_***" (CBPrefix), b: imm_signed(3..6), r: r(0..3) | hl_indirection(0..3)] => {
            info!("BIT, b: {b:?}, r: {r:?}");
        },
        "CALL": [
            // conditional call
            "11_***_100", cc: cc(3..6), addr: call_addr(),
            // unconditional call
            "11_001_101", cc: ConditionCode::Always, addr: call_addr(),
        ] => {
            info!("CALL, cc: {cc:?}, addr: {addr:?}");
        },
        "CCF": ["00_111_111"] => {
            info!("CCF");
        },
        "CP": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_111_***", src: src_dst(0..3),
            // IM
            "11_111_110", src: imm8(),
        ] => {
            info!("CP, src: {src:?}");
        },
        "CPD": ["10_101_001" (EDPrefix)] => {
            info!("CPD");
        },
        "CPDR": ["10_111_001" (EDPrefix)] => {
            info!("CPDR");
        },
        // CPI
        ["10_100_001" (EDPrefix)] => {
            info!("CPI");
        },
        "CPIR": ["10_110_001" (EDPrefix)] => {
            info!("CPIR");
        },
        "CPL": ["00_101_111"] => {
            info!("CPL");
        },
        "CPW": ["11_**0_111" (EDPrefix), src: rr_expanded(4..6)] => {
            info!("CPW, src: {src:?}");
        },
        "DAA": ["00_100_111"] => {
            info!("DAA");
        },
        "DEC (byte form)": ["00_***_101", dst: src_dst(3..6)] => {
            info!("DEC (byte form), dst: {dst:?}");
        },
        "DEC (word form)": ["00_**1_011", dst: rr_expanded(4..6)] => {
            info!("DEC (word form), dst: {dst:?}");
        },
        "DI": [
            "11_110_011", mask: const(0x7f),
            "01_110_111" (EDPrefix), mask: imm8(),
        ] => {
            info!("DI, mask: {mask:?}");
        },
        "DIV": [
            "11_***_100" (EDPrefix), src: src_dst(3..6),
            "11_111_100" (EDPrefix + IYOverride), src: imm8(),
        ] => {
            info!("DIV (byte form), src: {src:?}");
        },
        "DIVU": [
            "11_***_101" (EDPrefix), src: src_dst(3..6),
            "11_111_101" (EDPrefix + IYOverride), src: imm8(),
        ] => {
            info!("DIVU (byte form), src: {src:?}");
        },
        "DIVUW": ["11_**1_011" (EDPrefix), src: rr_expanded(4..6)] => {
            info!("DIVUW, src: {src:?}");
        },
        "DIVW": ["11_**1_010" (EDPrefix), src: rr_expanded(4..6)] => {
            info!("DIVW, src: {src:?}");
        },
        "DJNZ": ["00_010_000", addr: indirect(Register::PC + imm8())] => {
            info!("DJNZ, addr: {addr:?}")
        },
        "EI": [
            "11_111_011", mask: const(0x7f),
            "01_111_111" (EDPrefix), mask: imm8(),
        ] => {
            info!("EI, mask: {mask:?}");
        },
        "EX AF, AF'": ["00_001_000"] => {
            info!("EX AF, AF'");
        },
        "EX (SP)": ["11_100_011", dst: hl()] => {
            info!("EX (SP), dst: {dst:?}");
        },
        "EX H, L": ["11_101_111" (EDPrefix)] => {
            info!("EX H, L");
        },
        "EX HL": [
            "11_101_011", src: Register::DE,
            "11_101_011" (IXOverride), src: Register::IX,
            "11_101_011" (IYOverride), src: Register::IY,
        ] => {
            info!("EX HL, src: {src:?}");
        },
        "EX A": ["00_***_111" (EDPrefix), src: src_dst(3..6)] => {
            info!("EX A, src: {src:?}");
        },
        "EXTS (byte form)": ["10_100_100" (EDPrefix)] => {
            info!("EXTS (byte form)");
        },
        "EXTS (word form)": ["10_101_100" (EDPrefix)] => {
            info!("EXTS (word form)");
        },
        "EXX": ["11_011_001"] => {
            info!("EXX");
        },
        "HALT": ["01_110_110"] => {
            info!("HALT");
        },
        "IM": [
            "01_000_110" (EDPrefix), p: InterruptMode::Mode0,
            "01_010_110" (EDPrefix), p: InterruptMode::Mode1,
            "01_011_110" (EDPrefix), p: InterruptMode::Mode2,
            "01_001_110" (EDPrefix), p: InterruptMode::Mode3,
        ] => {
            info!("IM, p: {p:?}");
        },
        "IN": [
            "01_***_000" (EDPrefix), src: Register::C, dst: r(3..6) | ix_iy_components(3..6) | extended_indirect_modes(3..6),
            "11_011_011", src: imm8(), dst: Register::A,
        ] => {
            info!("IN, src: {src:?}, dst: {dst:?}");
        },
        "INC (byte form)": ["00_***_100", dst: src_dst(3..6)] => {
            info!("INC (byte form), dst: {dst:?}");
        },
        "INC (word form)": ["00_**0_011", dst: rr_expanded(4..6)] => {
            info!("INC (word form), dst: {dst:?}");
        },
        "IND": ["10_101_010" (EDPrefix)] => {
            info!("IND");
        },
        "INDW": ["10_001_010" (EDPrefix)] => {
            info!("INDW");
        },
        "INDR": ["10_111_010" (EDPrefix)] => {
            info!("INDR");
        },
        "INDRW": ["10_011_010" (EDPrefix)] => {
            info!("INDRW");
        },
        "INI": ["10_100_010" (EDPrefix)] => {
            info!("INI");
        },
        "INIW": ["10_000_010" (EDPrefix)] => {
            info!("INIW");
        },
        "INIR": ["10_110_010" (EDPrefix)] => {
            info!("INIR");
        },
        "INIRW": ["10_010_010" (EDPrefix)] => {
            info!("INIRW");
        },
        "IN HL": ["10_110_111" (EDPrefix)] => {
            info!("IN HL");
        },
        "JAF": ["00_101_000" (IXOverride), addr: indirect(Register::PC + imm8())] => {
            info!("JAF, addr: {addr:?}");
        },
        "JAR": ["00_100_000" (IXOverride), addr: indirect(Register::PC + imm8())] => {
            info!("JAR, addr: {addr:?}");
        },
        "JP": [
            "11_***_010" (IXOverride), cc: cc(3..6), dst: indirect(Register::HL),
            "11_101_001", cc: ConditionCode::Always, dst: indirect(hl()),
            "11_***_010", cc: cc(3..6), dst: imm16(),
            "11_000_011", cc: ConditionCode::Always, dst: imm16(),
            "11_***_010" (IYOverride), cc: cc(3..6), dst: indirect(Register::PC + imm16()),
            "11_000_011" (IYOverride), cc: ConditionCode::Always, dst: indirect(Register::PC + imm16()),
        ] => {
            info!("JP, cc: {cc:?}, dst: {dst:?}");
        },
        "JR": ["00_***_000", cc: cc_simplified(3..6), addr: indirect(Register::PC + imm8())] => {
            info!("JR, cc: {cc:?}, addr: {addr:?}");
        },
        "LD": [
            // LD A, *

            // R is a duplicate of LD register (byte)
            // RX, IR, X, SX, RA, SR, BX
            "01_111_***", src: ix_iy_components(0..3) | hl_indirect_overrides(0..3) | extended_indirect_modes(0..3), dst: Register::A,
            // IM is a duplicate of LD immediate (byte)
            // IR
            "00_001_010", src: indirect(Register::BC), dst: Register::A,
            "00_011_010", src: indirect(Register::DE), dst: Register::A,
            // DA
            "00_111_010", src: indirect(imm16()), dst: Register::A,

            // LD *, A

            // R is a duplicate of LD register (byte)
            // R, RX, IR, X, SX, RA, SR, BX
            "01_***_111", src: Register::A, dst: ix_iy_components(3..6) | hl_indirect_overrides(3..6) | extended_indirect_modes(3..6),
            // IR
            "00_000_010", src: Register::A, dst: indirect(Register::BC),
            "00_010_010", src: Register::A, dst: indirect(Register::DE),
            // DA
            "00_110_010", src: Register::A, dst: indirect(imm16()),

            // LD A, I
            "01_010_111" (EDPrefix), src: Register::I, dst: Register::A,
            // LD A, R
            "01_011_111" (EDPrefix), src: Register::R, dst: Register::A,

            // LD I, A
            "01_000_111" (EDPrefix), src: Register::A, dst: Register::I,
            // LD R, A
            "01_001_111" (EDPrefix), src: Register::A, dst: Register::R,

            // LD immediate (byte)
            "00_***_110", dst: src_dst(3..6), src: imm8(),

            // LD register (byte)

            // R, RX, IR, SX
            "01_***_***", src: r(0..3) | hl_indirection(0..3) | ix_iy_components(0..3), dst: r(3..6) | hl_indirection(3..6) | ix_iy_components(3..6),
            // IM is a duplicate of LD immediate (byte)

            // LDW
            "00_**0_001", dst: rr(4..6) | rr_ix_expansion(4..6), src: imm16(),

            // LD[W] (addressing register)

            // IM is a duplicate of LDW
            // DA
            "00_101_010", src: indirect(imm16()), dst: hl(),
            "00_100_010", src: hl(), dst: indirect(imm16()),
            // X, RA, SR, BX
            "00_***_100" (EDPrefix), src: lda_extended(3..6), dst: hl(),
            "00_***_101" (EDPrefix), src: hl(), dst: lda_extended(3..6),

            // LD[W] (word)

            // IM
            "00_**0_001", src: imm16(), dst: hl_no_overrides(4..6),
            // IR, SX
            "00_**0_110" (EDPrefix), src: hl_indirect_sx(), dst: hl_no_overrides(4..6),
            "00_**1_110" (EDPrefix), src: hl_no_overrides(4..6), dst: hl_indirect_sx(),
            // DA
            "01_**1_011" (EDPrefix), src: indirect(imm16()), dst: hl_no_overrides(4..6),
            "01_**0_011" (EDPrefix), src: hl_no_overrides(4..6), dst: indirect(imm16()),

            // LD[W] (stack pointer)

            // R
            "11_111_001", src: hl(), dst: Register::SP,
            // IM is a duplicate of LD[W] (word) IM
            // IR, SX
            "00_110_110" (EDPrefix), src: hl_indirect_sx(), dst: Register::SP,
            "00_111_110" (EDPrefix), src: Register::SP, dst: hl_indirect_sx(),
            // DA
            "01_111_011" (EDPrefix), src: indirect(imm16()), dst: Register::SP,
            "01_110_011" (EDPrefix), src: Register::SP, dst: indirect(imm16()),
        ] => {
            info!("LD, src: {src:?}, dst: {dst:?}");
        },
        "LDA": [
            // DA is a duplicate of LDW
            // X, RA, SR, BX
            "00_***_010" (EDPrefix), src: lda_extended(3..6), dst: hl(),
        ] => {
            info!("LDA, src: {src:?}, dst: {dst:?}");
        },
        "LDCTL": [
            "01_100_110" (EDPrefix), src: Register::C, dst: hl(),
            "01_101_110" (EDPrefix), src: hl(), dst: Register::C,
            "10_000_111" (EDPrefix), src: Register::USP, dst: hl(),
            "10_001_111" (EDPrefix), src: hl(), dst: Register::USP,
        ] => {
            info!("LDCTL, src: {src:?}, dst: {dst:?}");
        },
        "LDD": ["10_101_000" (EDPrefix)] => {
            info!("LDD");
        },
        "LDDR": ["10_111_000" (EDPrefix)] => {
            info!("LDDR");
        },
        "LDI": ["10_100_000" (EDPrefix)] => {
            info!("LDI");
        },
        "LDIR": ["10_110_000" (EDPrefix)] => {
            info!("LDIR");
        },
        "LDUD": [
            "10_000_110" (EDPrefix), src: hl_indirect_sx(), dst: Register::A,
            "10_001_110" (EDPrefix), src: Register::A, dst: hl_indirect_sx(),
        ] => {
            info!("LDUD, src: {src:?}, dst: {dst:?}");
        },
        "LDUP": [
            "10_010_110" (EDPrefix), src: hl_indirect_sx(), dst: Register::A,
            "10_011_110" (EDPrefix), src: Register::A, dst: hl_indirect_sx(),
        ] => {
            info!("LDUP, src: {src:?}, dst: {dst:?}");
        },
        "MULT": [
            "11_***_000" (EDPrefix), src: src_dst(3..6),
            "11_111_000" (EDPrefix + IYOverride), src: imm8(),
        ] => {
            info!("MULT, src: {src:?}");
        },
        "MULTU": [
            "11_***_001" (EDPrefix), src: src_dst(3..6),
            "11_111_001" (EDPrefix + IYOverride), src: imm8(),
        ] => {
            info!("MULTU, src: {src:?}");
        },
        "MULTUW": ["11_**0_011" (EDPrefix), src: rr_expanded(4..6)] => {
            info!("MULTUW, src: {src:?}");
        },
        "MULTW": ["11_**0_010" (EDPrefix), src: rr_expanded(4..6)] => {
            info!("MULTW, src: {src:?}");
        },
        "NEG": [
            "01_000_100" (EDPrefix), register: Register::A,
            "01_001_100" (EDPrefix), register: Register::HL,
        ] => {
            info!("NEG, register: {register:?}");
        },
        "NOP": ["00_000_000"] => {
            info!("NOP");
        },
        "OR": ["10_110_***", src: src_dst(0..3)] => {
            info!("OR, src: {src:?}");
        },
        "OTDR": ["10_111_011" (EDPrefix)] => {
            info!("OTDR");
        },
        "OTDRW": ["10_011_011" (EDPrefix)] => {
            info!("OTDRW");
        },
        "OTIR": ["10_110_011" (EDPrefix)] => {
            info!("OTIR");
        },
        "OTIRW": ["10_010_011" (EDPrefix)] => {
            info!("OTIRW");
        },
        "OUT": [
            "01_***_001" (EDPrefix), src: r(3..6) | ix_iy_components(3..6) | extended_indirect_modes(3..6), dst: Register::C,
            "11_010_011", src: Register::A, dst: imm8(),
        ] => {
            info!("OUT, src: {src:?}, dst: {dst:?}");
        },
        "OUTD": ["10_101_011" (EDPrefix)] => {
            info!("OUTD");
        },
        "OUTDW": ["10_001_011" (EDPrefix)] => {
            info!("OUTDW");
        },
        "OUTI": ["10_100_011" (EDPrefix)] => {
            info!("OUTI");
        },
        "OUTIW": ["10_000_011" (EDPrefix)] => {
            info!("OUTIW");
        },
        "OUT HL": ["10_111_111" (EDPrefix)] => {
            info!("OUT HL");
        },
        "PCACHE": ["01_100_101" (EDPrefix)] => {
            info!("PCACHE");
        },
        "POP": ["11_**0_001", dst: rr(4..6) | rr_ix_expansion(4..6)] => {
            info!("POP, dst: {dst:?}");
        },
        "PUSH": [
            // R, IR, DA, RA
            "11_**0_101", src: rr(4..6) | rr_ix_expansion(4..6),
            // IM
            "11_110_101" (IYOverride), src: imm16(),
        ] => {
            info!("PUSH, src: {src:?}");
        },
        "RES": ["10_***_***" (CBPrefix), b: imm_unsigned(3..6), dst: r(0..3) | hl_indirection(0..3)] => {
            info!("RES, b: {b:?}, dst: {dst:?}");
        },
        "RET": [
            "11_***_000", cc: cc(3..6),
            "11_001_001", cc: ConditionCode::Always,
        ] => {
            info!("RET, cc: {cc:?}");
        },
        "RETI": ["01_001_101" (EDPrefix)] => {
            info!("RETI");
        },
        "RETIL": ["01_010_101" (EDPrefix)] => {
            info!("RETIL");
        },
        "RETN": ["01_000_101" (EDPrefix)] => {
            info!("RETN");
        },
        "RL": [
            "00_010_***" (CBPrefix), dst: r(3..6) | hl_indirection(3..6),
            "00_010_111", dst: Register::A,
        ] => {
            info!("RL, dst: {dst:?}");
        },
        "RLC": [
            "00_000_***" (CBPrefix), dst: r(3..6) | hl_indirection(3..6),
            "00_000_111", dst: Register::A,
        ] => {
            info!("RLC, dst: {dst:?}");
        },
        "RLD": ["01_101_111" (EDPrefix)] => {
            info!("RLD");
        },
        "RR": [
            "00_011_***" (CBPrefix), dst: r(3..6) | hl_indirection(3..6),
            "00_011_111", dst: Register::A,
        ] => {
            info!("RR, dst: {dst:?}");
        },
        "RRC": [
            "00_001_***" (CBPrefix), dst: r(3..6) | hl_indirection(3..6),
            "00_001_111", dst: Register::A,
        ] => {
            info!("RRC, dst: {dst:?}");
        },
        "RRD": ["01_100_111" (EDPrefix)] => {
            info!("RRD");
        },
        "RST": ["11_***_111", t: imm_unsigned(3..6)] => {
            info!("RST, t: {t:?}");
        },
        "SBC (byte form)": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_011_***", src: src_dst(0..3),
            // IM
            "11_011_110", src: imm8(),
        ] => {
            info!("SBC (byte form), src: {src:?}");
        },
        "SBC (word form)": ["01_**0_010" (EDPrefix), src: rr(4..6), dst: hl()] => {
            info!("SBC (word form), src: {src:?}, dst: {dst:?}");
        },
        "SC": ["01_110_001" (EDPrefix), nn: imm16()] => {
            info!("SC, nn: {nn:?}");
        },
        "SCF": ["0_110_111"] => {
            info!("SCF");
        },
        "SET": ["11_***_***" (CBPrefix), b: imm_unsigned(3..6), dst: r(0..3) | hl_indirection(0..3)] => {
            info!("SET, b: {b:?}, dst: {dst:?}");
        },
        "SLA": ["00_100_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => {
            info!("SLA, dst: {dst:?}");
        },
        "SRA": ["00_101_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => {
            info!("SRA, dst: {dst:?}");
        },
        "SRL": ["00_111_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => {
            info!("SRL, dst: {dst:?}");
        },
        "SUB": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_010_***", src: src_dst(0..3),
            // IM
            "11_010_110", src: imm8(),
        ] => {
            info!("SUB, src: {src:?}");
        },
        "SUBW": ["11_**1_110" (EDPrefix), src: rr_expanded(4..6)] => {
            info!("SUBW, src: {src:?}");
        },
        "TSET": ["00_110_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => {
            info!("TSET, dst: {dst:?}");
        },
        "TSTI": ["01_110_000" (EDPrefix)] => {
            info!("TSTI");
        },
        "XOR": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_101_***", src: src_dst(0..3),
            // IM
            "11_101_110", src: imm8(),
        ] => {
            info!("XOR, src: {src:?}");
        },
        // TODO: EPU instructions
    },
    invalid_instruction_handler: {
        warn!("invalid instruction {opcode:#x} with prefixes {prefixes:?}");
    },
}
