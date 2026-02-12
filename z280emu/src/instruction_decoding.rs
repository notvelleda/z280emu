use crate::BusAccessor;
use instruction_decoder::decode_instructions;
use log::warn;

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
    AF,
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
            Self::H => (cpu_state.register_file.current_x_bank().hl >> 8) as u8,
            Self::L => (cpu_state.register_file.current_x_bank().hl & 0xff) as u8,
            Self::I => cpu_state.register_file.i,
            Self::R => cpu_state.register_file.r,
            Self::IXH => (cpu_state.register_file.ix >> 8) as u8,
            Self::IXL => (cpu_state.register_file.ix & 0xff) as u8,
            Self::IYH => (cpu_state.register_file.iy >> 8) as u8,
            Self::IYL => (cpu_state.register_file.iy & 0xff) as u8,
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
            Self::AF => {
                let partial_file = cpu_state.register_file.current_af_bank();
                ((partial_file.a as u16) << 8) | (partial_file.f.into_bits() as u16)
            }
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
            Self::AF => {
                let partial_file = cpu_state.register_file.current_af_bank_mut();
                partial_file.a = (value >> 8) as u8;
                partial_file.f.set_bits((value & 0xff) as u8);
                // TODO: how should unused bits be set here?
            }
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
    pub address: u16,
}

impl RegisterOrMemoryAccessor<u8> for Memory {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> u8 {
        let mut result = [0];

        cpu_state.bus_accessor.read(crate::BusAddressSpace::Memory, u32::from(self.address), &mut result);

        result[0]
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: u8) {
        cpu_state.bus_accessor.write(crate::BusAddressSpace::Memory, u32::from(self.address), &[value]);
    }
}

impl RegisterOrMemoryAccessor<u16> for Memory {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> u16 {
        let mut result = [0; 2];

        cpu_state.bus_accessor.read(crate::BusAddressSpace::Memory, u32::from(self.address), &mut result);

        u16::from_le_bytes(result)
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: u16) {
        cpu_state.bus_accessor.write(crate::BusAddressSpace::Memory, u32::from(self.address), &value.to_le_bytes());
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Immediate {
    Byte(u8),
    Word(u16),
    UnknownSigned(isize),
    UnknownUnsigned(usize),
}

impl Immediate {
    pub const fn is_zero(&self) -> bool {
        match self {
            Self::Byte(value) => *value == 0,
            Self::Word(value) => *value == 0,
            Self::UnknownSigned(value) => *value == 0,
            Self::UnknownUnsigned(value) => *value == 0,
        }
    }

    pub const fn is_non_zero(&self) -> bool {
        match self {
            Self::Byte(value) => *value != 0,
            Self::Word(value) => *value != 0,
            Self::UnknownSigned(value) => *value != 0,
            Self::UnknownUnsigned(value) => *value != 0,
        }
    }
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
        address: lhs.get(cpu_state).wrapping_add_signed(rhs.get(cpu_state)),
    }
}

fn direct<T: BusAccessor>(cpu_state: &mut super::CPUState<T>, lhs: impl RegisterOrMemoryAccessor<u16>, rhs: impl RegisterOrMemoryAccessor<i16>) -> Immediate {
    Immediate::Word(lhs.get(cpu_state).wrapping_add_signed(rhs.get(cpu_state)))
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
    PO,
    /// PE/V
    PE,
    /// P/NS
    P,
    /// M/S
    M,
    /// Unconditional
    Always,
}

impl ConditionCode {
    const fn is_condition_met<T: BusAccessor>(&self, cpu_state: &super::CPUState<T>) -> bool {
        if matches!(self, Self::Always) {
            return true;
        }

        let flags = cpu_state.register_file.current_af_bank().f;

        match self {
            Self::NZ => !flags.zero(),
            Self::Z => flags.zero(),
            Self::NC => !flags.carry(),
            Self::C => flags.carry(),
            Self::PO => !flags.parity_overflow(),
            Self::PE => flags.parity_overflow(),
            Self::P => !flags.sign(),
            Self::M => flags.sign(),
            _ => unreachable!(),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum InterruptMode {
    Mode0,
    Mode1,
    Mode2,
    Mode3,
}

macro_rules! set_sign_bit {
    (u8, $flags:ident, $value:expr) => {
        $flags.set_sign((($value) & 0x80) != 0);
    };
    (u16, $flags:ident, $value:expr) => {
        $flags.set_sign((($value) & 0x8000) != 0);
    };
}

macro_rules! set_half_carry {
    (u8, $flags:ident, $dst_value:expr, $src_value:expr) => {
        $flags.set_half_carry(super::calculate_half_carry_u8($dst_value, $src_value));
    };
    (u16, $flags:ident, $dst_value:expr, $src_value:expr) => {
        $flags.set_half_carry(super::calculate_half_carry_u16($dst_value, $src_value));
    };
    (u8, $flags:ident, $dst_value:expr, negate $src_value:expr) => {
        $flags.set_half_carry(super::calculate_half_carry_u8($dst_value, (-($src_value as i8)) as u8));
    };
    (u16, $flags:ident, $dst_value:expr, negate $src_value:expr) => {
        $flags.set_half_carry(super::calculate_half_carry_u16($dst_value, (-($src_value as i16)) as u16));
    };
}

macro_rules! impl_add {
    ($type:tt, $cpu_state:expr, $dst:expr, $src:expr, $respect_carry_bit:expr, $set_additional_flags:expr) => {
        let dst_value: $type = $dst.get($cpu_state);
        let src_value: $type = $src.get($cpu_state);
        let flags = &mut $cpu_state.register_file.current_af_bank_mut().f;

        let (result, carry) = dst_value.carrying_add(src_value, $respect_carry_bit && flags.carry());

        if $set_additional_flags {
            let result_checked = if $respect_carry_bit {
                dst_value.checked_add(src_value).and_then(|result| result.checked_add(if flags.carry() { 1 } else { 0 }))
            } else {
                dst_value.checked_add(src_value)
            };

            set_sign_bit!($type, flags, result);
            flags.set_zero(result == 0);
            flags.set_parity_overflow(result_checked.is_none());
        }

        set_half_carry!($type, flags, dst_value, src_value);
        flags.set_add_subtract(false);
        flags.set_carry(carry);

        $dst.set($cpu_state, result);
    };
}

macro_rules! impl_sub {
    ($type:tt, $cpu_state:expr, $dst:expr, $src:expr, $respect_carry_bit:expr) => {
        let dst_value: $type = $dst.get($cpu_state);
        let src_value: $type = $src.get($cpu_state);
        let flags = &mut $cpu_state.register_file.current_af_bank_mut().f;

        let result_checked = if $respect_carry_bit {
            dst_value.checked_sub(src_value).and_then(|result| result.checked_sub(if flags.carry() { 1 } else { 0 }))
        } else {
            dst_value.checked_sub(src_value)
        };
        let (result, carry) = dst_value.borrowing_sub(src_value, $respect_carry_bit && flags.carry());

        set_sign_bit!($type, flags, result);
        flags.set_zero(result == 0);
        set_half_carry!($type, flags, dst_value, negate src_value);
        flags.set_parity_overflow(result_checked.is_none());
        flags.set_add_subtract(true);
        flags.set_carry(carry);

        $dst.set($cpu_state, result);
    };
}

decode_instructions! {
    instruction_word_size: 1,
    trace_instructions: true,
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
        extended_indirect_no_da: {
            IXOverride => {
                0b000 => indirect(Register::SP + imm16()),
                0b001 => indirect(Register::HL + Register::IX),
                0b010 => indirect(Register::HL + Register::IY),
                0b011 => indirect(Register::IX + Register::IY),
            },
            IYOverride => {
                0b000 => indirect(Register::PC + imm16()),
                0b001 => indirect(Register::IX + imm16()),
                0b010 => indirect(Register::IY + imm16()),
                0b011 => indirect(Register::HL + imm16()),
            },
        },
        extended_indirect_da: {
            0b111 => indirect(imm16()),
        },
        extended_indirect_modes: {
            extended_indirect_no_da() | extended_indirect_da()
        },
        // R, RX, IR, DA, X, SX, RA, SR, BX
        src_dst: {
            r() | ix_iy_components() | hl_indirection() | extended_indirect_modes(),
        },
        rr: {
            0b00 => Register::BC,
            0b01 => Register::DE,
            0b10 => Register::HL,
            0b11 => Register::SP,
        },
        rr_xy_overrides: {
            IXOverride => {
                0b10 => Register::IX,
            },
            IYOverride => {
                0b10 => Register::IY,
            },
        },
        rr_stack_ops: {
            0b00 => Register::BC,
            0b01 => Register::DE,
            IXOverride => {
                0b10 => Register::IX,
            },
            IYOverride => {
                0b10 => Register::IY,
            },
            0b10 => Register::HL,
            0b11 => Register::AF,
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
            rr() | rr_xy_overrides() | rr_ix_expansion() | rr_iy_expansion()
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
            0b100 => ConditionCode::PO,
            0b101 => ConditionCode::PE,
            0b110 => ConditionCode::P,
            0b111 => ConditionCode::M,
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
            indirect(imm16()),
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
        t_encoding: {
            0b000 => const(0x00),
            0b001 => const(0x08),
            0b010 => const(0x10),
            0b011 => const(0x18),
            0b100 => const(0x20),
            0b101 => const(0x28),
            0b110 => const(0x30),
            0b111 => const(0x38),
        },
    },
    instructions: {
        "ADD/ADC (byte form)": [
            // ADC
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_001_***", src: src_dst(0..3), use_carry: const(1),
            // IM
            "11_001_110", src: imm8(), use_carry: const(1),

            // ADD
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_000_***", src: src_dst(0..3), use_carry: const(0),
            // IM
            "11_000_110", src: imm8(), use_carry: const(0),
        ] => {
            impl_add!(u8, cpu_state, Register::A, src, use_carry.is_non_zero(), true);
        },
        "ADD/ADC (word form)": [
            // ADC
            "01_**1_010" (EDPrefix), src: rr(4..6) | rr_xy_overrides(4..6), dst: hl(), use_carry: const(1), set_flags: const(1),
            // ADD
            "00_**1_001", src: rr(4..6) | rr_xy_overrides(4..6), dst: hl(), use_carry: const(0), set_flags: const(0),
            // ADDW
            "11_**0_110" (EDPrefix), src: rr_expanded(4..6), dst: Register::HL, use_carry: const(0), set_flags: const(1),
        ] => {
            impl_add!(u16, cpu_state, dst, src, use_carry.is_non_zero(), set_flags.is_non_zero());
        },
        "ADD": ["01_101_101" (EDPrefix), dst: hl(), src: Register::A] => {
            let dst_value: u16 = dst.get(cpu_state);
            let src: u8 = src.get(cpu_state);
            let src = src as i8 as i16 as u16;
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            let result_checked = dst_value.checked_add(src);
            let (result, carry) = dst_value.carrying_add(src, false);

            flags.set_sign((result & 0x8000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(super::calculate_half_carry_u16(dst_value, src));
            flags.set_parity_overflow(result_checked.is_none());
            flags.set_add_subtract(false);
            flags.set_carry(carry);

            dst.set(cpu_state, result);
        },
        "AND": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_100_***", src: src_dst(0..3),
            // IM
            "11_100_110", src: imm8(),
        ] => {
            let a: u8 = Register::A.get(cpu_state);
            let src: u8 = src.get(cpu_state);
            let result = a & src;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(true);
            flags.set_parity_overflow(super::calculate_parity(u16::from(result)));
            flags.set_add_subtract(false);
            flags.set_carry(false);

            Register::A.set(cpu_state, result);
        },
        "BIT": ["01_***_***" (CBPrefix), b: imm_unsigned(3..6), r: r(0..3) | hl_indirection(0..3)] => unimplemented,
        "CALL": [
            // conditional call
            "11_***_100", cc: cc(3..6), target: call_addr(),
            // unconditional call
            "11_001_101", cc: ConditionCode::Always, target: call_addr(),
        ] => {
            if cc.is_condition_met(cpu_state) {
                let pc = Register::PC.get(cpu_state);
                super::push(cpu_state, pc);
                Register::PC.set(cpu_state, target.address);
            }
        },
        "CCF": ["00_111_111"] => unimplemented,
        "CP": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_111_***", src: src_dst(0..3),
            // IM
            "11_111_110", src: imm8(),
        ] => {
            let a: u8 = Register::A.get(cpu_state);
            let src: u8 = src.get(cpu_state);
            let result_checked = a.checked_sub(src);
            let (result, borrow) = a.borrowing_sub(src, false);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(super::calculate_half_carry_u8(a, (-(src as i8)) as u8));
            flags.set_parity_overflow(result_checked.is_none());
            flags.set_add_subtract(true);
            flags.set_carry(borrow);
        },
        "CPD": ["10_101_001" (EDPrefix)] => unimplemented,
        "CPDR": ["10_111_001" (EDPrefix)] => unimplemented,
        "CPI": ["10_100_001" (EDPrefix)] => unimplemented,
        "CPIR": ["10_110_001" (EDPrefix)] => unimplemented,
        "CPL": ["00_101_111"] => unimplemented,
        "CPW": ["11_**0_111" (EDPrefix), src: rr_expanded(4..6)] => unimplemented,
        "DAA": ["00_100_111"] => {
            let a_value: u8 = Register::A.get(cpu_state);
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            let mut correction_factor = 0;

            // https://worldofspectrum.org/faq/reference/z80reference.htm#DAA

            if a_value & 0x0f > 9 || flags.half_carry() {
                correction_factor |= 0x06;
            }

            if a_value > 0x99 || flags.carry() {
                correction_factor |= 0x60;
                flags.set_carry(true);
            }

            if flags.add_subtract() {
                correction_factor = (-(correction_factor as i8)) as u8;
            }

            let result = a_value.wrapping_add(correction_factor);

            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(super::calculate_half_carry_u8(a_value, correction_factor));
            flags.set_parity_overflow(super::calculate_parity(u16::from(result)));

            Register::A.set(cpu_state, result);
        },
        "DEC (byte form)": ["00_***_101", dst: src_dst(3..6)] => {
            let value: u8 = dst.get(cpu_state);
            let result = value.checked_sub(1);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result.unwrap_or_default() & 0b1000_0000) != 0);
            flags.set_zero(result.unwrap_or_default() == 0);
            flags.set_half_carry(super::calculate_half_carry_u8(value, -1_i8 as u8));
            flags.set_parity_overflow(result.is_none());
            flags.set_add_subtract(true);

            dst.set(cpu_state, result.unwrap_or_default());
        },
        "DEC (word form)": ["00_**1_011", dst: rr_expanded(4..6)] => {
            let value: u16 = dst.get(cpu_state);
            dst.set(cpu_state, value.wrapping_sub(1));
        },
        "DI": [
            "11_110_011", mask: const(0x7f),
            "01_110_111" (EDPrefix), mask: imm8(),
        ] => unimplemented,
        "DIV": [
            "11_***_100" (EDPrefix), src: src_dst(3..6),
            "11_111_100" (EDPrefix + IYOverride), src: imm8(),
        ] => unimplemented,
        "DIVU": [
            "11_***_101" (EDPrefix), src: src_dst(3..6),
            "11_111_101" (EDPrefix + IYOverride), src: imm8(),
        ] => unimplemented,
        "DIVUW": ["11_**1_011" (EDPrefix), src: rr_expanded(4..6)] => unimplemented,
        "DIVW": ["11_**1_010" (EDPrefix), src: rr_expanded(4..6)] => unimplemented,
        "DJNZ": ["00_010_000", addr: indirect(Register::PC + imm8())] => {
            let value: u8 = Register::B.get(cpu_state);
            let result = value.wrapping_sub(1);

            Register::B.set(cpu_state, result);

            if result != 0 {
                Register::PC.set(cpu_state, addr.address);
            }
        },
        "EI": [
            "11_111_011", mask: const(0x7f),
            "01_111_111" (EDPrefix), mask: imm8(),
        ] => unimplemented,
        "EX AF, AF'": ["00_001_000"] => unimplemented,
        "EX (SP)": ["11_100_011", dst: hl()] => unimplemented,
        "EX H, L": ["11_101_111" (EDPrefix)] => unimplemented,
        "EX HL": [
            "11_101_011", src: Register::DE,
            "11_101_011" (IXOverride), src: Register::IX,
            "11_101_011" (IYOverride), src: Register::IY,
        ] => unimplemented,
        "EX A": ["00_***_111" (EDPrefix), src: src_dst(3..6)] => unimplemented,
        "EXTS (byte form)": ["10_100_100" (EDPrefix)] => unimplemented,
        "EXTS (word form)": ["10_101_100" (EDPrefix)] => unimplemented,
        "EXX": ["11_011_001"] => unimplemented,
        "HALT": ["01_110_110"] => {
            // TODO: handle this properly, this isn't even remotely correct
            std::process::exit(0);
        },
        "IM": [
            "01_000_110" (EDPrefix), p: InterruptMode::Mode0,
            "01_010_110" (EDPrefix), p: InterruptMode::Mode1,
            "01_011_110" (EDPrefix), p: InterruptMode::Mode2,
            "01_001_110" (EDPrefix), p: InterruptMode::Mode3,
        ] => unimplemented,
        "IN": [
            "01_***_000" (EDPrefix), src: Register::C, dst: r(3..6) | ix_iy_components(3..6) | extended_indirect_modes(3..6), addr_middle_byte: Register::B,
            "11_011_011", src: imm8(), dst: Register::A, addr_middle_byte: Register::A,
        ] => {
            let addr: u8 = src.get(cpu_state);
            let full_addr = super::calculate_io_address(cpu_state, addr, addr_middle_byte);
            let mut data = [0];

            cpu_state.bus_accessor.read(crate::BusAddressSpace::IO, full_addr, &mut data);

            dst.set(cpu_state, data[0]);
        },
        "INC (byte form)": ["00_***_100", dst: src_dst(3..6)] => {
            let value: u8 = dst.get(cpu_state);
            let result = value.checked_add(1);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result.unwrap_or_default() & 0b1000_0000) != 0);
            flags.set_zero(result.unwrap_or_default() == 0);
            flags.set_half_carry(super::calculate_half_carry_u8(value, 1));
            flags.set_parity_overflow(result.is_none());
            flags.set_add_subtract(false);

            dst.set(cpu_state, result.unwrap_or_default());
        },
        "INC (word form)": ["00_**0_011", dst: rr_expanded(4..6)] => {
            let value: u16 = dst.get(cpu_state);
            dst.set(cpu_state, value.wrapping_add(1));
        },
        "IND": ["10_101_010" (EDPrefix)] => unimplemented,
        "INDW": ["10_001_010" (EDPrefix)] => unimplemented,
        "INDR": ["10_111_010" (EDPrefix)] => unimplemented,
        "INDRW": ["10_011_010" (EDPrefix)] => unimplemented,
        "INI": ["10_100_010" (EDPrefix)] => unimplemented,
        "INIW": ["10_000_010" (EDPrefix)] => unimplemented,
        "INIR": ["10_110_010" (EDPrefix)] => unimplemented,
        "INIRW": ["10_010_010" (EDPrefix)] => unimplemented,
        "IN HL": ["10_110_111" (EDPrefix)] => unimplemented,
        "JAF": ["00_101_000" (IXOverride), addr: indirect(Register::PC + imm8())] => unimplemented,
        "JAR": ["00_100_000" (IXOverride), addr: indirect(Register::PC + imm8())] => unimplemented,
        "JP": [
            // JP
            "11_***_010" (IXOverride), cc: cc(3..6), dst: Register::HL,
            "11_101_001", cc: ConditionCode::Always, dst: hl(),
            "11_***_010", cc: cc(3..6), dst: imm16(),
            "11_000_011", cc: ConditionCode::Always, dst: imm16(),
            "11_***_010" (IYOverride), cc: cc(3..6), dst: direct(Register::PC + imm16()),
            "11_000_011" (IYOverride), cc: ConditionCode::Always, dst: direct(Register::PC + imm16()),

            // JR
            "00_***_000", cc: cc_simplified(3..6), dst: direct(Register::PC + imm8())
        ] => {
            let target: u16 = dst.get(cpu_state);

            if cc.is_condition_met(cpu_state) {
                Register::PC.set(cpu_state, target);
            }
        },
        "LD (byte)": [
            // LD A, *

            // R is a duplicate of LD register (byte)
            // RX, IR, X, SX, RA, SR, BX
            "01_111_***", src: ix_iy_components(0..3) | hl_indirect_overrides(0..3) | extended_indirect_no_da(0..3), dst: Register::A,
            // IM is a duplicate of LD immediate (byte)
            // IR
            "00_001_010", src: indirect(Register::BC), dst: Register::A,
            "00_011_010", src: indirect(Register::DE), dst: Register::A,
            // DA
            "00_111_010", src: indirect(imm16()), dst: Register::A,

            // LD *, A

            // R is a duplicate of LD register (byte)
            // R, RX, IR, X, SX, RA, SR, BX
            "01_***_111", src: Register::A, dst: ix_iy_components(3..6) | hl_indirect_overrides(3..6) | extended_indirect_no_da(3..6),
            // IR
            "00_000_010", src: Register::A, dst: indirect(Register::BC),
            "00_010_010", src: Register::A, dst: indirect(Register::DE),
            // DA
            "00_110_010", src: Register::A, dst: indirect(imm16()),

            // LD immediate (byte)
            "00_***_110", dst: src_dst(3..6), src: imm8(),

            // LD register (byte)

            // R, RX, IR, SX
            "01_***_***", src: r(0..3) | hl_indirection(0..3) | ix_iy_components(0..3), dst: r(3..6) | hl_indirection(3..6) | ix_iy_components(3..6),
            // IM is a duplicate of LD immediate (byte)
        ] => {
            let value: u8 = src.get(cpu_state);
            dst.set(cpu_state, value);
        },
        [
            // LDW
            "00_**0_001", dst: rr_xy_overrides(4..6) | rr_ix_expansion(4..6), src: imm16(),

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
            "00_**0_001", src: imm16(), dst: rr(4..6),
            // IR, SX
            "00_**0_110" (EDPrefix), src: hl_indirect_sx(), dst: rr(4..6),
            "00_**1_110" (EDPrefix), src: rr(4..6), dst: hl_indirect_sx(),
            // DA
            "01_**1_011" (EDPrefix), src: indirect(imm16()), dst: rr(4..6),
            "01_**0_011" (EDPrefix), src: rr(4..6), dst: indirect(imm16()),

            // LD[W] (stack pointer)

            // R
            "11_111_001", src: hl(), dst: Register::SP,
            // IM, IR, SX, DA is a duplicate of LD[W] (word)
        ] => {
            let value: u16 = src.get(cpu_state);
            dst.set(cpu_state, value);
        },
        "LD from/to I, R": [
            // LD A, I
            "01_010_111" (EDPrefix), src: Register::I, dst: Register::A,
            // LD A, R
            "01_011_111" (EDPrefix), src: Register::R, dst: Register::A,

            // LD I, A
            "01_000_111" (EDPrefix), src: Register::A, dst: Register::I,
            // LD R, A
            "01_001_111" (EDPrefix), src: Register::A, dst: Register::R,
        ] => unimplemented,
        "LDA": [
            // DA is a duplicate of LDW
            // X, RA, SR, BX
            "00_***_010" (EDPrefix), src: lda_extended(3..6), dst: hl(),
        ] => {
            dst.set(cpu_state, src.address);
        },
        "LDCTL": [
            "01_100_110" (EDPrefix), src: Register::C, dst: hl(),
            "01_101_110" (EDPrefix), src: hl(), dst: Register::C,
            "10_000_111" (EDPrefix), src: Register::USP, dst: hl(),
            "10_001_111" (EDPrefix), src: hl(), dst: Register::USP,
        ] => unimplemented,
        "LDD": ["10_101_000" (EDPrefix)] => unimplemented,
        "LDDR": ["10_111_000" (EDPrefix)] => unimplemented,
        "LDI": ["10_100_000" (EDPrefix)] => unimplemented,
        "LDIR": ["10_110_000" (EDPrefix)] => unimplemented,
        "LDUD": [
            "10_000_110" (EDPrefix), src: hl_indirect_sx(), dst: Register::A,
            "10_001_110" (EDPrefix), src: Register::A, dst: hl_indirect_sx(),
        ] => unimplemented,
        "LDUP": [
            "10_010_110" (EDPrefix), src: hl_indirect_sx(), dst: Register::A,
            "10_011_110" (EDPrefix), src: Register::A, dst: hl_indirect_sx(),
        ] => unimplemented,
        "MULT": [
            "11_***_000" (EDPrefix), src: src_dst(3..6),
            "11_111_000" (EDPrefix + IYOverride), src: imm8(),
        ] => unimplemented,
        "MULTU": [
            "11_***_001" (EDPrefix), src: src_dst(3..6),
            "11_111_001" (EDPrefix + IYOverride), src: imm8(),
        ] => unimplemented,
        "MULTUW": ["11_**0_011" (EDPrefix), src: rr_expanded(4..6)] => unimplemented,
        "MULTW": ["11_**0_010" (EDPrefix), src: rr_expanded(4..6)] => unimplemented,
        "NEG": [
            "01_000_100" (EDPrefix), register: Register::A,
            "01_001_100" (EDPrefix), register: Register::HL,
        ] => unimplemented,
        "NOP": ["00_000_000"] => {},
        "OR": ["10_110_***", src: src_dst(0..3)] => {
            let a: u8 = Register::A.get(cpu_state);
            let src: u8 = src.get(cpu_state);
            let result = a | src;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(super::calculate_parity(u16::from(result)));
            flags.set_add_subtract(false);
            flags.set_carry(false);

            Register::A.set(cpu_state, result);
        },
        "OTDR": ["10_111_011" (EDPrefix)] => unimplemented,
        "OTDRW": ["10_011_011" (EDPrefix)] => unimplemented,
        "OTIR": ["10_110_011" (EDPrefix)] => unimplemented,
        "OTIRW": ["10_010_011" (EDPrefix)] => unimplemented,
        "OUT": [
            "01_***_001" (EDPrefix), src: r(3..6) | ix_iy_components(3..6) | extended_indirect_modes(3..6), dst: Register::C, addr_middle_byte: Register::B,
            "11_010_011", src: Register::A, dst: imm8(), addr_middle_byte: Register::A,
        ] => {
            let addr: u8 = dst.get(cpu_state);
            let value: u8 = src.get(cpu_state);
            let full_addr = super::calculate_io_address(cpu_state, addr, addr_middle_byte);

            cpu_state.bus_accessor.write(crate::BusAddressSpace::IO, full_addr, &[value]);
        },
        "OUTD": ["10_101_011" (EDPrefix)] => unimplemented,
        "OUTDW": ["10_001_011" (EDPrefix)] => unimplemented,
        "OUTI": ["10_100_011" (EDPrefix)] => unimplemented,
        "OUTIW": ["10_000_011" (EDPrefix)] => unimplemented,
        "OUT HL": ["10_111_111" (EDPrefix)] => unimplemented,
        "PCACHE": ["01_100_101" (EDPrefix)] => unimplemented,
        "POP": ["11_**0_001", dst: rr_stack_ops(4..6) | rr_ix_expansion(4..6)] => {
            let value = super::pop(cpu_state);
            dst.set(cpu_state, value);
        },
        "PUSH": [
            // R, IR, DA, RA
            "11_**0_101", src: rr_stack_ops(4..6) | rr_ix_expansion(4..6),
            // IM
            "11_110_101" (IYOverride), src: imm16(),
        ] => {
            let value = src.get(cpu_state);
            super::push(cpu_state, value);
        },
        "RES": ["10_***_***" (CBPrefix), b: imm_unsigned(3..6), dst: r(0..3) | hl_indirection(0..3)] => unimplemented,
        "RET": [
            "11_***_000", cc: cc(3..6),
            "11_001_001", cc: ConditionCode::Always,
        ] => {
            if cc.is_condition_met(cpu_state) {
                let new_pc = super::pop(cpu_state);
                Register::PC.set(cpu_state, new_pc);
            }
        },
        "RETI": ["01_001_101" (EDPrefix)] => unimplemented,
        "RETIL": ["01_010_101" (EDPrefix)] => unimplemented,
        "RETN": ["01_000_101" (EDPrefix)] => unimplemented,
        "RL": [
            "00_010_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3), set_flags: const(1),
            "00_010_111", dst: Register::A, set_flags: const(0),
        ] => {
            let dst_value: u8 = dst.get(cpu_state);
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            let result = (dst_value << 1) | if flags.carry() { 1 } else { 0 };

            if set_flags.is_non_zero() {
                flags.set_sign((result & 0b1000_0000) != 0);
                flags.set_zero(result == 0);
                flags.set_parity_overflow(super::calculate_parity(u16::from(result)));
            }

            flags.set_half_carry(false);
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 0x80 != 0);

            dst.set(cpu_state, result);
        },
        "RLC": [
            "00_000_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3), set_flags: const(1),
            "00_000_111", dst: Register::A, set_flags: const(0),
        ] => {
            let dst_value: u8 = dst.get(cpu_state);
            let result = (dst_value << 1) | ((dst_value & 0x80) >> 7);

            dst.set(cpu_state, result);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            if set_flags.is_non_zero() {
                flags.set_sign((result & 0b1000_0000) != 0);
                flags.set_zero(result == 0);
                flags.set_parity_overflow(super::calculate_parity(u16::from(result)));
            }

            flags.set_half_carry(false);
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 0x80 != 0);
        },
        "RLD": ["01_101_111" (EDPrefix)] => unimplemented,
        "RR": [
            "00_011_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3), set_flags: const(1),
            "00_011_111", dst: Register::A, set_flags: const(0),
        ] => {
            let dst_value: u8 = dst.get(cpu_state);
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            let result = (dst_value >> 1) | if flags.carry() { 0x80 } else { 0 };

            if set_flags.is_non_zero() {
                flags.set_sign((result & 0b1000_0000) != 0);
                flags.set_zero(result == 0);
                flags.set_parity_overflow(super::calculate_parity(u16::from(result)));
            }

            flags.set_half_carry(false);
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 1 != 0);

            dst.set(cpu_state, result);
        },
        "RRC": [
            "00_001_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3), set_flags: const(1),
            "00_001_111", dst: Register::A, set_flags: const(0),
        ] => {
            let dst_value: u8 = dst.get(cpu_state);
            let result = (dst_value >> 1) | ((dst_value & 1) << 7);

            dst.set(cpu_state, result);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            if set_flags.is_non_zero() {
                flags.set_sign((result & 0b1000_0000) != 0);
                flags.set_zero(result == 0);
                flags.set_parity_overflow(super::calculate_parity(u16::from(result)));
            }

            flags.set_half_carry(false);
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 1 != 0);
        },
        "RRD": ["01_100_111" (EDPrefix)] => unimplemented,
        "RST": ["11_***_111", addr: t_encoding(3..6)] => unimplemented,
        "SUB/SBC (byte form)": [
            // SBC
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_011_***", src: src_dst(0..3), use_carry: const(1),
            // IM
            "11_011_110", src: imm8(), use_carry: const(1),

            // SUB
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_010_***", src: src_dst(0..3), use_carry: const(0),
            // IM
            "11_010_110", src: imm8(), use_carry: const(0),
        ] => {
            impl_sub!(u8, cpu_state, Register::A, src, use_carry.is_non_zero());
        },
        "SBC (word form)/SUBW": [
            // SBC
            "01_**0_010" (EDPrefix), src: rr(4..6) | rr_xy_overrides(4..6), dst: hl(), use_carry: const(1),
            // SUBW
            "11_**1_110" (EDPrefix), src: rr_expanded(4..6), dst: Register::HL, use_carry: const(0),
        ] => {
            impl_sub!(u16, cpu_state, dst, src, use_carry.is_non_zero());
        },
        "SC": ["01_110_001" (EDPrefix), nn: imm16()] => unimplemented,
        "SCF": ["0_110_111"] => unimplemented,
        "SET": ["11_***_***" (CBPrefix), b: imm_unsigned(3..6), dst: r(0..3) | hl_indirection(0..3)] => unimplemented,
        "SLA": ["00_100_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => unimplemented,
        "SRA": ["00_101_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => unimplemented,
        "SRL": ["00_111_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => unimplemented,
        "TSET": ["00_110_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => unimplemented,
        "TSTI": ["01_110_000" (EDPrefix)] => unimplemented,
        "XOR": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_101_***", src: src_dst(0..3),
            // IM
            "11_101_110", src: imm8(),
        ] => {
            let a: u8 = Register::A.get(cpu_state);
            let src: u8 = src.get(cpu_state);
            let result = a ^ src;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(super::calculate_parity(u16::from(result)));
            flags.set_add_subtract(false);
            flags.set_carry(false);

            Register::A.set(cpu_state, result);
        },
        // TODO: EPU instructions
    },
    invalid_instruction_handler: {
        warn!("invalid instruction {opcode:#x} with prefixes {prefixes:?}");
    },
    unimplemented_instruction_handler: {
        warn!("unimplemented instruction {instruction_as_string}");
    },
}
