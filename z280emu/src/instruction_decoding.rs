use crate::{
    helpers::{
        ConditionCode, Immediate, Memory, Register, RegisterOrMemoryAccessor, Trap, calculate_half_carry_u8, calculate_half_carry_u16, calculate_io_address, calculate_parity, direct, indirect, pop,
        privileged_instruction_check, push, system_stack_overflow_check,
    },
    mmu::AccessType,
    registers::{InterruptMode, UserSystemBit},
};
use instruction_decoder::decode_instructions;
use log::warn;

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
        $flags.set_half_carry(calculate_half_carry_u8($dst_value, $src_value));
    };
    (u16, $flags:ident, $dst_value:expr, $src_value:expr) => {
        $flags.set_half_carry(calculate_half_carry_u16($dst_value, $src_value));
    };
    (u8, $flags:ident, $dst_value:expr, negate $src_value:expr) => {
        $flags.set_half_carry(calculate_half_carry_u8($dst_value, (-($src_value as i8)) as u8));
    };
    (u16, $flags:ident, $dst_value:expr, negate $src_value:expr) => {
        $flags.set_half_carry(calculate_half_carry_u16($dst_value, (-($src_value as i16)) as u16));
    };
}

macro_rules! impl_add {
    ($type:tt, $cpu_state:expr, $dst:expr, $src:expr, $respect_carry_bit:expr, $set_additional_flags:expr) => {
        let dst_value: $type = $dst.get($cpu_state)?;
        let src_value: $type = $src.get($cpu_state)?;
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

        $dst.set($cpu_state, result)?;
    };
}

macro_rules! impl_sub {
    ($type:tt, $cpu_state:expr, $dst:expr, $src:expr, $respect_carry_bit:expr) => {
        let dst_value: $type = $dst.get($cpu_state)?;
        let src_value: $type = $src.get($cpu_state)?;
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

        $dst.set($cpu_state, result)?;
    };
}

macro_rules! impl_div {
    ($type: tt, $cpu_state:expr, $lhs:expr, $rhs:expr, $result:expr, $remainder:expr) => {
        let flags = &mut $cpu_state.register_file.current_af_bank_mut().f;

        if $rhs == 0 {
            flags.set_sign(false);
            flags.set_zero(true);
            flags.set_parity_overflow(true);

            return Err(Trap::DivisionException);
        }

        let result = $type::try_from($lhs / $rhs);

        match result {
            Ok(result) => {
                #[allow(unused_comparisons)] // this just makes things easier
                flags.set_sign(result < 0);
                flags.set_zero(result == 0);
                flags.set_parity_overflow(false);

                $result.set($cpu_state, result)?;
                $remainder.set($cpu_state, ($lhs % $rhs) as $type)?;
            }
            Err(_) => {
                flags.set_sign(false);
                flags.set_zero(false);
                flags.set_parity_overflow(true);

                return Err(Trap::DivisionException);
            }
        }
    };
}

// TODO: make sure all instructions won't modify state if an invalid memory address is accessed (except for block move instructions to an extent)
decode_instructions! {
    instruction_word_size: 1,
    trace_instructions: true,
    return_type: { Result<(), Trap> },
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
            Ok(())
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
            Ok(())
        },
        "ADD": ["01_101_101" (EDPrefix), dst: hl(), src: Register::A] => {
            let dst_value: u16 = dst.get(cpu_state)?;
            let src: u8 = src.get(cpu_state)?;
            let src = src as i8 as i16 as u16;
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            let result_checked = dst_value.checked_add(src);
            let (result, carry) = dst_value.carrying_add(src, false);

            flags.set_sign((result & 0x8000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(calculate_half_carry_u16(dst_value, src));
            flags.set_parity_overflow(result_checked.is_none());
            flags.set_add_subtract(false);
            flags.set_carry(carry);

            dst.set(cpu_state, result)?;
            Ok(())
        },
        "AND": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_100_***", src: src_dst(0..3),
            // IM
            "11_100_110", src: imm8(),
        ] => {
            let a: u8 = Register::A.get(cpu_state)?;
            let src: u8 = src.get(cpu_state)?;
            let result = a & src;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(true);
            flags.set_parity_overflow(calculate_parity(u16::from(result)));
            flags.set_add_subtract(false);
            flags.set_carry(false);

            Register::A.set(cpu_state, result)?;
            Ok(())
        },
        "BIT": ["01_***_***" (CBPrefix), b: imm_unsigned(3..6), dst: r(0..3) | hl_indirection(0..3)] => {
            let b: u8 = b.get(cpu_state)?;
            let dst: u8 = dst.get(cpu_state)?;
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            flags.set_zero(dst & (1 << b) == 0);
            flags.set_half_carry(true);
            flags.set_add_subtract(false);

            Ok(())
        },
        "CALL": [
            // conditional call
            "11_***_100", cc: cc(3..6), target: call_addr(),
            // unconditional call
            "11_001_101", cc: ConditionCode::Always, target: call_addr(),
        ] => {
            if cc.is_condition_met(cpu_state) {
                let pc = Register::PC.get(cpu_state)?;
                push(cpu_state, pc)?;
                Register::PC.set(cpu_state, target.address)?;
                system_stack_overflow_check(cpu_state, false)
            } else {
                Ok(())
            }
        },
        "CCF": ["00_111_111"] => {
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_carry(!flags.carry());

            Ok(())
        },
        "CP": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_111_***", src: src_dst(0..3),
            // IM
            "11_111_110", src: imm8(),
        ] => {
            let a: u8 = Register::A.get(cpu_state)?;
            let src: u8 = src.get(cpu_state)?;
            let result_checked = a.checked_sub(src);
            let (result, borrow) = a.borrowing_sub(src, false);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(calculate_half_carry_u8(a, (-(src as i8)) as u8));
            flags.set_parity_overflow(result_checked.is_none());
            flags.set_add_subtract(true);
            flags.set_carry(borrow);

            Ok(())
        },
        "CPD/CPI": [
            "10_101_001" (EDPrefix), repeat: const(0), subtract: const(1),
            "10_111_001" (EDPrefix), repeat: const(1), subtract: const(1),
            "10_100_001" (EDPrefix), repeat: const(0), subtract: const(0),
            "10_110_001" (EDPrefix), repeat: const(1), subtract: const(0),
        ] => {
            let a: u8 = Register::A.get(cpu_state)?;

            let (result, half_carry, parity_overflow) = loop {
                let hl_value = Register::HL.get(cpu_state)?;
                let bc_value: u16 = Register::BC.get(cpu_state)?;
                let src: u8 =
                    Memory {
                        address: hl_value,
                        access_type: AccessType::Data,
                    }
                    .get(cpu_state)?;
                let result = a.wrapping_sub(src);

                Register::HL.set(cpu_state, if subtract.is_non_zero() { hl_value.wrapping_sub(1) } else { hl_value.wrapping_add(1) })?;
                Register::BC.set(cpu_state, bc_value.wrapping_sub(1))?;

                if repeat.is_zero() || result == 0 || bc_value == 1 {
                    break (result, calculate_half_carry_u8(a, (-(src as i8)) as u8), bc_value != 1);
                }
            };

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(half_carry);
            flags.set_parity_overflow(parity_overflow);
            flags.set_add_subtract(true);

            Ok(())
        },
        "CPL": ["00_101_111"] => {
            let a: u8 = Register::A.get(cpu_state)?;
            Register::A.set(cpu_state, !a)?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_half_carry(true);
            flags.set_add_subtract(true);

            Ok(())
        },
        "CPW": ["11_**0_111" (EDPrefix), src: rr_expanded(4..6)] => {
            let a: u16 = Register::HL.get(cpu_state)?;
            let src: u16 = src.get(cpu_state)?;
            let result_checked = a.checked_sub(src);
            let (result, borrow) = a.borrowing_sub(src, false);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0x8000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(calculate_half_carry_u16(a, (-(src as i16)) as u16));
            flags.set_parity_overflow(result_checked.is_none());
            flags.set_add_subtract(true);
            flags.set_carry(borrow);

            Ok(())
        },
        "DAA": ["00_100_111"] => {
            let a_value: u8 = Register::A.get(cpu_state)?;
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
            flags.set_half_carry(calculate_half_carry_u8(a_value, correction_factor));
            flags.set_parity_overflow(calculate_parity(u16::from(result)));

            Register::A.set(cpu_state, result)?;

            Ok(())
        },
        "DEC (byte form)": ["00_***_101", dst: src_dst(3..6)] => {
            let value: u8 = dst.get(cpu_state)?;
            let result = value.checked_sub(1);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result.unwrap_or_default() & 0b1000_0000) != 0);
            flags.set_zero(result.unwrap_or_default() == 0);
            flags.set_half_carry(calculate_half_carry_u8(value, -1_i8 as u8));
            flags.set_parity_overflow(result.is_none());
            flags.set_add_subtract(true);

            dst.set(cpu_state, result.unwrap_or_default())?;

            Ok(())
        },
        "DEC (word form)": ["00_**1_011", dst: rr_expanded(4..6)] => {
            let value: u16 = dst.get(cpu_state)?;
            dst.set(cpu_state, value.wrapping_sub(1))?;

            Ok(())
        },
        "DI": [
            "11_110_011", mask: const(0x7f),
            "01_110_111" (EDPrefix), mask: imm8(),
        ] => {
            privileged_instruction_check(cpu_state)?;

            let mask: u8 = mask.get(cpu_state)?;
            let msr = &mut cpu_state.system_status_registers.master_status;

            msr.set_irq_enable(msr.irq_enable() & (!mask & 0x7f));
            Ok(())
        },
        "DIV": [
            "11_***_100" (EDPrefix), src: src_dst(3..6),
            "11_111_100" (EDPrefix + IYOverride), src: imm8(),
        ] => {
            let lhs: i16 = Register::HL.get(cpu_state)?;
            let rhs: i16 = src.get(cpu_state)?;

            impl_div!(i8, cpu_state, lhs, rhs, Register::A, Register::L);
            Ok(())
        },
        "DIVU": [
            "11_***_101" (EDPrefix), src: src_dst(3..6),
            "11_111_101" (EDPrefix + IYOverride), src: imm8(),
        ] => {
            let lhs: u16 = Register::HL.get(cpu_state)?;
            let rhs: u16 = src.get(cpu_state)?;

            impl_div!(u8, cpu_state, lhs, rhs, Register::A, Register::L);
            Ok(())
        },
        "DIVUW": ["11_**1_011" (EDPrefix), src: rr_expanded(4..6)] => {
            let lhs_high: u16 = Register::DE.get(cpu_state)?;
            let lhs_low: u16 = Register::HL.get(cpu_state)?;
            let rhs: u16 = src.get(cpu_state)?;

            impl_div!(u16, cpu_state, (u32::from(lhs_high) << 16) | u32::from(lhs_low), u32::from(rhs), Register::HL, Register::DE);
            Ok(())
        },
        "DIVW": ["11_**1_010" (EDPrefix), src: rr_expanded(4..6)] => {
            let lhs_high: i16 = Register::DE.get(cpu_state)?;
            let lhs_low: i16 = Register::HL.get(cpu_state)?;
            let rhs: i16 = src.get(cpu_state)?;

            impl_div!(i16, cpu_state, (i32::from(lhs_high) << 16) | i32::from(lhs_low), i32::from(rhs), Register::HL, Register::DE);
            Ok(())
        },
        "DJNZ": ["00_010_000", addr: indirect(Register::PC + imm8())] => {
            let value: u8 = Register::B.get(cpu_state)?;
            let result = value.wrapping_sub(1);

            Register::B.set(cpu_state, result)?;

            if result != 0 {
                Register::PC.set(cpu_state, addr.address)?;
            }

            Ok(())
        },
        "EI": [
            "11_111_011", mask: const(0x7f),
            "01_111_111" (EDPrefix), mask: imm8(),
        ] => {
            privileged_instruction_check(cpu_state)?;

            let mask: u8 = mask.get(cpu_state)?;
            let msr = &mut cpu_state.system_status_registers.master_status;

            msr.set_irq_enable(msr.irq_enable() | (mask & 0x7f));
            Ok(())
        },
        "EX AF, AF'": ["00_001_000"] => {
            cpu_state.register_file.af_bank_index = (cpu_state.register_file.af_bank_index + 1) & 1;
            Ok(())
        },
        "EX (byte)": [
            "11_101_111" (EDPrefix), src: Register::H, dst: Register::L,
            "00_***_111" (EDPrefix), src: src_dst(3..6), dst: Register::A
        ] => {
            let current_src: u8 = src.get(cpu_state)?;
            let current_dst: u8 = dst.get(cpu_state)?;
            src.set(cpu_state, current_dst)?;
            dst.set(cpu_state, current_src)?;

            Ok(())
        },
        "EX (word)": [
            "11_100_011", src: indirect(Register::SP), dst: hl(),
            "11_101_011", src: Register::DE, dst: Register::HL,
            "11_101_011" (IXOverride), src: Register::IX, dst: Register::HL,
            "11_101_011" (IYOverride), src: Register::IY, dst: Register::HL,
        ] => {
            let current_src: u16 = src.get(cpu_state)?;
            let current_dst: u16 = dst.get(cpu_state)?;
            src.set(cpu_state, current_dst)?;
            dst.set(cpu_state, current_src)?;

            Ok(())
        },
        "EXTS (byte form)": ["01_100_100" (EDPrefix)] => {
            let a: i8 = Register::A.get(cpu_state)?;
            Register::HL.set(cpu_state, a as i16)?;

            Ok(())
        },
        "EXTS (word form)": ["01_101_100" (EDPrefix)] => {
            let hl: i16 = Register::HL.get(cpu_state)?;
            Register::DE.set(cpu_state, if hl < 0 { 0xffff_u16 } else { 0_u16 })?;

            Ok(())
        },
        "EXX": ["11_011_001"] => {
            cpu_state.register_file.x_bank_index = (cpu_state.register_file.x_bank_index + 1) & 1;
            Ok(())
        },
        "HALT": ["01_110_110"] => {
            privileged_instruction_check(cpu_state)?;

            if cpu_state.system_status_registers.master_status.breakpoint_on_halt_enable() {
                return Err(Trap::BreakpointOnHalt);
            }

            // TODO: handle this properly, this isn't even remotely correct
            std::process::exit(0);
        },
        "IM": [
            "01_000_110" (EDPrefix), mode: InterruptMode::Mode0,
            "01_010_110" (EDPrefix), mode: InterruptMode::Mode1,
            "01_011_110" (EDPrefix), mode: InterruptMode::Mode2,
            "01_001_110" (EDPrefix), mode: InterruptMode::Mode3,
        ] => {
            privileged_instruction_check(cpu_state)?;
            cpu_state.system_status_registers.interrupt_status.set_interrupt_mode(mode);

            Ok(())
        },
        "IN": [
            "01_***_000" (EDPrefix), src: Register::C, dst: r(3..6) | ix_iy_components(3..6) | extended_indirect_modes(3..6), addr_middle_byte: Register::B,
            "11_011_011", src: imm8(), dst: Register::A, addr_middle_byte: Register::A,
        ] => {
            if cpu_state.system_status_registers.trap_control.inhibit_user_io() {
                privileged_instruction_check(cpu_state)?;
            }

            let addr: u8 = src.get(cpu_state)?;
            let full_addr = calculate_io_address(cpu_state, addr, addr_middle_byte)?;
            let mut data = [0];

            cpu_state.mmu.read_io(full_addr, &mut data);

            dst.set(cpu_state, data[0])?;
            Ok(())
        },
        "INC (byte form)": ["00_***_100", dst: src_dst(3..6)] => {
            let value: u8 = dst.get(cpu_state)?;
            let result = value.checked_add(1);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result.unwrap_or_default() & 0b1000_0000) != 0);
            flags.set_zero(result.unwrap_or_default() == 0);
            flags.set_half_carry(calculate_half_carry_u8(value, 1));
            flags.set_parity_overflow(result.is_none());
            flags.set_add_subtract(false);

            dst.set(cpu_state, result.unwrap_or_default())?;
            Ok(())
        },
        "INC (word form)": ["00_**0_011", dst: rr_expanded(4..6)] => {
            let value: u16 = dst.get(cpu_state)?;
            dst.set(cpu_state, value.wrapping_add(1))?;

            Ok(())
        },
        "IND/INI": [
            "10_101_010" (EDPrefix), repeat: const(0), subtract: const(1),
            "10_111_010" (EDPrefix), repeat: const(1), subtract: const(1),
            "10_100_010" (EDPrefix), repeat: const(0), subtract: const(0),
            "10_110_010" (EDPrefix), repeat: const(1), subtract: const(0),
        ] => {
            if cpu_state.system_status_registers.trap_control.inhibit_user_io() {
                privileged_instruction_check(cpu_state)?;
            }

            let zero_flag = loop {
                let addr: u8 = Register::C.get(cpu_state)?;
                let full_addr = calculate_io_address(cpu_state, addr, Register::B)?;
                let mut data = [0];

                cpu_state.mmu.read_io(full_addr, &mut data);

                let b_value: u8 = Register::B.get(cpu_state)?;
                Register::B.set(cpu_state, b_value.wrapping_sub(1))?;

                let hl_value: u16 = Register::HL.get(cpu_state)?;
                let new_hl_value = if subtract.is_non_zero() { hl_value.wrapping_add(1) } else { hl_value.wrapping_sub(1) };

                Memory {
                    address: hl_value,
                    access_type: AccessType::Data,
                }
                .set(cpu_state, data[0])?;

                Register::HL.set(cpu_state, new_hl_value)?;

                if b_value == 1 || repeat.is_zero() {
                    break b_value == 1;
                }
            };

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_zero(zero_flag);
            flags.set_add_subtract(true);

            Ok(())
        },
        "INDW/INIW": [
            "10_001_010" (EDPrefix), repeat: const(0), subtract: const(1),
            "10_011_010" (EDPrefix), repeat: const(1), subtract: const(1),
            "10_000_010" (EDPrefix), repeat: const(0), subtract: const(0),
            "10_010_010" (EDPrefix), repeat: const(1), subtract: const(0),
        ] => {
            if cpu_state.system_status_registers.trap_control.inhibit_user_io() {
                privileged_instruction_check(cpu_state)?;
            }

            let zero_flag = loop {
                let addr: u8 = Register::C.get(cpu_state)?;
                let full_addr = calculate_io_address(cpu_state, addr, Register::B)?;
                let mut data = [0; 2];

                cpu_state.mmu.read_io(full_addr, &mut data);

                let b_value: u8 = Register::B.get(cpu_state)?;
                Register::B.set(cpu_state, b_value.wrapping_sub(1))?;

                let hl_value: u16 = Register::HL.get(cpu_state)?;
                let new_hl_value = if subtract.is_non_zero() { hl_value.wrapping_add(2) } else { hl_value.wrapping_sub(2) };

                Memory {
                    address: hl_value,
                    access_type: AccessType::Data,
                }
                .set(cpu_state, u16::from_le_bytes(data))?;

                Register::HL.set(cpu_state, new_hl_value)?;

                if b_value == 1 || repeat.is_zero() {
                    break b_value == 1;
                }
            };

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_zero(zero_flag);
            flags.set_add_subtract(true);

            Ok(())
        },
        "IN[W]": ["10_110_111" (EDPrefix)] => {
            if cpu_state.system_status_registers.trap_control.inhibit_user_io() {
                privileged_instruction_check(cpu_state)?;
            }

            let addr: u8 = Register::C.get(cpu_state)?;
            let full_addr = calculate_io_address(cpu_state, addr, Register::B)?;
            let mut data = [0; 2];

            cpu_state.mmu.read_io(full_addr, &mut data);

            Register::HL.set(cpu_state, u16::from_le_bytes(data))?;
            Ok(())
        },
        "JAF": ["00_101_000" (IXOverride), addr: indirect(Register::PC + imm8())] => {
            if cpu_state.register_file.af_bank_index == 1 {
                Register::PC.set(cpu_state, addr.address)?;
            }

            Ok(())
        },
        "JAR": ["00_100_000" (IXOverride), addr: indirect(Register::PC + imm8())] => {
            if cpu_state.register_file.x_bank_index == 1 {
                Register::PC.set(cpu_state, addr.address)?;
            }

            Ok(())
        },
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
            let target: u16 = dst.get(cpu_state)?;

            if cc.is_condition_met(cpu_state) {
                Register::PC.set(cpu_state, target)?;
            }

            Ok(())
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
            let value: u8 = src.get(cpu_state)?;
            dst.set(cpu_state, value)?;

            Ok(())
        },
        "LD (word)": [
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
            let value: u16 = src.get(cpu_state)?;
            dst.set(cpu_state, value)?;

            Ok(())
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
        ] => {
            privileged_instruction_check(cpu_state)?;

            let value: u8 = src.get(cpu_state)?;
            dst.set(cpu_state, value)?;

            if dst == Register::A {
                let parity_overflow_flag = cpu_state.system_status_registers.interrupt_status.a_vector_enable();
                let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

                flags.set_sign((value & 0b1000_0000) != 0);
                flags.set_zero(value == 0);
                flags.set_half_carry(false);
                flags.set_parity_overflow(parity_overflow_flag);
                flags.set_add_subtract(false);
            }

            Ok(())
        },
        "LDA": [
            // DA is a duplicate of LDW
            // X, RA, SR, BX
            "00_***_010" (EDPrefix), src: lda_extended(3..6), dst: hl(),
        ] => {
            dst.set(cpu_state, src.address)?;

            Ok(())
        },
        "LDCTL": [
            "01_100_110" (EDPrefix), src: Register::C, dst: hl(),
            "01_101_110" (EDPrefix), src: hl(), dst: Register::C,
            "10_000_111" (EDPrefix), src: Register::USP, dst: hl(),
            "10_001_111" (EDPrefix), src: hl(), dst: Register::USP,
        ] => {
            privileged_instruction_check(cpu_state)?;

            if src == Register::C {
                let address: u8 = src.get(cpu_state)?;
                let src = cpu_state.load_register_by_address(address);
                dst.set(cpu_state, src)?;
            } else if dst == Register::C {
                let src: u16 = src.get(cpu_state)?;
                let address: u8 = dst.get(cpu_state)?;
                cpu_state.store_register_by_address(address, src);
            } else {
                let src: u16 = src.get(cpu_state)?;
                dst.set(cpu_state, src)?;
            }

            Ok(())
        },
        "LDD/LDI": [
            "10_101_000" (EDPrefix), repeat: const(0), subtract: const(1),
            "10_111_000" (EDPrefix), repeat: const(1), subtract: const(1),
            "10_100_000" (EDPrefix), repeat: const(0), subtract: const(0),
            "10_110_000" (EDPrefix), repeat: const(1), subtract: const(0),
        ] => {
            let flag = loop {
                let de_value = Register::DE.get(cpu_state)?;
                let hl_value = Register::HL.get(cpu_state)?;

                let byte: u8 =
                    Memory {
                        address: hl_value,
                        access_type: AccessType::Data,
                    }
                    .get(cpu_state)?;

                Memory {
                    address: de_value,
                    access_type: AccessType::Data,
                }
                .set(cpu_state, byte)?;

                if subtract.is_non_zero() {
                    Register::DE.set(cpu_state, de_value.wrapping_sub(1))?;
                    Register::HL.set(cpu_state, de_value.wrapping_sub(1))?;
                } else {
                    Register::DE.set(cpu_state, de_value.wrapping_add(1))?;
                    Register::HL.set(cpu_state, de_value.wrapping_add(1))?;
                }

                let bc_value: u16 = Register::BC.get(cpu_state)?;
                Register::BC.set(cpu_state, bc_value.wrapping_sub(1))?;

                if bc_value == 1 || repeat.is_zero() {
                    break bc_value == 1;
                }
            };

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_half_carry(false);
            flags.set_parity_overflow(flag);
            flags.set_add_subtract(false);

            Ok(())
        },
        "LDUD/LDUP A, *": [
            // LDUD
            "10_000_110" (EDPrefix), src: hl_indirect_sx(), dst: Register::A, kind: AccessType::Data,
            // LDUP
            "10_010_110" (EDPrefix), src: hl_indirect_sx(), dst: Register::A, kind: AccessType::Program,
        ] => {
            privileged_instruction_check(cpu_state)?;

            let mut data = [0];
            match cpu_state.mmu.read_memory(UserSystemBit::User, kind, src.address, &mut data) {
                Ok(_) => {
                    dst.set(cpu_state, data[0])?;
                    cpu_state.register_file.current_af_bank_mut().f.set_carry(false);
                },
                Err(error) => {
                    let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
                    flags.set_zero(error.wp_bit_used);
                    flags.set_parity_overflow(error.valid_bit_used);
                    flags.set_carry(true);
                }
            }

            Ok(())
        },
        "LDUD/LDUP *, A": [
            // LDUD
            "10_001_110" (EDPrefix), src: Register::A, dst: hl_indirect_sx(), kind: AccessType::Data,
            // LDUP
            "10_011_110" (EDPrefix), src: Register::A, dst: hl_indirect_sx(), kind: AccessType::Program,
        ] => {
            privileged_instruction_check(cpu_state)?;

            let data: u8 = src.get(cpu_state)?;
            match cpu_state.mmu.write_memory(UserSystemBit::User, kind, dst.address, &[data]) {
                Ok(_) => cpu_state.register_file.current_af_bank_mut().f.set_carry(false),
                Err(error) => {
                    let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
                    flags.set_zero(error.wp_bit_used);
                    flags.set_parity_overflow(error.valid_bit_used);
                    flags.set_carry(true);
                }
            }

            Ok(())
        },
        "MULT": [
            "11_***_000" (EDPrefix), src: src_dst(3..6),
            "11_111_000" (EDPrefix + IYOverride), src: imm8(),
        ] => {
            let a: i8 = Register::A.get(cpu_state)?;
            let src: i8 = src.get(cpu_state)?;

            let result = i16::from(a) * i16::from(src);
            Register::HL.set(cpu_state, result)?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign(result < 0);
            flags.set_zero(result == 0);
            flags.set_parity_overflow(false);
            flags.set_carry(!(-128..=127).contains(&result));

            Ok(())
        },
        "MULTU": [
            "11_***_001" (EDPrefix), src: src_dst(3..6),
            "11_111_001" (EDPrefix + IYOverride), src: imm8(),
        ] => {
            let a: u8 = Register::A.get(cpu_state)?;
            let src: u8 = src.get(cpu_state)?;

            let result = u16::from(a) * u16::from(src);
            Register::HL.set(cpu_state, result)?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign(false);
            flags.set_zero(result == 0);
            flags.set_parity_overflow(false);
            flags.set_carry(result > 0xff);

            Ok(())
        },
        "MULTUW": ["11_**0_011" (EDPrefix), src: rr_expanded(4..6)] => {
            let hl: u16 = Register::HL.get(cpu_state)?;
            let src: u16 = src.get(cpu_state)?;

            let result = u32::from(hl) * u32::from(src);
            Register::DE.set(cpu_state, (result >> 16) as u16)?;
            Register::HL.set(cpu_state, (result & 0xffff) as u16)?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign(false);
            flags.set_zero(result == 0);
            flags.set_parity_overflow(false);
            flags.set_carry(result > 0xffff);

            Ok(())
        },
        "MULTW": ["11_**0_010" (EDPrefix), src: rr_expanded(4..6)] => {
            let hl: i16 = Register::HL.get(cpu_state)?;
            let src: i16 = src.get(cpu_state)?;

            let result = i32::from(hl) * i32::from(src);
            Register::DE.set(cpu_state, (result >> 16) as i16)?;
            Register::HL.set(cpu_state, (result & 0xffff) as i16)?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign(result < 0);
            flags.set_zero(result == 0);
            flags.set_parity_overflow(false);
            flags.set_carry(!(-32768..=32767).contains(&result));

            Ok(())
        },
        "NEG A": ["01_000_100" (EDPrefix)] => {
            let value: i8 = Register::A.get(cpu_state)?;
            Register::A.set(cpu_state, if value == -128 { -128 } else { -value })?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign(value < 0);
            flags.set_zero(value == 0);
            flags.set_half_carry(calculate_half_carry_u8(0, value as u8));
            flags.set_parity_overflow(value != -128);
            flags.set_add_subtract(true);
            flags.set_carry(value != 0);

            Ok(())
        },
        "NEG HL": ["01_001_100" (EDPrefix)] => {
            let value: i16 = Register::HL.get(cpu_state)?;
            Register::HL.set(cpu_state, if value == -32768 { -32768 } else { -value })?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign(value < 0);
            flags.set_zero(value == 0);
            flags.set_half_carry(calculate_half_carry_u16(0, value as u16));
            flags.set_parity_overflow(value != -32768);
            flags.set_add_subtract(true);
            flags.set_carry(value != 0);

            Ok(())
        },
        "NOP": ["00_000_000"] => {
            Ok(())
        },
        "OR": ["10_110_***", src: src_dst(0..3)] => {
            let a: u8 = Register::A.get(cpu_state)?;
            let src: u8 = src.get(cpu_state)?;
            let result = a | src;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(calculate_parity(u16::from(result)));
            flags.set_add_subtract(false);
            flags.set_carry(false);

            Register::A.set(cpu_state, result)?;
            Ok(())
        },
        "OUT": [
            "01_***_001" (EDPrefix), src: r(3..6) | ix_iy_components(3..6) | extended_indirect_modes(3..6), dst: Register::C, addr_middle_byte: Register::B,
            "11_010_011", src: Register::A, dst: imm8(), addr_middle_byte: Register::A,
        ] => {
            if cpu_state.system_status_registers.trap_control.inhibit_user_io() {
                privileged_instruction_check(cpu_state)?;
            }

            let addr: u8 = dst.get(cpu_state)?;
            let value: u8 = src.get(cpu_state)?;
            let full_addr = calculate_io_address(cpu_state, addr, addr_middle_byte)?;

            cpu_state.mmu.write_io(full_addr, &[value]);
            Ok(())
        },
        "OUTD/OUTI": [
            "10_101_011" (EDPrefix), repeat: const(0), subtract: const(1),
            "10_111_011" (EDPrefix), repeat: const(1), subtract: const(1),
            "10_100_011" (EDPrefix), repeat: const(0), subtract: const(0),
            "10_110_011" (EDPrefix), repeat: const(1), subtract: const(0),
        ] => {
            if cpu_state.system_status_registers.trap_control.inhibit_user_io() {
                privileged_instruction_check(cpu_state)?;
            }

            let zero_flag = loop {
                let addr: u8 = Register::C.get(cpu_state)?;
                let full_addr = calculate_io_address(cpu_state, addr, Register::B)?;

                let b_value: u8 = Register::B.get(cpu_state)?;
                Register::B.set(cpu_state, b_value.wrapping_sub(1))?;

                let hl_value: u16 = Register::HL.get(cpu_state)?;
                let new_hl_value = if subtract.is_non_zero() { hl_value.wrapping_add(1) } else { hl_value.wrapping_sub(1) };
                let to_write: u8 =
                    Memory {
                        address: hl_value,
                        access_type: AccessType::Data,
                    }
                    .get(cpu_state)?;

                cpu_state.mmu.write_io(full_addr, &[to_write]);

                Register::HL.set(cpu_state, new_hl_value)?;

                if b_value == 1 || repeat.is_zero() {
                    break b_value == 1;
                }
            };

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_zero(zero_flag);
            flags.set_add_subtract(true);

            Ok(())
        },
        "OUTDW/OUTIW": [
            "10_001_011" (EDPrefix), repeat: const(0), subtract: const(1),
            "10_011_011" (EDPrefix), repeat: const(1), subtract: const(1),
            "10_000_011" (EDPrefix), repeat: const(0), subtract: const(0),
            "10_010_011" (EDPrefix), repeat: const(1), subtract: const(0),
        ] => {
            if cpu_state.system_status_registers.trap_control.inhibit_user_io() {
                privileged_instruction_check(cpu_state)?;
            }

            let zero_flag = loop {
                let addr: u8 = Register::C.get(cpu_state)?;
                let full_addr = calculate_io_address(cpu_state, addr, Register::B)?;

                let b_value: u8 = Register::B.get(cpu_state)?;
                Register::B.set(cpu_state, b_value.wrapping_sub(1))?;

                let hl_value: u16 = Register::HL.get(cpu_state)?;
                let new_hl_value = if subtract.is_non_zero() { hl_value.wrapping_add(2) } else { hl_value.wrapping_sub(2) };
                let to_write: u16 =
                    Memory {
                        address: hl_value,
                        access_type: AccessType::Data,
                    }
                    .get(cpu_state)?;

                cpu_state.mmu.write_io(full_addr, &to_write.to_le_bytes());
                Register::HL.set(cpu_state, new_hl_value)?;

                if b_value == 1 || repeat.is_zero() {
                    break b_value == 1;
                }
            };

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_zero(zero_flag);
            flags.set_add_subtract(true);

            Ok(())
        },
        "OUT[W]": ["10_111_111" (EDPrefix)] => {
            if cpu_state.system_status_registers.trap_control.inhibit_user_io() {
                privileged_instruction_check(cpu_state)?;
            }

            let addr: u8 = Register::C.get(cpu_state)?;
            let full_addr = calculate_io_address(cpu_state, addr, Register::B)?;
            let value: u16 = Register::HL.get(cpu_state)?;

            cpu_state.mmu.write_io(full_addr, &value.to_le_bytes());
            Ok(())
        },
        "PCACHE": ["01_100_101" (EDPrefix)] => unimplemented,
        "POP": ["11_**0_001", dst: rr_stack_ops(4..6) | rr_ix_expansion(4..6)] => {
            let value = pop(cpu_state)?;
            dst.set(cpu_state, value)?;

            Ok(())
        },
        "PUSH": [
            // R, IR, DA, RA
            "11_**0_101", src: rr_stack_ops(4..6) | rr_ix_expansion(4..6),
            // IM
            "11_110_101" (IYOverride), src: imm16(),
        ] => {
            let value = src.get(cpu_state)?;
            push(cpu_state, value)?;
            system_stack_overflow_check(cpu_state, false)
        },
        "RES": ["10_***_***" (CBPrefix), b: imm_unsigned(3..6), dst: r(0..3) | hl_indirection(0..3)] => {
            let b: u8 = b.get(cpu_state)?;
            let dst_value: u8 = dst.get(cpu_state)?;
            dst.set(cpu_state, dst_value & !(1 << b))?;

            Ok(())
        },
        "RET": [
            "11_***_000", cc: cc(3..6),
            "11_001_001", cc: ConditionCode::Always,
        ] => {
            if cc.is_condition_met(cpu_state) {
                let new_pc = pop(cpu_state)?;
                Register::PC.set(cpu_state, new_pc)?;
            }

            Ok(())
        },
        "RETI": ["01_001_101" (EDPrefix)] => {
            privileged_instruction_check(cpu_state)?;

            let new_pc = pop(cpu_state)?;
            Register::PC.set(cpu_state, new_pc)?;

            // TODO: how should the special bus transactions this performs be emulated?
            Ok(())
        },
        "RETIL": ["01_010_101" (EDPrefix)] => {
            privileged_instruction_check(cpu_state)?;

            let new_msr = pop(cpu_state)?;
            let new_pc = pop(cpu_state)?;

            let old_msr = std::mem::replace(&mut cpu_state.system_status_registers.master_status, crate::registers::MasterStatus::from_bits(new_msr));
            Register::PC.set(cpu_state, new_pc)?;

            let msr = &mut cpu_state.system_status_registers.master_status;
            msr.set_single_step_pending(msr.single_step_pending() || old_msr.single_step_pending());

            Ok(())
        },
        "RETN": ["01_000_101" (EDPrefix)] => {
            privileged_instruction_check(cpu_state)?;

            let new_pc = pop(cpu_state)?;
            Register::PC.set(cpu_state, new_pc)?;
            cpu_state.system_status_registers.master_status.set_irq_enable(cpu_state.interrupt_shadow_register);

            Ok(())
        },
        "RL": [
            "00_010_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3), set_flags: const(1),
            "00_010_111", dst: Register::A, set_flags: const(0),
        ] => {
            let dst_value: u8 = dst.get(cpu_state)?;
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            let result = (dst_value << 1) | if flags.carry() { 1 } else { 0 };

            if set_flags.is_non_zero() {
                flags.set_sign((result & 0b1000_0000) != 0);
                flags.set_zero(result == 0);
                flags.set_parity_overflow(calculate_parity(u16::from(result)));
            }

            flags.set_half_carry(false);
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 0x80 != 0);

            dst.set(cpu_state, result)?;
            Ok(())
        },
        "RLC": [
            "00_000_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3), set_flags: const(1),
            "00_000_111", dst: Register::A, set_flags: const(0),
        ] => {
            let dst_value: u8 = dst.get(cpu_state)?;
            let result = (dst_value << 1) | ((dst_value & 0x80) >> 7);

            dst.set(cpu_state, result)?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            if set_flags.is_non_zero() {
                flags.set_sign((result & 0b1000_0000) != 0);
                flags.set_zero(result == 0);
                flags.set_parity_overflow(calculate_parity(u16::from(result)));
            }

            flags.set_half_carry(false);
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 0x80 != 0);

            Ok(())
        },
        "RLD": ["01_101_111" (EDPrefix), dst: indirect(Register::HL)] => {
            let a_value: u8 = Register::A.get(cpu_state)?;
            let dst_value: u8 = dst.get(cpu_state)?;

            let new_a = (a_value & 0xf0) | (dst_value >> 4);
            let new_dst = (dst_value << 4) | (a_value & 0x0f);

            Register::A.set(cpu_state, new_a)?;
            dst.set(cpu_state, new_dst)?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            flags.set_sign((new_a & 0b1000_0000) != 0);
            flags.set_zero(new_a == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(calculate_parity(u16::from(new_a)));
            flags.set_add_subtract(false);

            Ok(())
        },
        "RR": [
            "00_011_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3), set_flags: const(1),
            "00_011_111", dst: Register::A, set_flags: const(0),
        ] => {
            let dst_value: u8 = dst.get(cpu_state)?;
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            let result = (dst_value >> 1) | if flags.carry() { 0x80 } else { 0 };

            if set_flags.is_non_zero() {
                flags.set_sign((result & 0b1000_0000) != 0);
                flags.set_zero(result == 0);
                flags.set_parity_overflow(calculate_parity(u16::from(result)));
            }

            flags.set_half_carry(false);
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 1 != 0);

            dst.set(cpu_state, result)?;
            Ok(())
        },
        "RRC": [
            "00_001_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3), set_flags: const(1),
            "00_001_111", dst: Register::A, set_flags: const(0),
        ] => {
            let dst_value: u8 = dst.get(cpu_state)?;
            let result = (dst_value >> 1) | ((dst_value & 1) << 7);

            dst.set(cpu_state, result)?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            if set_flags.is_non_zero() {
                flags.set_sign((result & 0b1000_0000) != 0);
                flags.set_zero(result == 0);
                flags.set_parity_overflow(calculate_parity(u16::from(result)));
            }

            flags.set_half_carry(false);
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 1 != 0);

            Ok(())
        },
        "RRD": ["01_100_111" (EDPrefix), dst: indirect(Register::HL)] => {
            let a_value: u8 = Register::A.get(cpu_state)?;
            let dst_value: u8 = dst.get(cpu_state)?;

            let new_a = (a_value & 0xf0) | (dst_value & 0x0f);
            let new_dst = (dst_value >> 4) | (a_value << 4);

            Register::A.set(cpu_state, new_a)?;
            dst.set(cpu_state, new_dst)?;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            flags.set_sign((new_a & 0b1000_0000) != 0);
            flags.set_zero(new_a == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(calculate_parity(u16::from(new_a)));
            flags.set_add_subtract(false);

            Ok(())
        },
        "RST": ["11_***_111", addr: t_encoding(3..6)] => {
            let addr: u16 = addr.get(cpu_state)?;
            let value = Register::PC.get(cpu_state)?;
            push(cpu_state, value)?;
            Register::PC.set(cpu_state, addr)?;

            Ok(())
        },
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
            Ok(())
        },
        "SBC (word form)/SUBW": [
            // SBC
            "01_**0_010" (EDPrefix), src: rr(4..6) | rr_xy_overrides(4..6), dst: hl(), use_carry: const(1),
            // SUBW
            "11_**1_110" (EDPrefix), src: rr_expanded(4..6), dst: Register::HL, use_carry: const(0),
        ] => {
            impl_sub!(u16, cpu_state, dst, src, use_carry.is_non_zero());
            Ok(())
        },
        "SC": ["01_110_001" (EDPrefix), nn: imm16()] => {
            Err(Trap::SystemCall(nn.get(cpu_state)?))
        },
        "SCF": ["0_110_111"] => {
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_half_carry(false);
            flags.set_add_subtract(false);
            flags.set_carry(true);

            Ok(())
        },
        "SET": ["11_***_***" (CBPrefix), b: imm_unsigned(3..6), dst: r(0..3) | hl_indirection(0..3)] => {
            let b: u8 = b.get(cpu_state)?;
            let dst_value: u8 = dst.get(cpu_state)?;
            dst.set(cpu_state, dst_value | (1 << b))?;

            Ok(())
        },
        "SLA": ["00_100_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => {
            let dst_value: u8 = dst.get(cpu_state)?;
            let result = dst_value << 1;
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(calculate_parity(u16::from(result)));
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 0x80 != 0);

            dst.set(cpu_state, result)?;
            Ok(())
        },
        "SRA": ["00_101_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => {
            let dst_value: u8 = dst.get(cpu_state)?;
            let result = (dst_value >> 1) | (dst_value & 0x80);
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(calculate_parity(u16::from(result)));
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 1 != 0);

            dst.set(cpu_state, result)?;
            Ok(())
        },
        "SRL": ["00_111_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => {
            let dst_value: u8 = dst.get(cpu_state)?;
            let result = dst_value >> 1;
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(calculate_parity(u16::from(result)));
            flags.set_add_subtract(false);
            flags.set_carry(dst_value & 1 != 0);

            dst.set(cpu_state, result)?;
            Ok(())
        },
        "TSET": ["00_110_***" (CBPrefix), dst: r(0..3) | hl_indirection(0..3)] => {
            let dst_value: u8 = dst.get(cpu_state)?;
            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;

            flags.set_sign((dst_value & 0b1000_0000) != 0);
            dst.set(cpu_state, 0xff_u8)?;

            Ok(())
        },
        "TSTI": ["01_110_000" (EDPrefix)] => {
            if cpu_state.system_status_registers.trap_control.inhibit_user_io() {
                privileged_instruction_check(cpu_state)?;
            }

            let addr: u8 = Register::C.get(cpu_state)?;
            let full_addr = calculate_io_address(cpu_state, addr, Register::B)?;
            let mut data = [0];

            cpu_state.mmu.read_io(full_addr, &mut data);

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((data[0] & 0b1000_0000) != 0);
            flags.set_zero(data[0] == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(calculate_parity(u16::from(data[0])));
            flags.set_add_subtract(false);

            Ok(())
        },
        "XOR": [
            // R, RX, IR, DA, X, SX, RA, SR, BX
            "10_101_***", src: src_dst(0..3),
            // IM
            "11_101_110", src: imm8(),
        ] => {
            let a: u8 = Register::A.get(cpu_state)?;
            let src: u8 = src.get(cpu_state)?;
            let result = a ^ src;

            let flags = &mut cpu_state.register_file.current_af_bank_mut().f;
            flags.set_sign((result & 0b1000_0000) != 0);
            flags.set_zero(result == 0);
            flags.set_half_carry(false);
            flags.set_parity_overflow(calculate_parity(u16::from(result)));
            flags.set_add_subtract(false);
            flags.set_carry(false);

            Register::A.set(cpu_state, result)?;
            Ok(())
        },
        "other EPU instructions": [
            // EPU internal
            "10_011_111" (EDPrefix), template_a: imm16(), template_b: imm16(), table_offset: const(12),
            // load accumulator from EPU
            "10_010_111" (EDPrefix), template_a: imm16(), template_b: imm16(), table_offset: const(8),
        ] => {
            let pc: u16 = Register::PC.get(cpu_state)?;
            let table_offset: u16 = table_offset.get(cpu_state)?;

            Err(Trap::ExtendedInstruction {
                memory_operand_address: None,
                template_address: pc - 4,
                vector_table_offset: u32::from(table_offset),
            })
        },
        "load EPU from/to memory": [
            // load EPU from memory
            // IR
            "10_100_110" (EDPrefix), operand: indirect(Register::HL), template_a: imm16(), template_b: imm16(), table_offset: const(0),
            // DA
            "10_100_111" (EDPrefix), operand: indirect(imm16()), template_a: imm16(), template_b: imm16(), table_offset: const(0),
            // X
            "10_***_100" (EDPrefix), operand: lda_extended(3..6), template_a: imm16(), template_b: imm16(), table_offset: const(0),

            // load memory from EPU
            // IR
            "10_101_110" (EDPrefix), operand: indirect(Register::HL), template_a: imm16(), template_b: imm16(), table_offset: const(4),
            // DA
            "10_101_111" (EDPrefix), operand: indirect(imm16()), template_a: imm16(), template_b: imm16(), table_offset: const(4),
            // X
            "10_***_101" (EDPrefix), operand: lda_extended(3..6), template_a: imm16(), template_b: imm16(), table_offset: const(4),
        ] => {
            let pc: u16 = Register::PC.get(cpu_state)?;
            let memory_operand_address = Some(operand.get(cpu_state)?);
            let table_offset: u16 = table_offset.get(cpu_state)?;

            Err(Trap::ExtendedInstruction {
                memory_operand_address,
                template_address: pc - 4,
                vector_table_offset: u32::from(table_offset),
            })
        },
    },
    invalid_instruction_handler: {
        warn!("invalid instruction {opcode:#x} with prefixes {prefixes:?}");
        Ok(())
    },
    unimplemented_instruction_handler: {
        warn!("unimplemented instruction {instruction_as_string}");
        Ok(())
    },
}
