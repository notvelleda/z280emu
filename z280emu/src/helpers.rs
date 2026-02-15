use crate::BusAccessor;

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
            Self::SP => cpu_state.register_file.stack_pointers[cpu_state.system_status_registers.master_status.user_system_bit().stack_pointer_index()],
            Self::USP => cpu_state.register_file.stack_pointers[1],
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
            Self::SP => cpu_state.register_file.stack_pointers[cpu_state.system_status_registers.master_status.user_system_bit().stack_pointer_index()] = value,
            Self::USP => cpu_state.register_file.stack_pointers[1] = value,
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

impl RegisterOrMemoryAccessor<i8> for Memory {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> i8 {
        let mut result = [0];

        cpu_state.bus_accessor.read(crate::BusAddressSpace::Memory, u32::from(self.address), &mut result);

        result[0] as i8
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: i8) {
        cpu_state.bus_accessor.write(crate::BusAddressSpace::Memory, u32::from(self.address), &[value as u8]);
    }
}

impl RegisterOrMemoryAccessor<i16> for Memory {
    fn get<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) -> i16 {
        let mut result = [0; 2];

        cpu_state.bus_accessor.read(crate::BusAddressSpace::Memory, u32::from(self.address), &mut result);

        i16::from_le_bytes(result)
    }

    fn set<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>, value: i16) {
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

pub fn indirect<T: BusAccessor>(cpu_state: &mut super::CPUState<T>, lhs: impl RegisterOrMemoryAccessor<u16>, rhs: impl RegisterOrMemoryAccessor<i16>) -> Memory {
    Memory {
        address: lhs.get(cpu_state).wrapping_add_signed(rhs.get(cpu_state)),
    }
}

pub fn direct<T: BusAccessor>(cpu_state: &mut super::CPUState<T>, lhs: impl RegisterOrMemoryAccessor<u16>, rhs: impl RegisterOrMemoryAccessor<i16>) -> Immediate {
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
    pub const fn is_condition_met<T: BusAccessor>(&self, cpu_state: &super::CPUState<T>) -> bool {
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

pub fn calculate_parity(mut value: u16) -> bool {
    let mut parity = false;

    while value != 0 {
        parity ^= (value & 1) != 0;
        value >>= 1;
    }

    parity
}

pub fn calculate_half_carry_u8(lhs: u8, rhs: u8) -> bool {
    (lhs ^ rhs ^ (lhs.wrapping_add(rhs))) & (1 << 4) != 0
}

pub fn calculate_half_carry_u16(lhs: u16, rhs: u16) -> bool {
    (lhs ^ rhs ^ (lhs.wrapping_add(rhs))) & (1 << 8) != 0
}

// TODO: system stack overflow warning trap
pub fn push<T: BusAccessor>(cpu_state: &mut super::CPUState<T>, value: u16) {
    let sp: u16 = Register::SP.get(cpu_state);
    let sp = sp.wrapping_sub(2);
    Register::SP.set(cpu_state, sp);

    Memory { address: sp }.set(cpu_state, value);
}

pub fn pop<T: BusAccessor>(cpu_state: &mut super::CPUState<T>) -> u16 {
    let sp: u16 = Register::SP.get(cpu_state);
    let new_sp = sp.wrapping_add(2);
    Register::SP.set(cpu_state, new_sp);

    Memory { address: sp }.get(cpu_state)
}

pub fn calculate_io_address<T: BusAccessor>(cpu_state: &mut super::CPUState<T>, low_byte: u8, middle_byte: Register) -> u32 {
    let middle_byte: u8 = middle_byte.get(cpu_state);
    (low_byte as u32) | ((middle_byte as u32) << 8) | ((cpu_state.system_status_registers.io_page as u32) << 16)
}

pub fn privileged_instruction_check<T: BusAccessor>(cpu_state: &mut super::CPUState<T>) -> Result<(), Trap> {
    match cpu_state.system_status_registers.master_status.user_system_bit() {
        crate::registers::UserSystemBit::User => Err(Trap::PrivilegedInstruction),
        crate::registers::UserSystemBit::System => Ok(()),
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Trap {
    ExtendedInstruction {
        memory_operand_address: Option<u16>,
        template_address: u16,
        vector_table_offset: u32,
    },
    PrivilegedInstruction,
    SystemCall(u16),
    AccessViolation,
    SystemStackOverflowWarning,
    DivisionException,
    SingleStep,
    BreakpointOnHalt,
}

impl Trap {
    /// whether the address of the next instruction should be pushed to the stack when handling this trap instead of the address of the current instruction
    pub const fn should_push_next_instruction_address(&self) -> bool {
        match self {
            Self::ExtendedInstruction { .. } | Self::SystemCall(_) | Self::SystemStackOverflowWarning | Self::SingleStep => true,
            Self::PrivilegedInstruction | Self::AccessViolation | Self::DivisionException | Self::BreakpointOnHalt => false,
        }
    }

    /// called when handling a trap to push extra trap-specific information to the stack
    pub fn push_extra_data<T: BusAccessor>(&self, cpu_state: &mut super::CPUState<T>) {
        match self {
            Self::ExtendedInstruction {
                memory_operand_address,
                template_address,
                ..
            } => {
                if let Some(address) = memory_operand_address {
                    push(cpu_state, *address);
                }

                push(cpu_state, *template_address);
            }
            Self::SystemCall(immediate) => push(cpu_state, *immediate),
            _ => (),
        }
    }

    /// gets the offset to load the new PC and MSR values from the interrupt/trap vector table at
    pub fn vector_table_offset(&self) -> u32 {
        match self {
            Self::ExtendedInstruction { vector_table_offset, .. } => 0x58 + vector_table_offset,
            Self::PrivilegedInstruction => 0x54,
            Self::SystemCall(_) => 0x50,
            Self::AccessViolation => 0x4c,
            Self::SystemStackOverflowWarning => 0x48,
            Self::DivisionException => 0x44,
            Self::SingleStep => 0x3c,
            Self::BreakpointOnHalt => 0x40,
        }
    }
}

pub fn system_stack_overflow_check<T: BusAccessor>(cpu_state: &mut super::CPUState<T>, force: bool) -> Result<(), Trap> {
    if !cpu_state.system_status_registers.trap_control.system_stack_overflow_warning()
        || !(cpu_state.system_status_registers.master_status.user_system_bit() == crate::registers::UserSystemBit::System || force)
    {
        return Ok(());
    }

    let sp_value: u16 = Register::SP.get(cpu_state);

    match (sp_value & !15) == (cpu_state.system_status_registers.system_stack_limit & !15) {
        true => Err(Trap::SystemStackOverflowWarning),
        false => Ok(()),
    }
}
