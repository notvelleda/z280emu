use bitfields::bitfield;

#[derive(Copy, Clone, Debug, Default)]
pub struct AFBank {
    /// accumulator register
    pub a: u8,
    /// flag register
    pub f: Flags,
}

#[derive(Copy, Clone, Debug, Default)]
pub struct ExtendedBank {
    /// byte register B
    pub b: u8,
    /// byte register C
    pub c: u8,
    /// byte register D
    pub d: u8,
    /// byte register E
    pub e: u8,
    /// 16 bit register pair HL (H, L)
    pub hl: u16,
}

#[bitfield(u8)]
#[derive(Copy, Clone)]
pub struct Flags {
    /// the Carry Flag (C)
    pub carry: bool,
    /// the Add/Subtract Flag (N)
    pub add_subtract: bool,
    /// the Parity/Overflow Flag (P/V)
    pub parity_overflow: bool,
    #[bits(1, default = 0)]
    _zero: u8,
    /// the Half-Carry Flag (H)
    pub half_carry: bool,
    #[bits(1, default = 0)]
    _zero: u8,
    /// the Zero Flag (Z)
    pub zero: bool,
    /// the Sign Flag (S)
    pub sign: bool,
}

#[derive(Copy, Clone, Debug, Default)]
pub struct RegisterFile {
    /// AF and AF' registers
    pub af_bank: [AFBank; 2],
    /// which of the sets of AF registers is in use
    pub af_bank_index: usize,
    /// BC, DE, HL and BC', DE', HL' registers
    pub x_bank: [ExtendedBank; 2],
    /// which of the sets of other byte/word registers is in use
    pub x_bank_index: usize,
    /// interrupt register
    pub i: u8,
    /// refresh register
    pub r: u8,
    /// index register pair IX (IXH, IXL)
    pub ix: u16,
    /// index register pair IY (IYH, IYL)
    pub iy: u16,
    /// program counter
    pub pc: u16,
    /// SSP and USP stack pointer registers
    pub stack_pointers: [u16; 2],
}

impl RegisterFile {
    /// returns a reference to the set of accumulator and flags registers currently in use
    pub const fn current_af_bank(&self) -> &AFBank {
        &self.af_bank[self.af_bank_index]
    }

    /// returns a mutable reference to the set of accumulator and flags registers currently in use
    pub const fn current_af_bank_mut(&mut self) -> &mut AFBank {
        &mut self.af_bank[self.af_bank_index]
    }

    /// returns a reference to the set of other byte/word registers currently in use
    pub const fn current_x_bank(&self) -> &ExtendedBank {
        &self.x_bank[self.x_bank_index]
    }

    /// returns a mutable reference to the set of other byte/word registers currently in use
    pub const fn current_x_bank_mut(&mut self) -> &mut ExtendedBank {
        &mut self.x_bank[self.x_bank_index]
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct ControlRegisters {
    /// the Bus Timing and Control register
    pub bus_timing_and_control: BusTimingAndControl,
    /// the Bus Timing and Initialization register
    pub bus_timing_and_initialization: BusTimingAndInitialization,
    /// the Local Address register
    pub local_address: LocalAddress,
    /// the Cache Control register
    pub cache_control: CacheControl,
}

/// the contents of the Bus Timing and Initialization register
#[bitfield(u8)]
#[derive(Copy, Clone)]
pub struct BusTimingAndInitialization {
    /// the Bus Clock Frequency field (CS). this cannot be modified via software
    #[bits(2, default = BusClockFrequency::BusClockHalf)]
    pub bus_clock_frequency: BusClockFrequency,
    /// the Low Memory Wait Insertion field (LM)
    #[bits(2, default = 0)]
    pub low_memory_wait_insertion: u8,
    /// reserved field, must be 0
    #[bits(1, default = 0)]
    _zero: u8,
    /// the Multiprocessor Configuration Enable bit (MP)
    pub multiprocessor_enable: bool,
    /// the Bootstrap Mode Enable bit (BS).
    /// this cannot be modified via software and must be set to true when read
    #[bits(default = false)]
    pub bootstrap_mode_enable: bool,
    /// reserved field, must be 1
    #[bits(1, default = 1)]
    _one: u8,
}

/// the CS field (bits 0-1) in the Bus Timing and Initialization register
#[derive(Copy, Clone, Debug)]
pub enum BusClockFrequency {
    /// sets the bus clock to run at 1/2 the CPU clock frequency
    BusClockHalf,
    /// sets the bus clock to run at the CPU clock frequency
    BusClockEqual,
    /// sets the bus clock to run at 1/4 the CPU clock frequency
    BusClockQuarter,
    Reserved,
}

impl BusClockFrequency {
    pub const fn from_bits(bits: u8) -> Self {
        match bits {
            0b00 => Self::BusClockHalf,
            0b01 => Self::BusClockEqual,
            0b10 => Self::BusClockQuarter,
            0b11 => Self::Reserved,
            _ => panic!("invalid input to BusClockSetting::from_bits()"),
        }
    }

    pub const fn into_bits(self) -> u8 {
        match self {
            Self::BusClockHalf => 0b00,
            Self::BusClockEqual => 0b01,
            Self::BusClockQuarter => 0b10,
            Self::Reserved => 0b11,
        }
    }
}

/// the Bus Timing and Control Register
#[bitfield(u8)]
#[derive(Copy, Clone)]
pub struct BusTimingAndControl {
    /// the I/O Wait Insertion field (I/O)
    #[bits(2, default = 0)]
    pub io_wait_insertion: u8,
    /// the High Memory Wait Insertion field (HM)
    #[bits(2, default = 0)]
    pub high_memory_wait_insertion: u8,
    /// reserved field, should be 0b00 when writing and 0b11 when reading
    #[bits(2, default = 3)]
    _reserved: u8,
    /// the Daisy Chain Timing field (DC)
    #[bits(2, default = 0)]
    pub daisy_chain_timing: u8,
}

/// the Local Address register
#[bitfield(u8)]
#[derive(Copy, Clone)]
pub struct LocalAddress {
    #[bits(4)]
    pub base: u8,
    #[bits(4)]
    pub match_enable: u8,
}

impl LocalAddress {
    /// tests the high 4 bits of an address against the contents of this register,
    /// returning true if a local bus access should be performed and false if a global bus access should be performed
    pub fn is_local_bus_access(&self, high_4_bits: u8) -> bool {
        let match_enable = self.match_enable();
        self.base() & match_enable == high_4_bits & match_enable
    }
}

#[bitfield(u8)]
#[derive(Copy, Clone)]
pub struct CacheControl {
    #[bits(3, default = 0)]
    _zero: u8,
    /// the High Memory Burst Capability (HMB) bit
    #[bits(default = false)]
    pub high_memory_burst_capability: bool,
    /// the Low Memory Burst Capability (LMB) bit
    #[bits(default = false)]
    pub low_memory_burst_capability: bool,
    /// the Cache Data Disable (D) bit.
    /// disables the data cache if set to true
    #[bits(default = true)]
    pub cache_data_disable: bool,
    /// the Cache Instruction Disable (I) bit.
    /// disables the instruction cache if set to true
    #[bits(default = false)]
    pub cache_instruction_disable: bool,
    /// the Memory/Cache (M/C) bit.
    /// if this is set to true, the on-chip cache can be accessed as regular memory. if set to false, it's used as cache
    #[bits(1, default = MemoryCacheBit::Cache)]
    pub memory_cache_bit: MemoryCacheBit,
}

#[derive(Copy, Clone, Debug, Default)]
pub enum MemoryCacheBit {
    #[default]
    Cache,
    Memory,
}

impl MemoryCacheBit {
    pub const fn from_bits(bits: u8) -> Self {
        match bits {
            0 => Self::Cache,
            1 => Self::Memory,
            _ => panic!("invalid input to MemoryCacheBit::from_bits()"),
        }
    }

    pub const fn into_bits(self) -> u8 {
        match self {
            Self::Cache => 0,
            Self::Memory => 1,
        }
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct SystemStatusRegisters {
    /// the Master Status register
    pub master_status: MasterStatus,
    /// the Interrupt Status register
    pub interrupt_status: InterruptStatus,
    /// the Interrupt/Trap Vector Table Pointer register.
    /// the 4 least significant bits of this register must be set to 0,
    /// the other 12 bits define the 12 most significant bits of the address of the Interrupt/Trap Vector Table
    pub interrupt_trap_vector_table_pointer: u16,
    /// the I/O Page register.
    /// this contains the 8 most significant bits of emitted 24 bit I/O addresses
    pub io_page: u8,
    /// the Trap Control register
    pub trap_control: TrapControl,
    /// the System Stack Limit register.
    /// a System Stack Overflow Warning trap is generated if the 12 most significant bits of this register match the 12 most significant bits of the System Stack Pointer
    /// and if the System Stack Overflow Warning bit in the Trap Control register is set.
    /// the 4 least significant bits of this register must be set to 0
    pub system_stack_limit: u16,
}

#[bitfield(u16)]
#[derive(Copy, Clone)]
pub struct MasterStatus {
    /// the Interrupt Request Enable (E) bits
    #[bits(7, default = 0)]
    pub irq_enable: u8,
    #[bits(1, default = 0)]
    _zero: u8,
    /// the Single-Step (SS) bit
    #[bits(default = false)]
    pub single_step: bool,
    /// the Single-Step Pending (SSP) bit
    #[bits(default = false)]
    pub single_step_pending: bool,
    #[bits(2, default = 0)]
    pub _zero: u8,
    /// the Breakpoint-on-Halt Enable (BH) bit
    #[bits(default = false)]
    pub breakpoint_on_halt_enable: bool,
    #[bits(1, default = 0)]
    pub _zero: u8,
    /// the User/System (U/S) bit
    #[bits(1, default = UserSystemBit::System)]
    pub user_system_bit: UserSystemBit,
    #[bits(1, default = 0)]
    pub _zero: u8,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub enum UserSystemBit {
    #[default]
    System,
    User,
}

impl UserSystemBit {
    pub const fn from_bits(bits: u8) -> Self {
        match bits {
            0 => Self::System,
            1 => Self::User,
            _ => panic!("invalid input to UserSystemBit::from_bits()"),
        }
    }

    pub const fn into_bits(self) -> u8 {
        match self {
            Self::System => 0,
            Self::User => 1,
        }
    }

    pub const fn stack_pointer_index(&self) -> usize {
        match self {
            Self::System => 0,
            Self::User => 1,
        }
    }
}

#[bitfield(u16)]
#[derive(Copy, Clone)]
pub struct InterruptStatus {
    /// the Interrupt Request Pending (IP) bits
    #[bits(7, default = 0)]
    pub irq_pending: u8,
    #[bits(1, default = 0)]
    _zero: u8,
    /// the Interrupt Mode (IM) field
    #[bits(2, default = InterruptMode::Mode0)]
    pub interrupt_mode: InterruptMode,
    #[bits(2, default = 0)]
    _zero: u8,
    /// the Interrupt Vector Enable (I) bit for the NMI vector line
    #[bits(default = false)]
    pub nmi_vector_enable: bool,
    /// the Interrupt Vector Enable (I) bit for the A vector line
    #[bits(default = false)]
    pub a_vector_enable: bool,
    /// the Interrupt Vector Enable (I) bit for the B vector line
    #[bits(default = false)]
    pub b_vector_enable: bool,
    /// the Interrupt Vector Enable (I) bit for the C vector line
    #[bits(default = false)]
    pub c_vector_enable: bool,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum InterruptMode {
    Mode0,
    Mode1,
    Mode2,
    Mode3,
}

impl InterruptMode {
    pub const fn from_bits(bits: u8) -> Self {
        match bits {
            0 => Self::Mode0,
            1 => Self::Mode1,
            2 => Self::Mode2,
            3 => Self::Mode3,
            _ => panic!("invalid input to InterruptMode::from_bits()"),
        }
    }

    pub const fn into_bits(self) -> u8 {
        match self {
            Self::Mode0 => 0,
            Self::Mode1 => 1,
            Self::Mode2 => 2,
            Self::Mode3 => 3,
        }
    }
}

#[bitfield(u8)]
#[derive(Copy, Clone)]
pub struct TrapControl {
    /// the System Stack Overflow Warning (S) bit
    pub system_stack_overflow_warning: bool,
    /// the EPU Enable (E) bit
    pub epu_enable: bool,
    /// the Inhibit User I/O (I) bit
    pub inhibit_user_io: bool,
    #[bits(5, default = 0)]
    _zero: u8,
}
