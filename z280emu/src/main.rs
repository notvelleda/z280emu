pub mod instruction_decoding;
pub mod registers;

use std::io::Write;

use log::info;
use instruction_decoding::{Memory, Register, RegisterOrMemoryAccessor};

pub struct CPUState<T: BusAccessor + 'static> {
    pub register_file: registers::RegisterFile,
    pub control_registers: registers::ControlRegisters,
    pub system_status_registers: registers::SystemStatusRegisters,
    pub bus_accessor: T,
    //pub instruction_decoder: instruction_decoding::InstructionDecoder<T>,
}

impl<T: BusAccessor> CPUState<T> {
    pub fn new(bus_accessor: T) -> Self {
        Self {
            register_file: registers::RegisterFile::default(),
            control_registers: registers::ControlRegisters::default(),
            system_status_registers: registers::SystemStatusRegisters::default(),
            bus_accessor,
            //instruction_decoder: instruction_decoding::InstructionDecoder::default(),
        }
    }

    pub fn single_step(&mut self) {
        //self.instruction_decoder.decode_instruction(self);
    }
}

pub trait BusAccessor {
    /// reads data from memory. the upper 8 bits of the address are unused
    fn read(&self, address_space: BusAddressSpace, address: u32, data: &mut [u8]);

    /// writes data to memory. the upper 8 bits of the address are unused
    fn write(&mut self, address_space: BusAddressSpace, address: u32, data: &[u8]);
}

#[derive(Copy, Clone, Debug)]
pub enum BusAddressSpace {
    Memory,
    IO,
}

struct SimpleBusAccessor {
    memory: Box<[u8]>,
}

impl BusAccessor for SimpleBusAccessor {
    fn read(&self, address_space: BusAddressSpace, address: u32, data: &mut [u8]) {
        match address_space {
            BusAddressSpace::Memory => data.copy_from_slice(&self.memory[address as usize..address as usize + data.len()]),
            BusAddressSpace::IO => {
                info!("read {} bytes from IO at address {address:#x}", data.len());
                data.fill(0);
            }
        }
    }

    fn write(&mut self, address_space: BusAddressSpace, address: u32, data: &[u8]) {
        match address_space {
            BusAddressSpace::Memory => self.memory[address as usize..address as usize + data.len()].copy_from_slice(data),
            BusAddressSpace::IO => {
                match address {
                    1 => std::io::stdout().write_all(data).unwrap(),
                    _ => info!("wrote to IO at address {address:#x} with data {data:?}"),
                }
            },
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
    (lhs ^ rhs ^ (lhs.wrapping_add(rhs))) & 0x10 != 0
}

pub fn calculate_half_carry_u16(lhs: u16, rhs: u16) -> bool {
    (lhs ^ rhs ^ (lhs.wrapping_add(rhs))) & 0x0100 != 0
}

// is this correct?
pub fn calculate_carry_u8(lhs: u8, rhs: u8) -> bool {
    (lhs ^ rhs ^ (lhs.wrapping_add(rhs))) & 0x80 != 0
}

pub fn calculate_carry_u16(lhs: u16, rhs: u16) -> bool {
    (lhs ^ rhs ^ (lhs.wrapping_add(rhs))) & 0x8000 != 0
}

// TODO: system stack overflow warning trap
pub fn push<T: BusAccessor>(cpu_state: &mut CPUState<T>, value: u16) {
    let sp: u16 = Register::SP.get(cpu_state);
    let sp = sp.wrapping_sub(2);
    Register::SP.set(cpu_state, sp);

    Memory { address: sp }.set(cpu_state, value);
}

pub fn pop<T: BusAccessor>(cpu_state: &mut CPUState<T>) -> u16 {
    let sp: u16 = Register::SP.get(cpu_state);
    let new_sp = sp.wrapping_add(2);
    Register::SP.set(cpu_state, new_sp);

    Memory { address: sp }.get(cpu_state)
}

pub fn calculate_io_address<T: BusAccessor>(cpu_state: &mut CPUState<T>, low_byte: u8) -> u32 {
    let b_register: u8 = Register::B.get(cpu_state);
    (low_byte as u32) | ((b_register as u32) << 8) | ((cpu_state.system_status_registers.io_page as u32) << 16)
}

fn main() {
    env_logger::init();

    let time = std::time::Instant::now();
    let decoder = instruction_decoding::InstructionDecoder::default();
    info!("initialized tables in {:?}", time.elapsed());

    // adapted from https://github.com/skx/z80-examples/blob/03ef9c1a77a2ee9429b6877bfb990d11e5c1acf0/string-output.z80
    let program = [
        // CALL 0010H
        0b11_001_101,
        16,
        0,
        // Hellorld!\r\n
        b'H',
        b'e',
        b'l',
        b'l',
        b'o',
        b'r',
        b'l',
        b'd',
        b'!',
        b'\r',
        b'\n',
        0,
        // HALT
        0b01_110_110,
        // POP HL
        0b11_100_001,
        // LD A, (HL)
        0b01_111_110,
        // INC HL
        0b00_100_011,
        // PUSH HL
        0b11_100_101,
        // CP A, 0
        0b11_111_110,
        0,
        // RET Z
        0b11_001_000,
        // OUT (1), A
        0b11_010_011,
        1,
        // JP 0010H
        0b11_000_011,
        16,
        0,
    ];

    let bus_accessor = SimpleBusAccessor {
        memory: vec![0; 65536].into_boxed_slice(),
    };
    let mut cpu_state = CPUState::new(bus_accessor);

    cpu_state.bus_accessor.memory[..program.len()].clone_from_slice(&program);
    *cpu_state.register_file.current_stack_pointer_mut() = 0xffff;

    loop {
        decoder.decode_instruction(&mut cpu_state);
    }
}
