pub mod instruction_decoding;
pub mod registers;

use std::io::{Read, Write};

use instruction_decoding::{Memory, Register, RegisterOrMemoryAccessor};
use log::info;

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
            BusAddressSpace::IO => match address & 0xff {
                1 => {
                    let _ = std::io::stdout().flush();
                    std::io::stdin().read_exact(data).unwrap();
                }
                _ => {
                    info!("read {} bytes from IO at address {address:#x}", data.len());
                    data.fill(0);
                }
            },
        }
    }

    fn write(&mut self, address_space: BusAddressSpace, address: u32, data: &[u8]) {
        match address_space {
            BusAddressSpace::Memory => self.memory[address as usize..address as usize + data.len()].copy_from_slice(data),
            BusAddressSpace::IO => match address & 0xff {
                1 => std::io::stdout().write_all(data).unwrap(),
                _ => info!("wrote to IO at address {address:#x} with data {data:?}"),
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
    (lhs ^ rhs ^ (lhs.wrapping_add(rhs))) & (1 << 4) != 0
}

pub fn calculate_half_carry_u16(lhs: u16, rhs: u16) -> bool {
    (lhs ^ rhs ^ (lhs.wrapping_add(rhs))) & (1 << 8) != 0
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

pub fn calculate_io_address<T: BusAccessor>(cpu_state: &mut CPUState<T>, low_byte: u8, middle_byte: Register) -> u32 {
    let middle_byte: u8 = middle_byte.get(cpu_state);
    (low_byte as u32) | ((middle_byte as u32) << 8) | ((cpu_state.system_status_registers.io_page as u32) << 16)
}

fn main() {
    env_logger::init();

    let time = std::time::Instant::now();
    let decoder = instruction_decoding::InstructionDecoder::default();
    info!("initialized tables in {:?}", time.elapsed());

    let bus_accessor = SimpleBusAccessor {
        memory: vec![0; 65536].into_boxed_slice(),
    };
    let mut cpu_state = CPUState::new(bus_accessor);

    let program = std::fs::read(std::env::args().nth(1).expect("expected program to execute as an argument")).unwrap();

    cpu_state.bus_accessor.memory[..program.len()].clone_from_slice(&program);
    *cpu_state.register_file.current_stack_pointer_mut() = 0xffff;

    loop {
        decoder.decode_instruction(&mut cpu_state);
    }
}
