pub mod helpers;
pub mod instruction_decoding;
pub mod registers;

use log::{info, warn};
use std::io::{Read, Write};

pub struct CPUState<T: BusAccessor + 'static> {
    pub register_file: registers::RegisterFile,
    pub control_registers: registers::ControlRegisters,
    pub system_status_registers: registers::SystemStatusRegisters,
    pub interrupt_shadow_register: u8,
    pub bus_accessor: T,
    //pub instruction_decoder: instruction_decoding::InstructionDecoder<T>,
}

impl<T: BusAccessor> CPUState<T> {
    pub fn new(bus_accessor: T) -> Self {
        Self {
            register_file: registers::RegisterFile::default(),
            control_registers: registers::ControlRegisters::default(),
            system_status_registers: registers::SystemStatusRegisters::default(),
            interrupt_shadow_register: 0,
            bus_accessor,
            //instruction_decoder: instruction_decoding::InstructionDecoder::default(),
        }
    }

    /// gets the value of a control register based on its address
    pub fn load_register_by_address(&self, address: u8) -> u16 {
        match address {
            0x00 => self.system_status_registers.master_status.into_bits(),
            0x16 => self.system_status_registers.interrupt_status.into_bits(),
            0x06 => self.system_status_registers.interrupt_trap_vector_table_pointer,
            0x08 => u16::from(self.system_status_registers.io_page),
            0x10 => u16::from(self.system_status_registers.trap_control.into_bits()),
            0x04 => self.system_status_registers.system_stack_limit,
            0x02 => u16::from(self.control_registers.bus_timing_and_control.into_bits()),
            0xff => u16::from(self.control_registers.bus_timing_and_initialization.into_bits()),
            0x14 => u16::from(self.control_registers.local_address.into_bits()),
            0x12 => u16::from(self.control_registers.cache_control.into_bits()),
            _ => {
                warn!("attempted to read from invalid control register {address:#x}");
                0
            }
        }
    }

    /// sets the bits of a control register based on its address
    pub fn store_register_by_address(&mut self, address: u8, value: u16) {
        match address {
            0x00 => self.system_status_registers.master_status = registers::MasterStatus::from_bits(value),
            0x16 => self.system_status_registers.interrupt_status = registers::InterruptStatus::from_bits(value),
            0x06 => self.system_status_registers.interrupt_trap_vector_table_pointer = value,
            0x08 => self.system_status_registers.io_page = value as u8,
            0x10 => self.system_status_registers.trap_control = registers::TrapControl::from_bits(value as u8),
            0x04 => self.system_status_registers.system_stack_limit = value & !15,
            0x02 => self.control_registers.bus_timing_and_control = registers::BusTimingAndControl::from_bits(value as u8),
            0xff => self.control_registers.bus_timing_and_initialization = registers::BusTimingAndInitialization::from_bits(value as u8),
            0x14 => self.control_registers.local_address = registers::LocalAddress::from_bits(value as u8),
            0x12 => self.control_registers.cache_control = registers::CacheControl::from_bits(value as u8),
            _ => warn!("attempted to write to invalid control register {address:#x}"),
        }
    }

    pub fn handle_trap(&mut self, trap: helpers::Trap, old_pc_value: u16) {
        if !trap.should_push_next_instruction_address() {
            self.system_status_registers.master_status.set_single_step_pending(false);
        }

        let pc = self.register_file.pc;
        let msr = self.system_status_registers.master_status.into_bits();

        // forces the system stack to be used while pushing data for this trap regardless of the MSR that will be loaded
        self.system_status_registers.master_status.set_user_system_bit(registers::UserSystemBit::System);

        if trap.should_push_next_instruction_address() {
            helpers::push(self, pc);
        } else {
            helpers::push(self, old_pc_value);
        }

        helpers::push(self, msr);
        trap.push_extra_data(self);

        let full_address = (u32::from(self.system_status_registers.interrupt_trap_vector_table_pointer & !15) << 8) + trap.vector_table_offset();
        let mut bytes = [0; 4];

        self.bus_accessor.read(BusAddressSpace::Memory, full_address, &mut bytes);

        self.system_status_registers.master_status = registers::MasterStatus::from_bits(u16::from_le_bytes(bytes[0..2].try_into().unwrap()));
        self.register_file.pc = u16::from_le_bytes(bytes[2..4].try_into().unwrap());
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
    cpu_state.register_file.stack_pointers[registers::UserSystemBit::System.stack_pointer_index()] = 0xffff;

    loop {
        if cpu_state.system_status_registers.master_status.single_step_pending() {
            cpu_state.system_status_registers.master_status.set_single_step_pending(false);
            cpu_state.handle_trap(helpers::Trap::SingleStep, cpu_state.register_file.pc);

            continue;
        }

        let old_pc_value = cpu_state.register_file.pc;
        let msr = &mut cpu_state.system_status_registers.master_status;
        msr.set_single_step_pending(msr.single_step());

        if let Err(trap) = decoder.decode_instruction(&mut cpu_state) {
            cpu_state.handle_trap(trap, old_pc_value);

            // TODO: is this the correct behavior?
            if trap != helpers::Trap::SystemStackOverflowWarning
                && let Err(new_trap) = helpers::system_stack_overflow_check(&mut cpu_state, true)
            {
                cpu_state.handle_trap(new_trap, cpu_state.register_file.pc);
            }
        }
    }
}
