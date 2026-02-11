use log::info;

pub mod instruction_decoding;
pub mod registers;

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
            BusAddressSpace::IO => info!("wrote to IO at address {address:#x} with data {data:?}"),
        }
    }
}

fn main() {
    env_logger::init();

    let time = std::time::Instant::now();
    let decoder = instruction_decoding::InstructionDecoder::default();
    info!("initialized tables in {:?}", time.elapsed());

    let bus_accessor = SimpleBusAccessor {
        memory: vec![
            // ld hl, output
            0b00_100_001,
            9,
            0,
            // xor a, a
            0b10_101_111,
            // inc a
            0b00_111_100,
            // ld (hl), a
            0b01_110_111,
            // jp loop
            0b11_000_011,
            4,
            0,
            // output
            0,
        ]
        .into_boxed_slice(),
    };
    let mut cpu_state = CPUState::new(bus_accessor);

    for _i in 0..5 {
        decoder.decode_instruction(&mut cpu_state);
    }
}
