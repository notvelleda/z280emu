use crate::{BusAccessor, helpers::Trap, registers::UserSystemBit};
use bitfields::bitfield;

pub struct MMU<T: BusAccessor> {
    pub external_bus: T,
    pub user_page_descriptor_table: [PageDescriptor; 16],
    pub system_page_descriptor_table: [PageDescriptor; 16],
    pub master_control_register: MasterControl,
    pub page_descriptor_register_pointer: u8,
}

impl<T: BusAccessor> MMU<T> {
    pub fn new(bus_accessor: T) -> Self {
        Self {
            external_bus: bus_accessor,
            user_page_descriptor_table: Default::default(),
            system_page_descriptor_table: Default::default(),
            master_control_register: MasterControl::default(),
            page_descriptor_register_pointer: 0,
        }
    }

    /// gets a reference to one of the page descriptor tables based on whether the CPU is in system or user mode
    pub fn get_page_descriptor_table(&self, user_system_bit: UserSystemBit) -> &[PageDescriptor] {
        match user_system_bit {
            UserSystemBit::System => &self.system_page_descriptor_table,
            UserSystemBit::User => &self.user_page_descriptor_table,
        }
    }

    /// gets a mutable reference to one of the page descriptor tables based on whether the CPU is in system or user mode
    pub fn get_page_descriptor_table_mut(&mut self, user_system_bit: UserSystemBit) -> &mut [PageDescriptor] {
        match user_system_bit {
            UserSystemBit::System => &mut self.system_page_descriptor_table,
            UserSystemBit::User => &mut self.user_page_descriptor_table,
        }
    }

    /// checks whether address translation is enabled based on whether the CPU is in system or user mode
    pub fn is_translation_enabled(&self, user_system_bit: UserSystemBit) -> bool {
        match user_system_bit {
            UserSystemBit::System => self.master_control_register.system_mode_translation_enabled(),
            UserSystemBit::User => self.master_control_register.user_mode_translation_enabled(),
        }
    }

    /// checks whether address translation is split between program and data address spaces based on whether the CPU is in system or user mode
    pub fn is_access_separated(&self, user_system_bit: UserSystemBit) -> bool {
        match user_system_bit {
            UserSystemBit::System => self.master_control_register.system_mode_separation(),
            UserSystemBit::User => self.master_control_register.user_mode_separation(),
        }
    }

    /// used to set the PFI field and return an error if reading from or writing to this page would be invalid
    fn check_is_page_access_valid(&mut self, page: &PageDescriptor, page_index: usize, user_system_bit: UserSystemBit, is_writing: bool) -> Result<(), MMUError> {
        if !page.is_valid() || (is_writing && page.is_write_protected()) {
            match user_system_bit {
                UserSystemBit::User => self.master_control_register.set_page_fault_identifier(page_index as u8),
                UserSystemBit::System => self.master_control_register.set_page_fault_identifier((1 << 5) | page_index as u8),
            }

            Err(MMUError {
                wp_bit_used: page.is_write_protected(),
                valid_bit_used: page.is_valid(),
            })
        } else {
            Ok(())
        }
    }

    /// calculates the offset into the page to be used for the given address
    fn get_offset_in_page(&self, user_system_bit: UserSystemBit, address: u16) -> u16 {
        if self.is_access_separated(user_system_bit) {
            // pages are 8K in size when I/D separation is enabled
            address & 8191
        } else {
            address & 4095
        }
    }

    /// calculates the index to be used when looking up a page in a page table by its address
    fn get_page_table_index(&self, user_system_bit: UserSystemBit, access_type: AccessType, address: u16) -> usize {
        if self.is_access_separated(user_system_bit) {
            (access_type.as_page_descriptor_table_index_msb() << 3) | (address >> 13) as usize
        } else {
            (address >> 12) as usize
        }
    }

    /// reads from memory, translating the given logical address to its physical address counterpart
    pub fn read_memory(&mut self, user_system_bit: UserSystemBit, access_type: AccessType, address: u16, data: &mut [u8]) -> Result<(), MMUError> {
        // handles accesses wrapping around from the highest to lowest addresses
        if address as usize + data.len() > u16::MAX as usize {
            self.read_memory(user_system_bit, access_type, address, &mut data[..(u16::MAX - address) as usize])?;
            return self.read_memory(user_system_bit, access_type, 0, &mut data[(u16::MAX - address) as usize..]);
        }

        if !self.is_translation_enabled(user_system_bit) {
            self.external_bus.read(crate::BusAddressSpace::Memory, u32::from(address), data);
            return Ok(());
        }

        let offset = self.get_offset_in_page(user_system_bit, address);

        // handles accesses across page boundaries
        if self.is_access_separated(user_system_bit) && offset as usize + data.len() > 8191 {
            self.read_memory(user_system_bit, access_type, address, &mut data[..8191 - offset as usize])?;
            return self.read_memory(user_system_bit, access_type, (address & !8191) + 8192, &mut data[8191 - offset as usize..]);
        } else if !self.is_access_separated(user_system_bit) && offset as usize + data.len() > 4095 {
            self.read_memory(user_system_bit, access_type, address, &mut data[..4095 - offset as usize])?;
            return self.read_memory(user_system_bit, access_type, (address & !4095) + 4096, &mut data[4095 - offset as usize..]);
        }

        let index = self.get_page_table_index(user_system_bit, access_type, address);
        let page = self.get_page_descriptor_table(user_system_bit)[index];
        let full_address = (u32::from(page.page_frame_address()) << 8) | u32::from(offset);

        self.check_is_page_access_valid(&page, index, user_system_bit, false)?;
        self.external_bus.read(crate::BusAddressSpace::Memory, full_address, data);
        Ok(())
    }

    /// writes to memory, translating the given logical address to its physical address counterpart
    pub fn write_memory(&mut self, user_system_bit: UserSystemBit, access_type: AccessType, address: u16, data: &[u8]) -> Result<(), MMUError> {
        // handles accesses wrapping around from the highest to lowest addresses
        if address as usize + data.len() > u16::MAX as usize {
            self.write_memory(user_system_bit, access_type, address, &data[..(u16::MAX - address) as usize])?;
            return self.write_memory(user_system_bit, access_type, 0, &data[(u16::MAX - address) as usize..]);
        }

        if !self.is_translation_enabled(user_system_bit) {
            self.external_bus.write(crate::BusAddressSpace::Memory, u32::from(address), data);
            return Ok(());
        }

        let offset = self.get_offset_in_page(user_system_bit, address);

        // handles accesses across page boundaries
        if self.is_access_separated(user_system_bit) && offset as usize + data.len() > 8191 {
            self.write_memory(user_system_bit, access_type, address, &data[..8191 - offset as usize])?;
            return self.write_memory(user_system_bit, access_type, (address & !8191) + 8192, &data[8191 - offset as usize..]);
        } else if !self.is_access_separated(user_system_bit) && offset as usize + data.len() > 4095 {
            self.write_memory(user_system_bit, access_type, address, &data[..4095 - offset as usize])?;
            return self.write_memory(user_system_bit, access_type, (address & !4095) + 4096, &data[4095 - offset as usize..]);
        }

        let index = self.get_page_table_index(user_system_bit, access_type, address);
        let page = self.get_page_descriptor_table(user_system_bit)[index];
        let full_address = (u32::from(page.page_frame_address()) << 8) | u32::from(offset);

        self.check_is_page_access_valid(&page, index, user_system_bit, true)?;
        self.get_page_descriptor_table_mut(user_system_bit)[index].set_was_modified(true);
        self.external_bus.write(crate::BusAddressSpace::Memory, full_address, data);
        Ok(())
    }

    /// gets a reference to the page descriptor pointed to by the current value of the page descriptor reference pointer
    pub fn get_current_page_descriptor(&self) -> &PageDescriptor {
        let index = (self.page_descriptor_register_pointer & 15) as usize;

        match (self.page_descriptor_register_pointer >> 4) & 1 {
            0 => &self.user_page_descriptor_table[index],
            1 => &self.system_page_descriptor_table[index],
            _ => unreachable!(),
        }
    }

    /// gets a mutable reference to the page descriptor pointed to by the current value of the page descriptor reference pointer
    pub fn get_current_page_descriptor_mut(&mut self) -> &mut PageDescriptor {
        let index = (self.page_descriptor_register_pointer & 15) as usize;

        match (self.page_descriptor_register_pointer >> 4) & 1 {
            0 => &mut self.user_page_descriptor_table[index],
            1 => &mut self.system_page_descriptor_table[index],
            _ => unreachable!(),
        }
    }

    /// reads from IO with the control registers for the MMU overlaid
    pub fn read_io(&mut self, address: u32, data: &mut [u8]) {
        match address & 0xff00ff {
            // master control register
            0xff00f0 => {
                let slice_size = data.len().min(2);
                data[..slice_size].clone_from_slice(&self.master_control_register.into_bits().to_le_bytes()[..slice_size]);
            }
            // page descriptor register pointer
            0xff00f1 => {
                data[0] = self.page_descriptor_register_pointer;
                data[1..].fill(0);
            }
            // descriptor select port, block move port
            0xff00f5 | 0xff00f4 => {
                let slice_size = data.len().min(2);
                data[..slice_size].clone_from_slice(&self.get_current_page_descriptor().into_bits().to_le_bytes()[..slice_size]);

                if address & 0xff == 0xf4 {
                    self.page_descriptor_register_pointer = self.page_descriptor_register_pointer.wrapping_add(1);
                }
            }
            // invalidation port
            0xff00f2 => data.fill(0),
            _ => self.external_bus.read(crate::BusAddressSpace::IO, address, data),
        }
    }

    /// writes to IO with the control registers for the MMU overlaid
    pub fn write_io(&mut self, address: u32, data: &[u8]) {
        match address & 0xff00ff {
            // master control register
            0xff00f0 => {
                let value = if data.len() == 1 { u16::from(data[0]) } else { u16::from_le_bytes([data[0], data[1]]) };
                self.master_control_register = MasterControl::from_bits(value);
            }
            // page descriptor register pointer
            0xff00f1 => self.page_descriptor_register_pointer = data[0],
            // descriptor select port, block move port
            0xff00f5 | 0xff00f4 => {
                let value = if data.len() == 1 { u16::from(data[0]) } else { u16::from_le_bytes([data[0], data[1]]) };
                *self.get_current_page_descriptor_mut() = PageDescriptor::from_bits(value);

                if address & 0xff == 0xf4 {
                    self.page_descriptor_register_pointer = self.page_descriptor_register_pointer.wrapping_add(1);
                }
            }
            // invalidation port
            0xff00f2 => {
                if data[0] & (1 << 0) != 0 {
                    for descriptor in self.get_page_descriptor_table_mut(UserSystemBit::System).iter_mut().take(8) {
                        descriptor.set_is_valid(false);
                    }
                }

                if data[0] & (1 << 1) != 0 {
                    for descriptor in self.get_page_descriptor_table_mut(UserSystemBit::System).iter_mut().skip(8).take(8) {
                        descriptor.set_is_valid(false);
                    }
                }

                if data[0] & (1 << 2) != 0 {
                    for descriptor in self.get_page_descriptor_table_mut(UserSystemBit::User).iter_mut().take(8) {
                        descriptor.set_is_valid(false);
                    }
                }

                if data[0] & (1 << 3) != 0 {
                    for descriptor in self.get_page_descriptor_table_mut(UserSystemBit::User).iter_mut().skip(8).take(8) {
                        descriptor.set_is_valid(false);
                    }
                }
            }
            _ => self.external_bus.write(crate::BusAddressSpace::IO, address, data),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AccessType {
    Data,
    Program,
}

impl AccessType {
    pub fn as_page_descriptor_table_index_msb(&self) -> usize {
        match self {
            Self::Data => 0,
            Self::Program => 1,
        }
    }
}

/// this error type is used so that LDUD/LDUP instructions can access the WP and V bit states as needed
#[derive(Copy, Clone, Debug)]
pub struct MMUError {
    pub wp_bit_used: bool,
    pub valid_bit_used: bool,
}

impl From<MMUError> for Trap {
    fn from(_value: MMUError) -> Self {
        Self::AccessViolation
    }
}

#[bitfield(u16)]
#[derive(Copy, Clone)]
pub struct PageDescriptor {
    /// the Modified bit (M)
    pub was_modified: bool,
    /// the Cacheable bit (C)
    pub is_cacheable: bool,
    /// the Write-Protect bit (WP)
    pub is_write_protected: bool,
    /// the Valid bit (V)
    pub is_valid: bool,
    /// the 11 or 12 most significant bits of the page frame address
    #[bits(12)]
    pub page_frame_address: u16,
}

#[bitfield(u16)]
#[derive(Copy, Clone)]
pub struct MasterControl {
    /// the Page Fault Identifier (PFI) field
    #[bits(5)]
    pub page_fault_identifier: u8,
    #[bits(5, default = 31)]
    _one: u8,
    /// the System Mode Program/Data Separation Enable (SPD) bit
    pub system_mode_separation: bool,
    /// the System Mode Translate Enable (STE) bit
    pub system_mode_translation_enabled: bool,
    #[bits(2, default = 3)]
    _one: u8,
    /// the User Mode Program/Data Separation Enable (UPD) bit
    pub user_mode_separation: bool,
    /// the User Mode Translate Enable (UTE) bit
    pub user_mode_translation_enabled: bool,
}
