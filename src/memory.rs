use crate::VM;
use crate::instructions::Registers::*;
use std::fs::File;
use std::io::{self, Read};

pub const MAX_MEMORY: usize = 1 << 16;

pub const MR_KBSR: usize = 0xFE00;
pub const MR_KBDR: usize = 0xFE02;

pub fn read_image(path: &str, vm: &mut VM) -> io::Result<()> {
    let mut file = File::open(path)?;

    let mut origin_bytes = [0u8; 2];
    file.read_exact(&mut origin_bytes)?;
    let origin = u16::from_be_bytes(origin_bytes) as usize;

    vm.registers[PC as usize] = origin as u16;

    read_image_file(&mut file, &mut vm.memory, origin)
}

fn read_image_file(
    reader: &mut impl Read,
    memory: &mut [u16; MAX_MEMORY],
    origin: usize,
) -> io::Result<()> {
    let max_read = MAX_MEMORY - origin;

    for i in 0..max_read {
        let mut word = [0u8; 2];
        match reader.read_exact(&mut word) {
            Ok(_) => {
                memory[origin + i] = u16::from_be_bytes(word);
            }
            Err(ref e) if e.kind() == io::ErrorKind::UnexpectedEof => {
                break;
            }
            Err(e) => return Err(e),
        }
    }
    return Ok(());
}

impl VM {
    pub fn mem_write(&mut self, address: u16, value: u16) {
        let index = address as usize;
        self.memory[index] = value;
    }
    pub fn mem_read(&mut self, address: u16) -> u16 {
        let index = address as usize;
        if index == MR_KBSR {
            if let Some(key) = self.keyboard.check_key() {
                self.memory[MR_KBSR] = 1 << 15;
                self.memory[MR_KBDR] = key;
            }
        } else if index == MR_KBDR {
            self.memory[MR_KBSR] = 0;
        }
        return self.memory[index];
    }
}

#[cfg(test)]
mod tests {
    use super::*;
        #[test]
        fn read_image_file_decodes_big_endian() {
            let mut memory = [0u16; MAX_MEMORY];
            let mut data: &[u8] = &[0x12, 0x34, 0xAB, 0xCD]; 
            read_image_file(&mut data, &mut memory, 0x3000).unwrap();
            assert_eq!(memory[0x3000], 0x1234);
            assert_eq!(memory[0x3001], 0xABCD);
        }
        #[test]
        fn read_image_file_stops_at_eof() {
            let mut memory = [0u16; MAX_MEMORY];
            let mut data: &[u8] = &[0xFF, 0xEE]; 
            read_image_file(&mut data, &mut memory, 0x3000).unwrap();
            assert_eq!(memory[0x3000], 0xFFEE);
            assert_eq!(memory[0x3001], 0x0000); 
        }
        #[test]
        fn read_image_file_prevents_memory_overflow() {
            let mut memory = [0u16; MAX_MEMORY];
            let mut data: &[u8] = &[0xAA, 0xBB, 0xCC, 0xDD];
            read_image_file(&mut data, &mut memory, 0xFFFF).unwrap();
            assert_eq!(memory[0xFFFF], 0xAABB);
        }
        #[test]
        fn mem_write_stores_value_at_address() {
            let mut vm = VM::new();
            vm.mem_write(0x3000, 42);
            assert_eq!(vm.memory[0x3000], 42);
        }
        #[test]
        fn mem_write_overwrites_previous_value() {
            let mut vm = VM::new();
            vm.mem_write(0x3000, 42);
            vm.mem_write(0x3000, 99);
            assert_eq!(vm.memory[0x3000], 99);
        }
        #[test]
        fn mem_write_highest_address() {
            let mut vm = VM::new();
            vm.mem_write(0xFFFF, 42);
            assert_eq!(vm.memory[0xFFFF], 42);
        }
        #[test]
        fn mem_read_returns_stored_value() {
            let mut vm = VM::new();
            vm.memory[0x3000] = 42;
            let value = vm.mem_read(0x3000);
            assert_eq!(value, 42);
        }
        #[test]
        fn reading_kbdr_clears_kbsr() {
            let mut vm = VM::new();
            vm.memory[MR_KBSR] = 1 << 15;
            vm.memory[MR_KBDR] = 0x0041;
            let _ = vm.mem_read(MR_KBDR as u16);
            assert_eq!(vm.memory[MR_KBSR], 0);
        }
        #[test]
        fn standard_read_does_not_clear_kbsr() {
            let mut vm = VM::new();
            vm.memory[MR_KBSR] = 1 << 15;
            vm.memory[0x3000] = 42;
            let _ = vm.mem_read(0x3000);
            assert_eq!(vm.memory[MR_KBSR], 1 << 15);
        }
}