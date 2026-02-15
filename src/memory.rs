use crate::VM;
use std::fs::File;
use std::io::{self, Read};

pub const MAX_MEMORY: usize = 1 << 16;

pub const MR_KBSR: usize = 0xFE00;
pub const MR_KBDR: usize = 0xFE02;

pub fn read_image(path: &str, vm: &mut VM) -> io::Result<()> {
    let mut file = File::open(path)?;
    read_image_file(&mut file, &mut vm.memory)
}

fn read_image_file(file: &mut File, memory: &mut [u16; MAX_MEMORY]) -> io::Result<()> {
    let mut origin = [0u8; 2];
    file.read_exact(&mut origin)?;
    let origin = u16::from_be_bytes(origin) as usize;

    let max_read = MAX_MEMORY - origin;

    for i in 0..max_read {
        let mut word = [0u8; 2];
        match file.read_exact(&mut word) {
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
        } else {
            self.memory[MR_KBSR] = 0;
        }
        return self.memory[index];
    }
}
