use crate::Keyboard;
use std::fs::File;
use std::io::{self, Read};

pub const MAX_MEMORY: usize = 1 << 16;

pub const MR_KBSR: usize = 0xFE00;
pub const MR_KBDR: usize = 0xFE02;

pub fn read_image(path: &str, memory: &mut [u16; MAX_MEMORY]) -> io::Result<()> {
    let mut file = File::open(path)?;
    read_image_file(&mut file, memory)
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

pub fn mem_write(memory: &mut [u16; MAX_MEMORY], address: usize, value: u16) {
    memory[address] = value;
}

pub fn mem_read(memory: &mut [u16; MAX_MEMORY], address: u16, keyboard: &mut dyn Keyboard) -> u16 {
    let index_address = address as usize;
    if index_address == MR_KBSR {
        if let Some(key) = keyboard.check_key() {
            memory[MR_KBSR] = 1 << 15;
            memory[MR_KBSR] = key;
        }
    }
    return memory[index_address];
}
