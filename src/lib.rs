pub mod image;
pub mod instructions;
pub mod memory;
pub mod platform;

use instructions::*;
use memory::*;
pub trait Keyboard {
    fn check_key(&mut self) -> Option<u16>;
}

pub struct VM {
    pub memory: [u16; MAX_MEMORY],
    pub registers: [u16; REGISTER_COUNT],
    pub keyboard: Box<dyn Keyboard>,
    pub running: bool,
}
