pub mod image;
pub mod instructions;
pub mod memory;
pub mod platform;

use memory::*;
use platform::PlatformKeyboard;
pub const REGISTER_COUNT: usize = 10;

pub trait Keyboard {
    fn check_key(&mut self) -> Option<u16>;
    fn get_key(&mut self) -> u16 {
        loop {
            if let Some(k) = self.check_key() {
                return k;
            }
        }
    }
}

pub struct VM {
    pub memory: [u16; MAX_MEMORY],
    pub registers: [u16; REGISTER_COUNT],
    pub keyboard: Box<dyn Keyboard>,
    pub running: bool,
}

impl VM {
    pub fn new() -> Self {
        Self {
            memory: [0; MAX_MEMORY],
            registers: [0; REGISTER_COUNT],
            running: true,
            keyboard: Box::new(PlatformKeyboard::new()),
        }
    }
}
