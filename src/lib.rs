pub mod image;
pub mod instructions;
pub mod memory;
pub mod platform;
pub mod vm;

pub trait Keyboard {
    fn check_key(&mut self) -> Option<u16>;
}
