#![doc = include_str!("../docs/README.md")]
mod instructions;
mod memory;
mod platform;
mod vm;

pub use memory::read_image;
pub use platform::TerminalGuard;
pub use vm::Keyboard;
pub use vm::Registers;
pub use vm::TerminalOutput;
pub use vm::VM;
pub use vm::{FL_N, FL_P, FL_Z};
