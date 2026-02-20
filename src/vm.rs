use crate::instructions::Registers::COND;
use crate::instructions::*;
use crate::memory::{MAX_MEMORY, read_image};
use crate::platform::PlatformKeyboard;
use std::io::{self, Write};

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

pub struct StdoutDevice;

pub trait TerminalOutput {
    fn write_char(&mut self, c: u8);
    fn flush(&mut self);
}

impl TerminalOutput for StdoutDevice {
    fn write_char(&mut self, c: u8) {
        print!("{}", c as char);
    }
    fn flush(&mut self) {
        let _ = io::stdout().flush();
    }
}

pub struct VM {
    pub memory: [u16; MAX_MEMORY],
    pub registers: [u16; REGISTER_COUNT],
    pub keyboard: Box<dyn Keyboard>,
    pub output: Box<dyn TerminalOutput>,
    pub running: bool,
}

impl VM {
    pub fn new() -> Self {
        let mut vm = Self {
            memory: [0; MAX_MEMORY],
            registers: [0; REGISTER_COUNT],
            keyboard: Box::new(PlatformKeyboard::new()),
            output: Box::new(StdoutDevice),
            running: true,
        };
        vm.registers[COND as usize] = FL_Z;
        vm
    }
    pub fn load_image(&mut self, path: &str) -> std::io::Result<()> {
        read_image(path, self)
    }
    pub fn run(&mut self) {
        while self.running {
            let pc = self.registers[Registers::PC as usize];
            let instr = self.mem_read(pc);

            self.registers[Registers::PC as usize] = pc.wrapping_add(1);

            let opcode = instr >> 12;

            match opcode {
                0x0 => op_br(instr, self),
                0x1 => op_add(instr, self),
                0x2 => op_ld(instr, self),
                0x3 => op_st(instr, self),
                0x4 => op_jsr(instr, self),
                0x5 => op_and(instr, self),
                0x6 => op_ldr(instr, self),
                0x7 => op_str(instr, self),
                0x8 => panic!("Bad opcode: {opcode:#x} (RTI unused)"),
                0x9 => op_not(instr, self),
                0xA => op_ldi(instr, self),
                0xB => op_sti(instr, self),
                0xC => op_jmp(instr, self),
                0xD => panic!("Bad opcode: {opcode:#x} (RES reserved)"),
                0xE => op_lea(instr, self),
                0xF => op_trap(instr, self),
                _ => unreachable!(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::{MR_KBDR, MR_KBSR};
    struct MockKeyboard {
        key: Option<u16>,
    }

    impl Keyboard for MockKeyboard {
        fn check_key(&mut self) -> Option<u16> {
            self.key
        }
    }

    #[test]
    fn run_executes_instruction_cycle_and_halts() {
        let mut vm = VM::new();
        let origin = 0x3000;
        vm.registers[Registers::PC as usize] = origin as u16;
        vm.registers[1] = 0;
        vm.memory[origin] = 0x1261; // ADD R1, R1, #1
        vm.memory[origin + 1] = 0xF025; // HALT
        vm.run();
        assert_eq!(vm.registers[1], 1);
        assert_eq!(vm.running, false);
        assert_eq!(vm.registers[Registers::PC as usize], (origin + 2) as u16);
    }
    #[test]
    fn run_executes_sequential_instructions_before_halting() {
        let mut vm = VM::new();
        let origin = 0x3000;
        vm.registers[Registers::PC as usize] = origin as u16;
        vm.registers[1] = 0;
        vm.memory[origin] = 0x1261; // ADD R1, R1, #1
        vm.memory[origin + 1] = 0x1262; // ADD R1, R1, #2
        vm.memory[origin + 2] = 0xF025; // HALT
        vm.run();
        assert_eq!(vm.registers[1], 3);
        assert_eq!(vm.running, false);
        assert_eq!(vm.registers[Registers::PC as usize], (origin + 3) as u16);
    }
    #[test]
    #[should_panic]
    fn run_panics_on_invalid_opcode() {
        let mut vm = VM::new();
        let origin = 0x3000;
        vm.registers[Registers::PC as usize] = origin as u16;
        vm.memory[origin] = 0xD000;
        vm.run();
    }
    #[test]
    fn vm_initializes_with_clean_state() {
        let vm = VM::new();
        assert_eq!(vm.memory.iter().all(|&x| x == 0), true);
        assert_eq!(vm.running, true);
        for reg in 0..(COND as usize) {
            assert_eq!(vm.registers[reg], 0);
        }
        assert_eq!(vm.registers[COND as usize], 1 << 1);
    }
    #[test]
    fn reading_kbsr_without_input_maintains_state() {
        let mut vm = VM::new();
        vm.keyboard = Box::new(MockKeyboard { key: None });
        vm.memory[MR_KBSR] = 0;
        let val = vm.mem_read(MR_KBSR as u16);
        assert_eq!(val, 0);
        assert_eq!(vm.memory[MR_KBSR], 0);
    }
    #[test]
    fn reading_kbsr_with_input_sets_flags_and_data() {
        let mut vm = VM::new();
        vm.keyboard = Box::new(MockKeyboard { key: Some(0x0041) });
        vm.memory[MR_KBSR] = 0;
        let val = vm.mem_read(MR_KBSR as u16);
        assert_eq!(val, 1 << 15);
        assert_eq!(vm.memory[MR_KBSR], 1 << 15);
        assert_eq!(vm.memory[MR_KBDR], 0x0041);
    }
}
