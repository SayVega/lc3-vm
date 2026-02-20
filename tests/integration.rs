use lc3_vm::Keyboard;
use lc3_vm::Registers::*;
use lc3_vm::TerminalOutput;
use lc3_vm::VM;
use lc3_vm::read_image;
use std::cell::RefCell;
use std::rc::Rc;

struct MockKeyboard {
    key: Option<u16>,
}
impl Keyboard for MockKeyboard {
    fn check_key(&mut self) -> Option<u16> {
        self.key
    }
}

struct MockOutput {
    buffer: Rc<RefCell<Vec<u8>>>,
}

impl TerminalOutput for MockOutput {
    fn write_char(&mut self, c: u8) {
        self.buffer.borrow_mut().push(c);
    }
    fn flush(&mut self) {}
}

fn load_program(vm: &mut VM, origin: u16, program: &[u16]) {
    for (i, &instr) in program.iter().enumerate() {
        vm.memory[origin as usize + i] = instr;
    }
}

#[test]
fn integration_add_immediate_and_register() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x1025, // ADD R0, R0, #5
        0x1240, // ADD R1, R1, R0
        0xF025, // TRAP HALT
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R0 as usize], 5);
    assert_eq!(vm.registers[R1 as usize], 5);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_and_reg_and_imm() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x2203, // LD R1, #3
        0x546F, // AND R2, R1, #15
        0x5642, // AND R3, R1, R2
        0xF025, // TRAP HALT
        0x00FF, // Mask data
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R2 as usize], 0x000F);
    assert_eq!(vm.registers[R3 as usize], 0x000F);
}

#[test]
fn integration_not() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x1025, // ADD R0, R0, #5
        0x923F, // NOT R1, R0
        0xF025, // TRAP HALT
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R0 as usize], 5);
    assert_eq!(vm.registers[R1 as usize], 0xFFFA);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_br() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x5020, // AND R0, R0, #0
        0x0801, // BRn #1
        0x1021, // ADD R0, R0, #1
        0x0201, // BRp #1
        0x1021, // ADD R0, R0, #1
        0xF025, // TRAP HALT
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R0 as usize], 1);
    assert_eq!(vm.registers[PC as usize], origin + 6);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_jmp() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x2802, // LD R4, #2
        0xC100, // JMP R4
        0x1221, // ADD R1, R1, #1
        0x3004, // Data
        0xF025, // TRAP HALT
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R1 as usize], 0);
    assert_eq!(vm.registers[PC as usize], origin + program.len() as u16);
}
#[test]
fn integration_jsr() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x4802, // JSR #2
        0xF025, // TRAP HALT
        0x1221, // ADD R1, R1, #1
        0x14A5, // ADD R2, R2, #5
        0xC1C0, // JMP R7
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R7 as usize], 0x3002);
    assert_eq!(vm.registers[R2 as usize], 5);
    assert_eq!(vm.registers[R1 as usize], 0);
    assert_eq!(vm.registers[PC as usize], 0x3002);
}

#[test]
fn integration_ld() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x2001, // LD R0, #1
        0xF025, // TRAP HALT
        0xABCD, // Data
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R0 as usize], 0xABCD);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_ldi() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0xA001, // LDI R0, #1
        0xF025, // TRAP HALT
        0x3004, // Pointer
        0x0000, // Padding
        0x4567, // Data
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R0 as usize], 0x4567);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_ldr() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x2202, // LD R1, #2
        0x6041, // LDR R0, R1, #1
        0xF025, // TRAP HALT
        0x3004, // Pointer
        0x0000, // Padding
        0x9876, // Data
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R0 as usize], 0x9876);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_st() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x1267, // ADD R1, R1, #7
        0x3202, // ST R1, #2
        0xF025, // TRAP HALT
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R1 as usize], 7);
    assert_eq!(vm.memory[0x3004], 7);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_sti_store_indirect() {
    let mut vm = VM::new();
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x1265, // ADD R1, R1, #5
        0xB202, // STI R1, #2
        0xF025, // TRAP HALT
        0x0000, // Padding
        0x3006, // Pointer
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.memory[0x3006], 5);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_getc() {
    let mut vm = VM::new();
    vm.keyboard = Box::new(MockKeyboard {
        key: Some(0x42), // 'B'
    });
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0xF020, // TRAP GETC
        0xF025, // TRAP HALT
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R0 as usize], 0x42);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_out() {
    let mut vm = VM::new();
    let shared_buffer = Rc::new(RefCell::new(Vec::new()));
    vm.output = Box::new(MockOutput {
        buffer: Rc::clone(&shared_buffer),
    });
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0x2002, // LD R0, #2
        0xF021, // TRAP OUT
        0xF025, // TRAP HALT
        0x0043, // 'C'
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(*shared_buffer.borrow(), vec![0x43]);
}

#[test]
fn integration_puts() {
    let mut vm = VM::new();
    let shared_buffer = Rc::new(RefCell::new(Vec::new()));
    vm.output = Box::new(MockOutput {
        buffer: Rc::clone(&shared_buffer),
    });
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0xE002, // LEA R0, #2
        0xF022, // TRAP PUTS
        0xF025, // TRAP HALT
        0x0041, // 'A'
        0x0000, // '\0'
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(*shared_buffer.borrow(), vec![0x41]);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_in() {
    let mut vm = VM::new();
    let shared_buffer = Rc::new(RefCell::new(Vec::new()));
    vm.output = Box::new(MockOutput {
        buffer: Rc::clone(&shared_buffer),
    });
    vm.keyboard = Box::new(MockKeyboard { key: Some(0x44) }); // 'D'
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0xF023, // TRAP IN
        0xF025, // TRAP HALT
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(vm.registers[R0 as usize], 0x44);
    let mut expected_output = b"Enter a character: ".to_vec();
    expected_output.push(0x44);
    assert_eq!(*shared_buffer.borrow(), expected_output);
}

#[test]
fn integration_putsp() {
    let mut vm = VM::new();
    let shared_buffer = Rc::new(RefCell::new(Vec::new()));
    vm.output = Box::new(MockOutput {
        buffer: Rc::clone(&shared_buffer),
    });
    let origin = 0x3000;
    vm.registers[PC as usize] = origin;
    let program = [
        0xE002, // LEA R0, #2
        0xF024, // TRAP PUTSP
        0xF025, // TRAP HALT
        0x4241, // 'B' en bits [15:8], 'A' en bits [7:0]
        0x0000,
    ];
    load_program(&mut vm, origin, &program);
    vm.run();
    assert_eq!(*shared_buffer.borrow(), vec![0x41, 0x42]);
}

#[test]
fn integration_obj_palindrome() {
    let mut vm = VM::new();
    read_image("tests/fixtures/palindrome.obj", &mut vm).unwrap();
    vm.run();
    assert_eq!(vm.registers[R5 as usize], 1);
    assert_eq!(vm.memory[0x4000], 1);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_obj_fibonacci() {
    let mut vm = VM::new();
    read_image("tests/fixtures/fibonacci.obj", &mut vm).unwrap();
    vm.run();
    assert_eq!(vm.registers[R0 as usize], 55);
    assert_eq!(vm.memory[0x4000], 55);
    assert_eq!(vm.running, false);
}

#[test]
fn integration_obj_bubblesort() {
    let mut vm = VM::new();
    let data = [5, 2, 3, 4, 1];
    for (i, &val) in data.iter().enumerate() {
        vm.memory[0x4000 + i] = val;
    }
    read_image("tests/fixtures/bubblesort.obj", &mut vm).unwrap();
    vm.run();
    assert_eq!(vm.memory[0x4000], 1);
    assert_eq!(vm.memory[0x4001], 2);
    assert_eq!(vm.memory[0x4002], 3);
    assert_eq!(vm.memory[0x4003], 4);
    assert_eq!(vm.memory[0x4004], 5);
    assert_eq!(vm.running, false);
}
