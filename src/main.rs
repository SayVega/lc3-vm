use lc3_vm::VM;
use lc3_vm::instructions::*;
use lc3_vm::memory::read_image;
use lc3_vm::platform::TerminalGuard;

use std::env;
use std::process;

fn main() {
    let _terminal = TerminalGuard::new();
    let mut vm = VM::new();
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("lc3 [image-file1] ...");
        process::exit(2);
    }

    for image_path in &args[1..] {
        if read_image(image_path, &mut vm).is_err() {
            println!("failed to load image: {}", image_path);
            process::exit(1);
        }
    }

    while vm.running {
        let pc = vm.registers[Registers::PC as usize];
        let instr = vm.mem_read(pc);

        vm.registers[Registers::PC as usize] = pc.wrapping_add(1);

        let opcode = instr >> 12;

        match opcode {
            0x0 => op_br(instr, &mut vm),
            0x1 => op_add(instr, &mut vm),
            0x2 => op_ld(instr, &mut vm),
            0x3 => op_st(instr, &mut vm),
            0x4 => op_jsr(instr, &mut vm),
            0x5 => op_and(instr, &mut vm),
            0x6 => op_ldr(instr, &mut vm),
            0x7 => op_str(instr, &mut vm),
            0x8 => { /* RTI unused */ }
            0x9 => op_not(instr, &mut vm),
            0xA => op_ldi(instr, &mut vm),
            0xB => op_sti(instr, &mut vm),
            0xC => op_jmp(instr, &mut vm),
            0xD => { /* RES unused */ }
            0xE => op_lea(instr, &mut vm),
            0xF => op_trap(instr, &mut vm),
            _ => panic!("Bad opcode: {opcode:#x}"),
        }
    }
}
