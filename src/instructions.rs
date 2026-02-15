use crate::VM;
use Registers::*;
use std::io::{self, Write};

pub enum Registers {
    R0 = 0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    PC,
    COND,
    COUNT,
}

fn sign_extend(x: u16, bit_count: u8) -> u16 {
    if (x >> (bit_count - 1)) & 1 == 1 {
        return x | (0xFFFF << bit_count);
    } else {
        return x;
    }
}

impl VM {
    pub fn update_flags(&mut self, r: usize) {
        const FL_POS: u16 = 1 << 0;
        const FL_ZRO: u16 = 1 << 1;
        const FL_NEG: u16 = 1 << 2;
        if self.registers[r] == 0 {
            self.registers[COND as usize] = FL_ZRO;
        } else if (self.registers[r] >> 15) == 1 {
            self.registers[COND as usize] = FL_NEG;
        } else {
            self.registers[COND as usize] = FL_POS;
        }
    }
}

pub fn op_br(instr: u16, vm: &mut VM) {
    let pc_offset = sign_extend(instr & 0x1FF, 9);
    let cond_flag = (instr >> 9) & 0x7;
    let cond_reg = vm.registers[COND as usize];

    if (cond_flag & cond_reg) != 0 {
        let pc = vm.registers[PC as usize];
        vm.registers[PC as usize] = pc.wrapping_add(pc_offset);
    }
}

pub fn op_add(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let r1 = ((instr >> 6) & 0x7) as usize;
    let imm_flag = (instr >> 5) & 0x1;

    if imm_flag == 1 {
        let imm5 = sign_extend(instr & 0x1F, 5);
        vm.registers[r0] = vm.registers[r1].wrapping_add(imm5);
    } else {
        let r2 = (instr & 0x7) as usize;
        vm.registers[r0] = vm.registers[r1].wrapping_add(vm.registers[r2]);
    }
    vm.update_flags(r0);
}

pub fn op_ld(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let pc = vm.registers[PC as usize];
    let address = pc.wrapping_add(pc_offset);

    vm.registers[r0] = vm.mem_read(address);

    vm.update_flags(r0);
}

pub fn op_st(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let pc = vm.registers[PC as usize];
    let address = pc.wrapping_add(pc_offset);

    let value = vm.registers[r0];

    vm.mem_write(address, value);
}

pub fn op_jsr(instr: u16, vm: &mut VM) {
    let long_flag = (instr >> 11) & 1;
    vm.registers[R7 as usize] = vm.registers[PC as usize];

    if long_flag == 1 {
        let long_pc_offset = sign_extend(instr & 0x7FF, 11);
        let pc = vm.registers[PC as usize];
        vm.registers[PC as usize] = pc.wrapping_add(long_pc_offset);
    } else {
        let r1 = ((instr >> 6) & 0x7) as usize;
        vm.registers[PC as usize] = vm.registers[r1];
    }
}

pub fn op_and(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let r1 = ((instr >> 6) & 0x7) as usize;
    let imm_flag = (instr >> 5) & 0x1;

    if imm_flag == 1 {
        let imm5 = sign_extend(instr & 0x1F, 5);
        vm.registers[r0] = vm.registers[r1] & imm5;
    } else {
        let r2 = (instr & 0x7) as usize;
        vm.registers[r0] = vm.registers[r1] & vm.registers[r2];
    }
    vm.update_flags(r0);
}

pub fn op_ldr(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let r1 = ((instr >> 6) & 0x7) as usize;
    let offset = sign_extend(instr & 0x3F, 6);

    let base = vm.registers[r1];
    let address = base.wrapping_add(offset);

    vm.registers[r0] = vm.mem_read(address);

    vm.update_flags(r0);
}

pub fn op_str(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let r1 = ((instr >> 6) & 0x7) as usize;
    let offset = sign_extend(instr & 0x3F, 6);

    let base = vm.registers[r1];
    let address = base.wrapping_add(offset);

    let value = vm.registers[r0];

    vm.mem_write(address, value);
}

pub fn op_not(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let r1 = ((instr >> 6) & 0x7) as usize;

    vm.registers[r0] = !vm.registers[r1];

    vm.update_flags(r0);
}

pub fn op_ldi(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let address = vm.registers[PC as usize].wrapping_add(pc_offset);

    let final_address = vm.mem_read(address);
    vm.registers[r0] = vm.mem_read(final_address);

    vm.update_flags(r0);
}

pub fn op_sti(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let pc = vm.registers[PC as usize];
    let address = pc.wrapping_add(pc_offset);

    let indirect_address = vm.mem_read(address);

    let value = vm.registers[r0];

    vm.mem_write(indirect_address, value);
}

pub fn op_jmp(instr: u16, vm: &mut VM) {
    let r1 = ((instr >> 6) & 0x7) as usize;
    vm.registers[PC as usize] = vm.registers[r1];
}

pub fn op_lea(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let pc = vm.registers[PC as usize];

    vm.registers[r0] = pc.wrapping_add(pc_offset);

    vm.update_flags(r0);
}

pub fn op_trap(instr: u16, vm: &mut VM) {
    let trap_vector = instr & 0xFF;

    vm.registers[R7 as usize] = vm.registers[PC as usize];

    match trap_vector {
        0x20 => trap_getc(vm),
        0x21 => trap_out(vm),
        0x22 => trap_puts(vm),
        0x23 => trap_in(vm),
        0x24 => trap_putsp(vm),
        0x25 => trap_halt(vm),
        _ => panic!("Unkown TRAP: {trap_vector:#x}"),
    }
}

fn trap_getc(vm: &mut VM) {
    let ch = vm.keyboard.get_key();
    vm.registers[R0 as usize] = ch;
    vm.update_flags(R0 as usize);
}

fn trap_out(vm: &mut VM) {
    let ch = vm.registers[R0 as usize];
    print!("{ch}");
    io::stdout().flush().unwrap();
}

fn trap_puts(vm: &mut VM) {
    let mut address = vm.registers[R0 as usize];

    loop {
        let ch = vm.mem_read(address);
        if ch == 0 {
            break;
        }

        print!("{}", (ch as u8) as char);
        address = address.wrapping_add(1);
    }
}

fn trap_in(vm: &mut VM) {
    print!("Enter a character: ");
    io::stdout().flush().unwrap();

    let ch = vm.keyboard.get_key();
    io::stdout().flush().unwrap();

    vm.registers[R0 as usize] = ch;
    vm.update_flags(R0 as usize);
}

fn trap_putsp(vm: &mut VM) {
    let mut address = vm.registers[R0 as usize];
    loop {
        let word = vm.mem_read(address);

        if word == 0 {
            break;
        }

        let ch1 = (word & 0x00FF) as u8;
        print!("{}", ch1 as char);
        let ch2 = (word >> 8) as u8;
        if ch2 != 0 {
            print!("{}", ch2 as char);
        }
        address = address.wrapping_add(1);
    }
    io::stdout().flush().unwrap();
}

fn trap_halt(vm: &mut VM) {
    println!("HALT");
    vm.running = false;
}
