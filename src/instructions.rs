use crate::VM;
use Registers::*;
use std::io::{self, Write};

#[allow(dead_code)]
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

pub const FL_P: u16 = 1 << 0;
pub const FL_Z: u16 = 1 << 1;
pub const FL_N: u16 = 1 << 2;

fn sign_extend(x: u16, bit_count: u8) -> u16 {
    if (x >> (bit_count - 1)) & 1 == 1 && bit_count < 16 {
        return x | (0xFFFF << bit_count);
    } else {
        return x;
    }
}

impl VM {
    pub fn update_flags(&mut self, r: usize) {
        if self.registers[r] == 0 {
            self.registers[COND as usize] = FL_Z;
        } else if (self.registers[r] >> 15) == 1 {
            self.registers[COND as usize] = FL_N;
        } else {
            self.registers[COND as usize] = FL_P;
        }
    }
}

pub(crate) fn op_br(instr: u16, vm: &mut VM) {
    let pc_offset = sign_extend(instr & 0x1FF, 9);
    let cond_flag = (instr >> 9) & 0x7;
    let cond_reg = vm.registers[COND as usize];

    if (cond_flag & cond_reg) != 0 {
        let pc = vm.registers[PC as usize];
        vm.registers[PC as usize] = pc.wrapping_add(pc_offset);
    }
}

pub(crate) fn op_add(instr: u16, vm: &mut VM) {
    let destination = ((instr >> 9) & 0x7) as usize;
    let source = ((instr >> 6) & 0x7) as usize;
    let imm_flag = (instr >> 5) & 0x1;

    if imm_flag == 1 {
        let imm5 = sign_extend(instr & 0x1F, 5);
        vm.registers[destination] = vm.registers[source].wrapping_add(imm5);
    } else {
        let r2 = (instr & 0x7) as usize;
        vm.registers[destination] = vm.registers[source].wrapping_add(vm.registers[r2]);
    }
    vm.update_flags(destination);
}

pub(crate) fn op_ld(instr: u16, vm: &mut VM) {
    let destination = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let pc = vm.registers[PC as usize];
    let address = pc.wrapping_add(pc_offset);

    vm.registers[destination] = vm.mem_read(address);

    vm.update_flags(destination);
}

pub(crate) fn op_st(instr: u16, vm: &mut VM) {
    let source = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);
    let address = vm.registers[PC as usize].wrapping_add(pc_offset);

    vm.mem_write(address, vm.registers[source]);
}

pub(crate) fn op_jsr(instr: u16, vm: &mut VM) {
    let long_flag = (instr >> 11) & 1;
    let pc = vm.registers[PC as usize];

    let target_pc = if long_flag == 1 {
        let long_pc_offset = sign_extend(instr & 0x7FF, 11);
        pc.wrapping_add(long_pc_offset)
    } else {
        let source = ((instr >> 6) & 0x7) as usize;
        vm.registers[source]
    };
    vm.registers[R7 as usize] = pc;
    vm.registers[PC as usize] = target_pc;
}

pub(crate) fn op_and(instr: u16, vm: &mut VM) {
    let destination = ((instr >> 9) & 0x7) as usize;
    let source1 = ((instr >> 6) & 0x7) as usize;
    let imm_flag = (instr >> 5) & 0x1;

    if imm_flag == 1 {
        let imm5 = sign_extend(instr & 0x1F, 5);
        vm.registers[destination] = vm.registers[source1] & imm5;
    } else {
        let source2 = (instr & 0x7) as usize;
        vm.registers[destination] = vm.registers[source1] & vm.registers[source2];
    }
    vm.update_flags(destination);
}

pub(crate) fn op_ldr(instr: u16, vm: &mut VM) {
    let destination = ((instr >> 9) & 0x7) as usize;
    let base_source = ((instr >> 6) & 0x7) as usize;
    let offset = sign_extend(instr & 0x3F, 6);

    let base_adress = vm.registers[base_source];
    let address = base_adress.wrapping_add(offset);

    vm.registers[destination] = vm.mem_read(address);

    vm.update_flags(destination);
}

pub(crate) fn op_str(instr: u16, vm: &mut VM) {
    let source = ((instr >> 9) & 0x7) as usize;
    let base_source = ((instr >> 6) & 0x7) as usize;
    let offset = sign_extend(instr & 0x3F, 6);

    let base_address = vm.registers[base_source];
    let address = base_address.wrapping_add(offset);

    let value = vm.registers[source];

    vm.mem_write(address, value);
}

pub(crate) fn op_not(instr: u16, vm: &mut VM) {
    let destination = ((instr >> 9) & 0x7) as usize;
    let source = ((instr >> 6) & 0x7) as usize;

    vm.registers[destination] = !vm.registers[source];

    vm.update_flags(destination);
}

pub(crate) fn op_ldi(instr: u16, vm: &mut VM) {
    let destination = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let address = vm.registers[PC as usize].wrapping_add(pc_offset);

    let final_address = vm.mem_read(address);
    vm.registers[destination] = vm.mem_read(final_address);

    vm.update_flags(destination);
}

pub(crate) fn op_sti(instr: u16, vm: &mut VM) {
    let source = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let pc = vm.registers[PC as usize];
    let address = pc.wrapping_add(pc_offset);

    let indirect_address = vm.mem_read(address);

    let value = vm.registers[source];

    vm.mem_write(indirect_address, value);
}

pub(crate) fn op_jmp(instr: u16, vm: &mut VM) {
    let source = ((instr >> 6) & 0x7) as usize;
    vm.registers[PC as usize] = vm.registers[source];
}

pub(crate) fn op_lea(instr: u16, vm: &mut VM) {
    let destination = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let pc = vm.registers[PC as usize];

    vm.registers[destination] = pc.wrapping_add(pc_offset);

    vm.update_flags(destination);
}

pub(crate) fn op_trap(instr: u16, vm: &mut VM) {
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
    let ch = (vm.registers[R0 as usize] & 0x00FF) as u8;
    vm.output.write_char(ch);
    vm.output.flush();
}

fn trap_puts(vm: &mut VM) {
    let mut address = vm.registers[R0 as usize];
    loop {
        let ch = vm.mem_read(address);
        if ch == 0 {
            break;
        }
        vm.output.write_char((ch & 0x00FF) as u8);
        address = address.wrapping_add(1);
    }
    vm.output.flush();
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
        vm.output.write_char(ch1);
        let ch2 = (word >> 8) as u8;
        if ch2 != 0 {
            vm.output.write_char(ch2);
        }
        address = address.wrapping_add(1);
    }
    vm.output.flush();
}

fn trap_halt(vm: &mut VM) {
    vm.running = false;
}

#[cfg(test)]
mod tests {
    use super::*;
    mod helpers {
        use super::*;
        #[test]
        fn sign_extend_zero() {
            assert_eq!(sign_extend(0b00000, 5), 0);
        }

        #[test]
        fn sign_extend_negative() {
            assert_eq!(sign_extend(0b10000, 5), 0xFFF0);
        }

        #[test]
        fn sign_extend_positive() {
            assert_eq!(sign_extend(0b01111, 5), 15);
        }

        #[test]
        fn sign_extend_full_width() {
            assert_eq!(sign_extend(0x8000, 16), 0x8000);
        }

        #[test]
        fn sign_extend_one_bit() {
            assert_eq!(sign_extend(0b0, 1), 0);
            assert_eq!(sign_extend(0b1, 1), 0xFFFF);
        }

        #[test]
        fn update_flags_zero() {
            let mut vm = VM::new();
            vm.registers[1] = 0;
            vm.update_flags(1);
            assert_eq!(vm.registers[COND as usize], 1 << 1);
        }

        #[test]
        fn update_flags_positive() {
            let mut vm = VM::new();
            vm.registers[1] = 5;
            vm.update_flags(1);
            assert_eq!(vm.registers[COND as usize], 1 << 0);
        }

        #[test]
        fn update_flags_negative() {
            let mut vm = VM::new();
            vm.registers[1] = 0x8000;
            vm.update_flags(1);
            assert_eq!(vm.registers[COND as usize], 1 << 2);
        }

        #[test]
        fn update_flags_overwrites_previous() {
            let mut vm = VM::new();
            vm.registers[COND as usize] = 0xFFFF;
            vm.registers[1] = 0;
            vm.update_flags(1);
            assert_eq!(vm.registers[COND as usize], 1 << 1);
        }
    }
    mod opcodes {
        use super::*;

        fn build_br(flags: u16, offset: i16) -> u16 {
            (0b0000 << 12) | ((flags & 0x7) << 9) | ((offset as u16) & 0x1FF)
        }
        fn build_add(destination: u16, source1: u16, source2: u16) -> u16 {
            (0b0001 << 12)
                | ((destination & 0x7) << 9)
                | ((source1 & 0x7) << 6)
                | (0 << 5)
                | (source2 & 0x7)
        }
        fn build_add_imm(destination: u16, source: u16, imm5: i8) -> u16 {
            (0b0001 << 12)
                | ((destination & 0x7) << 9)
                | (source << 6)
                | (1 << 5)
                | ((imm5 as u16) & 0x1F)
        }
        fn build_ld(destination: u16, offset9: i16) -> u16 {
            (0b0010 << 12) | ((destination & 0x7) << 9) | ((offset9 as u16) & 0x1FF)
        }
        fn build_st(source: u16, offset: i16) -> u16 {
            (0b0011 << 12) | ((source & 0x7) << 9) | ((offset as u16) & 0x1FF)
        }
        fn build_jsr(offset: i16) -> u16 {
            (0b0100 << 12) | (1 << 11) | ((offset as u16) & 0x7FF)
        }
        fn build_jsrr(base: u16) -> u16 {
            (0b0100 << 12) | (0 << 11) | ((base & 0x7) << 6)
        }
        fn build_and_reg(destination: u16, source1: u16, source2: u16) -> u16 {
            (0b0101 << 12)
                | ((destination & 0x7) << 9)
                | (source1 << 6)
                | (0 << 5)
                | (source2 & 0x7)
        }
        fn build_and_imm(destination: u16, source: u16, imm5: i8) -> u16 {
            (0b0101 << 12)
                | ((destination & 0x7) << 9)
                | (source << 6)
                | (1 << 5)
                | ((imm5 as u16) & 0x1F)
        }
        fn build_ldr(destination: u16, base: u16, offset: i16) -> u16 {
            (0b0110 << 12)
                | ((destination & 0x7) << 9)
                | ((base & 0x7) << 6)
                | ((offset as u16) & 0x3F)
        }
        fn build_str(source: u16, base: u16, offset: i16) -> u16 {
            (0b0111 << 12) | ((source & 0x7) << 9) | ((base & 0x7) << 6) | ((offset as u16) & 0x3F)
        }
        fn build_not(destination: u16, source: u16) -> u16 {
            (0b1001 << 12) | ((destination & 0x7) << 9) | ((source & 0x7) << 6) | 0x3F
        }
        fn build_ldi(destination: u16, offset: i16) -> u16 {
            (0b1010 << 12) | ((destination & 0x7) << 9) | ((offset as u16) & 0x1FF)
        }
        fn build_sti(source: u16, offset: i16) -> u16 {
            (0b1011 << 12) | ((source & 0x7) << 9) | ((offset as u16) & 0x1FF)
        }
        fn build_jmp(base: u16) -> u16 {
            (0b1100 << 12) | ((base & 0x7) << 6)
        }
        fn build_lea(destination: u16, offset: i16) -> u16 {
            (0b1110 << 12) | ((destination & 0x7) << 9) | ((offset as u16) & 0x1FF)
        }
        fn build_trap(trap_vector: u8) -> u16 {
            (0b1111 << 12) | (trap_vector as u16)
        }
        #[test]
        fn br_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[COND as usize] = FL_P;
            let instr = build_br(0b001, 3);
            op_br(instr, &mut vm);
            assert_eq!(vm.registers[PC as usize], 0x3003);
        }
        #[test]
        fn br_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3005;
            vm.registers[COND as usize] = FL_P;
            let instr = build_br(0b001, -2);
            op_br(instr, &mut vm);
            assert_eq!(vm.registers[PC as usize], 0x3003);
        }
        #[test]
        fn br_max_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[COND as usize] = FL_P;
            let instr = build_br(0b001, 255);
            op_br(instr, &mut vm);
            assert_eq!(vm.registers[PC as usize], 0x30FF);
        }
        #[test]
        fn br_max_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[COND as usize] = FL_P;
            let instr = build_br(0b001, -256);
            op_br(instr, &mut vm);
            assert_eq!(vm.registers[PC as usize], 0x2F00);
        }
        #[test]
        fn br_no_jump_when_flag_not_set() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[COND as usize] = FL_Z;
            let instr = build_br(0b001, 3);
            op_br(instr, &mut vm);
            assert_eq!(vm.registers[PC as usize], 0x3000);
        }
        #[test]
        fn br_mixed_flags_match() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[COND as usize] = FL_P;
            let instr = build_br(0b011, 5);
            op_br(instr, &mut vm);
            assert_eq!(vm.registers[PC as usize], 0x3005);
        }
        #[test]
        fn br_wrapping_negative() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x0000;
            vm.registers[COND as usize] = FL_Z;
            let instr = build_br(0b111, -1);
            op_br(instr, &mut vm);
            assert_eq!(vm.registers[PC as usize], 0xFFFF);
        }
        #[test]
        fn add_register_mode() {
            let mut vm = VM::new();
            vm.registers[1] = 5;
            vm.registers[2] = 3;
            let instr = build_add(0, 1, 2);
            op_add(instr, &mut vm);
            assert_eq!(vm.registers[0], 8);
        }
        #[test]
        fn add_immediate_mode() {
            let mut vm = VM::new();
            vm.registers[1] = 5;
            let instr = build_add_imm(0, 1, 3);
            op_add(instr, &mut vm);
            assert_eq!(vm.registers[0], 8);
        }
        #[test]
        fn add_immediate_max_positive() {
            let mut vm = VM::new();
            vm.registers[1] = 10;
            let instr = build_add_imm(0, 1, 15);
            op_add(instr, &mut vm);
            assert_eq!(vm.registers[0], 25);
        }

        #[test]
        fn add_immediate_max_negative() {
            let mut vm = VM::new();
            vm.registers[1] = 20;
            let instr = build_add_imm(0, 1, -16);
            op_add(instr, &mut vm);
            assert_eq!(vm.registers[0], 4);
        }
        #[test]
        fn add_sets_positive_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 1;
            vm.registers[2] = 1;
            let instr = build_add(0, 1, 2);
            op_add(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_P);
        }
        #[test]
        fn add_sets_negative_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0x8000;
            vm.registers[2] = 0;
            let instr = build_add(0, 1, 2);
            op_add(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_N);
        }
        #[test]
        fn add_sets_zero_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 5;
            vm.registers[2] = -5i16 as u16;
            let instr = build_add(0, 1, 2);
            op_add(instr, &mut vm);
            assert_eq!(vm.registers[0], 0);
            assert_eq!(vm.registers[COND as usize], FL_Z);
        }
        #[test]
        fn add_immediate_negative() {
            let mut vm = VM::new();
            vm.registers[1] = 5;
            let instr = build_add_imm(0, 1, -1);
            op_add(instr, &mut vm);
            assert_eq!(vm.registers[0], 4);
        }
        #[test]
        fn ld_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x3001, 42);
            let instr = build_ld(0, 1);
            op_ld(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ld_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x2FFF, 42);
            let instr = build_ld(0, -1);
            op_ld(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ld_max_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x30FF, 42);
            let instr = build_ld(0, 255);
            op_ld(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ld_max_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x2F00, 42);
            let instr = build_ld(0, -256);
            op_ld(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ld_wrapping() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x0000;
            vm.mem_write(0xFFFF, 42);
            let instr = build_ld(0, -1);
            op_ld(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ld_sets_positive_flag() {
            let mut vm: VM = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x3001, 42);
            let instr = build_ld(0, 1);
            op_ld(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_P);
        }
        #[test]
        fn ld_sets_negative_flag() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x3001, -1i16 as u16);
            let instr = build_ld(0, 1);
            op_ld(instr, &mut vm);
            assert_eq!(vm.registers[0], -1i16 as u16);
            assert_eq!(vm.registers[COND as usize], FL_N);
        }
        #[test]
        fn ld_sets_zero_flag() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x3001, 0);
            let instr = build_ld(0, 1);
            op_ld(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_Z);
        }
        #[test]
        fn st_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[0] = 42;
            let instr = build_st(0, 1);
            op_st(instr, &mut vm);
            assert_eq!(vm.mem_read(0x3001), 42);
        }
        #[test]
        fn st_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[0] = 42;
            let instr = build_st(0, -1);
            op_st(instr, &mut vm);
            assert_eq!(vm.mem_read(0x2FFF), 42);
        }
        #[test]
        fn st_max_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[0] = 42;
            let instr = build_st(0, 255);
            op_st(instr, &mut vm);
            assert_eq!(vm.mem_read(0x30FF), 42);
        }
        #[test]
        fn st_max_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[0] = 42;
            let instr = build_st(0, -256);
            op_st(instr, &mut vm);
            assert_eq!(vm.mem_read(0x2F00), 42);
        }
        #[test]
        fn st_wrapping() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x0000;
            vm.registers[0] = 42;
            let instr = build_st(0, -1);
            op_st(instr, &mut vm);
            assert_eq!(vm.mem_read(0xFFFF), 42);
        }
        #[test]
        fn jsr_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            let instr = build_jsr(5);
            op_jsr(instr, &mut vm);
            assert_eq!(vm.registers[R7 as usize], 0x3000);
            assert_eq!(vm.registers[PC as usize], 0x3005);
        }
        #[test]
        fn jsr_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            let instr = build_jsr(-5);
            op_jsr(instr, &mut vm);
            assert_eq!(vm.registers[R7 as usize], 0x3000);
            assert_eq!(vm.registers[PC as usize], 0x2FFB);
        }
        #[test]
        fn jsr_max_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            let instr = build_jsr(1023);
            op_jsr(instr, &mut vm);
            assert_eq!(vm.registers[R7 as usize], 0x3000);
            assert_eq!(vm.registers[PC as usize], 0x33FF);
        }
        #[test]
        fn jsr_max_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            let instr = build_jsr(-1024);
            op_jsr(instr, &mut vm);
            assert_eq!(vm.registers[R7 as usize], 0x3000);
            assert_eq!(vm.registers[PC as usize], 0x2C00);
        }
        #[test]
        fn jsrr_happy_path() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[3] = 0x5000;
            let instr = build_jsrr(3);
            op_jsr(instr, &mut vm);
            assert_eq!(vm.registers[R7 as usize], 0x3000);
            assert_eq!(vm.registers[PC as usize], 0x5000);
        }
        #[test]
        fn jsrr_swap_r7() {
            let mut vm = VM::new();
            let old_pc = 0x3000;
            let old_r7 = 0x4000;
            vm.registers[PC as usize] = old_pc;
            vm.registers[R7 as usize] = old_r7;
            let instr = build_jsrr(7);
            op_jsr(instr, &mut vm);
            assert_eq!(vm.registers[PC as usize], old_r7);
            assert_eq!(vm.registers[R7 as usize], old_pc);
        }
        #[test]
        fn jsr_wrapping() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x0000;
            let instr = build_jsr(-1);
            op_jsr(instr, &mut vm);
            assert_eq!(vm.registers[R7 as usize], 0x0000);
            assert_eq!(vm.registers[PC as usize], 0xFFFF);
        }
        #[test]
        fn and_reg_happy_path() {
            let mut vm = VM::new();
            vm.registers[1] = 0b1010_1010_1010_1010;
            vm.registers[2] = 0b1111_0000_1111_0000;
            let instr = build_and_reg(0, 1, 2);
            op_and(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b1010_0000_1010_0000);
        }
        #[test]
        fn and_immediate_positive() {
            let mut vm = VM::new();
            vm.registers[1] = 0b0000_0000_1010_1010;
            let instr = build_and_imm(0, 1, 0b01010);
            op_and(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b0000_0000_0000_1010);
        }
        #[test]
        fn and_immediate_negative() {
            let mut vm = VM::new();
            vm.registers[1] = 0b0000_0000_1010_1010;
            let instr = build_and_imm(0, 1, -1); // -1 = 1111 1111 1111 1111
            op_and(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b0000_0000_1010_1010);
        }
        #[test]
        fn and_immediate_max_positive() {
            let mut vm = VM::new();
            vm.registers[1] = 0b0000_0000_1010_1010;
            let instr = build_and_imm(0, 1, 0b01111);
            op_and(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b0000_0000_0000_1010);
        }
        #[test]
        fn and_immediate_max_negative() {
            let mut vm = VM::new();
            vm.registers[1] = 0b0000_0000_1010_1010;
            let instr = build_and_imm(0, 1, -16); // -16 = 1111 1111 1111 0000
            op_and(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b0000_0000_1010_0000);
        }
        #[test]
        fn and_sets_positive_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0b0000_0000_0000_1111;
            vm.registers[2] = 0b0000_0000_0000_0011;
            let instr = build_and_reg(0, 1, 2);
            op_and(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b0000_0000_0000_0011);
            assert_eq!(vm.registers[COND as usize], FL_P);
        }
        #[test]
        fn and_sets_negative_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0b1111_1111_1111_1111;
            vm.registers[2] = 0b1000_0000_0000_0000;
            let instr = build_and_reg(0, 1, 2);
            op_and(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b1000_0000_0000_0000);
            assert_eq!(vm.registers[COND as usize], FL_N);
        }
        #[test]
        fn and_sets_zero_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0b0000_1111_0000_1111;
            vm.registers[2] = 0b1111_0000_1111_0000;
            let instr = build_and_reg(0, 1, 2);
            op_and(instr, &mut vm);
            assert_eq!(vm.registers[0], 0);
            assert_eq!(vm.registers[COND as usize], FL_Z);
        }
        #[test]
        fn ldr_positive_offset() {
            let mut vm = VM::new();
            vm.registers[1] = 0x3000;
            vm.mem_write(0x3005, 42);
            let instr = build_ldr(0, 1, 5);
            op_ldr(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldr_negative_offset() {
            let mut vm = VM::new();
            vm.registers[2] = 0x3000;
            vm.mem_write(0x2FFF, 42);
            let instr = build_ldr(0, 2, -1);
            op_ldr(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldr_max_positive_offset() {
            let mut vm = VM::new();
            vm.registers[1] = 0x3000;
            vm.mem_write(0x301F, 42);
            let instr = build_ldr(0, 1, 31);
            op_ldr(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldr_max_negative_offset() {
            let mut vm = VM::new();
            vm.registers[1] = 0x3000;
            vm.mem_write(0x2FE0, 42);
            let instr = build_ldr(0, 1, -32);
            op_ldr(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldr_wrapping() {
            let mut vm = VM::new();
            vm.registers[3] = 0x0000;
            vm.mem_write(0xFFFF, 42);
            let instr = build_ldr(0, 3, -1);
            op_ldr(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldr_sets_positive_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0x3000;
            vm.mem_write(0x3000, 5);
            let instr = build_ldr(0, 1, 0);
            op_ldr(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_P);
        }
        #[test]
        fn ldr_sets_negative_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0x3000;
            vm.mem_write(0x3000, -1i16 as u16);
            let instr = build_ldr(0, 1, 0);
            op_ldr(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_N);
        }
        #[test]
        fn ldr_sets_zero_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0x3000;
            vm.mem_write(0x3000, 0);
            let instr = build_ldr(0, 1, 0);
            op_ldr(instr, &mut vm);
            assert_eq!(vm.registers[0], 0);
            assert_eq!(vm.registers[COND as usize], FL_Z);
        }
        #[test]
        fn str_positive_offset() {
            let mut vm = VM::new();
            vm.registers[0] = 42;
            vm.registers[1] = 0x3000;
            let instr = build_str(0, 1, 3);
            op_str(instr, &mut vm);
            assert_eq!(vm.mem_read(0x3003), 42);
        }
        #[test]
        fn str_negative_offset() {
            let mut vm = VM::new();
            vm.registers[2] = 42;
            vm.registers[3] = 0x3000;
            let instr = build_str(2, 3, -1);
            op_str(instr, &mut vm);
            assert_eq!(vm.mem_read(0x2FFF), 42);
        }
        #[test]
        fn str_max_positive_offset() {
            let mut vm = VM::new();
            vm.registers[0] = 42;
            vm.registers[1] = 0x3000;
            let instr = build_str(0, 1, 31);
            op_str(instr, &mut vm);
            assert_eq!(vm.mem_read(0x301F), 42);
        }
        #[test]
        fn str_max_negative_offset() {
            let mut vm = VM::new();
            vm.registers[0] = 42;
            vm.registers[1] = 0x3000;
            let instr = build_str(0, 1, -32);
            op_str(instr, &mut vm);
            assert_eq!(vm.mem_read(0x2FE0), 42);
        }
        #[test]
        fn str_wrapping() {
            let mut vm = VM::new();
            vm.registers[0] = 42;
            vm.registers[1] = 0x0000;
            let instr = build_str(0, 1, -1);
            op_str(instr, &mut vm);
            assert_eq!(vm.mem_read(0xFFFF), 42);
        }
        #[test]
        fn not_happy_path() {
            let mut vm = VM::new();
            vm.registers[1] = 0b1111_0000_1111_0000;
            let instr = build_not(0, 1);
            op_not(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b0000_1111_0000_1111);
        }
        #[test]
        fn not_sets_positive_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0b1111_1111_1111_1110;
            let instr = build_not(0, 1);
            op_not(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b0000_0000_0000_0001);
            assert_eq!(vm.registers[COND as usize], FL_P);
        }
        #[test]
        fn not_sets_negative_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0b0000_0000_0000_0000;
            let instr = build_not(0, 1);
            op_not(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b1111_1111_1111_1111);
            assert_eq!(vm.registers[COND as usize], FL_N);
        }
        #[test]
        fn not_sets_zero_flag() {
            let mut vm = VM::new();
            vm.registers[1] = 0b1111_1111_1111_1111;
            let instr = build_not(0, 1);
            op_not(instr, &mut vm);
            assert_eq!(vm.registers[0], 0b0000_0000_0000_0000);
            assert_eq!(vm.registers[COND as usize], FL_Z);
        }
        #[test]
        fn ldi_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x3005, 0x4000);
            vm.mem_write(0x4000, 42);
            let instr = build_ldi(0, 5);
            op_ldi(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldi_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x2FFF, 0x5000);
            vm.mem_write(0x5000, 42);
            let instr = build_ldi(0, -1);
            op_ldi(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldi_max_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x30FF, 0x4000);
            vm.mem_write(0x4000, 42);
            let instr = build_ldi(0, 255);
            op_ldi(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldi_max_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x2F00, 0x5000);
            vm.mem_write(0x5000, 42);
            let instr = build_ldi(0, -256);
            op_ldi(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldi_wrapping() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x0000;
            vm.mem_write(0xFFFF, 0x6000);
            vm.mem_write(0x6000, 42);
            let instr = build_ldi(0, -1);
            op_ldi(instr, &mut vm);
            assert_eq!(vm.registers[0], 42);
        }
        #[test]
        fn ldi_sets_negative_flag() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x3000, 0x4000);
            vm.mem_write(0x4000, -1i16 as u16);
            let instr = build_ldi(0, 0);
            op_ldi(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_N);
        }
        #[test]
        fn ldi_sets_zero_flag() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.mem_write(0x3000, 0x4000);
            vm.mem_write(0x4000, 0);
            let instr = build_ldi(0, 0);
            op_ldi(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_Z);
        }
        #[test]
        fn sti_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[0] = 42;
            vm.mem_write(0x3001, 0x4000);
            let instr = build_sti(0, 1);
            op_sti(instr, &mut vm);
            assert_eq!(vm.mem_read(0x4000), 42);
        }
        #[test]
        fn sti_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[2] = 42;
            vm.mem_write(0x2FFF, 0x5000);
            let instr = build_sti(2, -1);
            op_sti(instr, &mut vm);
            assert_eq!(vm.mem_read(0x5000), 42);
        }
        #[test]
        fn sti_max_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[0] = 42;
            vm.mem_write(0x30FF, 0x4000);
            let instr = build_sti(0, 255);
            op_sti(instr, &mut vm);
            assert_eq!(vm.mem_read(0x4000), 42);
        }
        #[test]
        fn sti_max_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            vm.registers[0] = 42;
            vm.mem_write(0x2F00, 0x5000);
            let instr = build_sti(0, -256);
            op_sti(instr, &mut vm);
            assert_eq!(vm.mem_read(0x5000), 42);
        }
        #[test]
        fn sti_pc_wrapping() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x0000;
            vm.registers[1] = 42;
            vm.mem_write(0xFFFF, 0x6000);
            let instr = build_sti(1, -1);
            op_sti(instr, &mut vm);
            assert_eq!(vm.mem_read(0x6000), 42);
        }
        #[test]
        fn jmp_happy_path() {
            let mut vm = VM::new();
            vm.registers[2] = 42;
            let instr = build_jmp(2);
            op_jmp(instr, &mut vm);
            assert_eq!(vm.registers[PC as usize], 42);
        }
        #[test]
        fn lea_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            let instr = build_lea(0, 5);
            op_lea(instr, &mut vm);
            assert_eq!(vm.registers[0], 0x3005);
        }
        #[test]
        fn lea_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            let instr = build_lea(0, -1);
            op_lea(instr, &mut vm);
            assert_eq!(vm.registers[0], 0x2FFF);
        }
        #[test]
        fn lea_max_positive_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            let instr = build_lea(0, 255);
            op_lea(instr, &mut vm);
            assert_eq!(vm.registers[0], 0x30FF);
        }
        #[test]
        fn lea_max_negative_offset() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            let instr = build_lea(0, -256);
            op_lea(instr, &mut vm);
            assert_eq!(vm.registers[0], 0x2F00);
        }
        #[test]
        fn lea_wrapping() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x0000;
            let instr = build_lea(0, -1);
            op_lea(instr, &mut vm);
            assert_eq!(vm.registers[0], 0xFFFF);
        }
        #[test]
        fn lea_sets_positive_flag() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x0001;
            let instr = build_lea(0, 0);
            op_lea(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_P);
        }
        #[test]
        fn lea_sets_negative_flag() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x8000;
            let instr = build_lea(0, 0);
            op_lea(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_N);
        }
        #[test]
        fn lea_sets_zero_flag() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x0000;
            let instr = build_lea(0, 0);
            op_lea(instr, &mut vm);
            assert_eq!(vm.registers[COND as usize], FL_Z);
        }
        #[test]
        fn trap_saves_pc_in_r7() {
            let mut vm = VM::new();
            vm.registers[PC as usize] = 0x3000;
            let instr = build_trap(0xFF);
            let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                op_trap(instr, &mut vm);
            }));
            assert_eq!(vm.registers[R7 as usize], 0x3000);
        }
        #[test]
        #[should_panic]
        fn trap_unknown_vector_panics() {
            let mut vm = VM::new();
            op_trap(build_trap(0xFF), &mut vm);
        }
    }
    mod trapcodes {
        use super::*;
        use crate::vm::Keyboard;
        use crate::vm::TerminalOutput;
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

        #[test]
        fn trap_getc_reads_character_and_updates_flags() {
            let mut vm = VM::new();
            vm.keyboard = Box::new(MockKeyboard { key: Some(0x0041) }); // 'A'
            trap_getc(&mut vm);
            assert_eq!(vm.registers[R0 as usize], 0x0041);
            assert_eq!(vm.registers[COND as usize], FL_P);
        }
        #[test]
        fn trap_out_outputs_masked_r0_and_leaves_r0_unchanged() {
            let mut vm = VM::new();
            let shared_buffer = Rc::new(RefCell::new(Vec::new()));
            vm.output = Box::new(MockOutput {
                buffer: Rc::clone(&shared_buffer),
            });
            let value = 0xFF41; // 'A' with upper bits set to test masking
            vm.registers[R0 as usize] = value;
            trap_out(&mut vm);
            assert_eq!(*shared_buffer.borrow(), vec![0x41]);
            assert_eq!(vm.registers[R0 as usize], value);
        }
        #[test]
        fn trap_puts_outputs_null_terminated_string_and_masks_upper_bits() {
            let mut vm = VM::new();
            let shared_buffer = Rc::new(RefCell::new(Vec::new()));
            vm.output = Box::new(MockOutput {
                buffer: Rc::clone(&shared_buffer),
            });
            let address = 0x3000;
            vm.registers[R0 as usize] = address;
            vm.memory[address as usize] = 0xFF48; // 'H' with upper bits to test masking
            vm.memory[(address + 1) as usize] = 0xFF69; // 'i' with upper bits to test masking
            vm.memory[(address + 2) as usize] = 0x0000; // '\0'
            vm.memory[(address + 3) as usize] = 0xFFFF;
            trap_puts(&mut vm);
            assert_eq!(*shared_buffer.borrow(), vec![0x48, 0x69]);
            assert_eq!(vm.registers[R0 as usize], address);
        }
        #[test]
        fn trap_in_reads_character_and_updates_flags() {
            let mut vm = VM::new();
            vm.keyboard = Box::new(MockKeyboard { key: Some(0x0041) }); // 'A'
            trap_in(&mut vm);
            assert_eq!(vm.registers[R0 as usize], 0x0041);
            assert_eq!(vm.registers[COND as usize], FL_P);
        }
        #[test]
        fn trap_putsp_outputs_packed_string_and_handles_odd_length() {
            let mut vm = VM::new();
            let shared_buffer = Rc::new(RefCell::new(Vec::new()));
            vm.output = Box::new(MockOutput {
                buffer: Rc::clone(&shared_buffer),
            });
            let base_addr = 0x3000;
            vm.registers[Registers::R0 as usize] = base_addr;
            vm.memory[base_addr as usize] = 0x4241; // 'A' + 'B'
            vm.memory[(base_addr + 1) as usize] = 0x0043; // 'C' + '\0'
            trap_putsp(&mut vm);
            assert_eq!(*shared_buffer.borrow(), vec![0x41, 0x42, 0x43]);
            assert_eq!(vm.registers[Registers::R0 as usize], base_addr);
        }
        #[test]
        fn trap_halt_stops_execution() {
            let mut vm = VM::new();
            vm.running = true;
            trap_halt(&mut vm);
            assert_eq!(vm.running, false);
        }
    }
}
