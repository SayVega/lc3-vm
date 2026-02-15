use crate::VM;
use Registers::*;
enum Operations {
    OPBR = 0, /* branch */
    OPADD,    /* add  */
    OPLD,     /* load */
    OPST,     /* store */
    OPJSR,    /* jump register */
    OPAND,    /* bitwise and */
    OPLDR,    /* load register */
    OPSTR,    /* store register */
    OPRTI,    /* unused */
    OPNOT,    /* bitwise not */
    OPLDI,    /* load indirect */
    OPSTI,    /* store indirect */
    OPJMP,    /* jump */
    OPRES,    /* reserved (unused) */
    OPLEA,    /* load effective address */
    OPTRAP,   /* execute trap */
}
enum Registers {
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

pub const REGISTER_COUNT: usize = 10;

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
    let addr = pc.wrapping_add(pc_offset);

    vm.registers[r0] = vm.mem_read(addr);

    vm.update_flags(r0);
}

pub fn op_st(instr: u16, vm: &mut VM) {
    let r0 = ((instr >> 9) & 0x7) as usize;
    let pc_offset = sign_extend(instr & 0x1FF, 9);

    let pc = vm.registers[PC as usize];
    let addr = pc.wrapping_add(pc_offset);

    let value = vm.registers[r0];

    vm.mem_write(addr, value);
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
    let addr = base.wrapping_add(offset);

    vm.registers[r0] = vm.mem_read(addr);

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
