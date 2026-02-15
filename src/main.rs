use lc3_vm::memory::{MAX_MEMORY, read_image};
use lc3_vm::platform::TerminalGuard;
use std::env;
use std::process;

enum Instructions {
    R0 = 0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    RPC,
    RCOND,
    RCOUNT,
}
pub const PC_START: usize = 0x3000;

fn main() {
    let _terminal = TerminalGuard::new();

    let args: Vec<String> = env::args().collect();
    let mut memory = [0u16; MAX_MEMORY];
    if args.len() < 2 {
        println!("lc3 [image-file1] ...");
        process::exit(2);
    }

    for image_path in &args[1..] {
        if !read_image(image_path, &mut memory).is_ok() {
            println!("failed to load image: {}", image_path);
            process::exit(1);
        }
    }
}
