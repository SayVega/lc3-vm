use lc3_vm::{TerminalGuard, VM};
use std::env;
use std::process;

fn main() {
    let _terminal = TerminalGuard::new();
    let mut vm = VM::new();
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Error: Missing input file.");
        eprintln!("Usage: lc3-vm <path_to_image.obj>");
        eprintln!("Example: make run ARGS=\"./image.obj\"");
        process::exit(2);
    }

    for image_path in &args[1..] {
        if vm.load_image(image_path).is_err() {
            eprintln!("Error: File '{}' not found.", image_path);
            process::exit(1);
        }
    }

    vm.run();
}
