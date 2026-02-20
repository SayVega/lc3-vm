use lc3_vm::{TerminalGuard, VM};
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
        if vm.load_image(image_path).is_err() {
            println!("failed to load image: {}", image_path);
            process::exit(1);
        }
    }

    vm.run();
}
