use std::env;
use std::process;
use lc3_vm::memory::{read_image, MAX_MEMORY};


fn main() {
    let args: Vec<String> = env::args().collect();
    let mut memory = [0u16;MAX_MEMORY];
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