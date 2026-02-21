# LC-3 Virtual Machine

### Prerequisites
- Rust (latest stable).
- `make` (optional).

## Installation
Clone the repository and navigate to the directory
```Bash
git clone https://github.com/SayVega/lc3-vm.git
cd lc3-vm
```
To use it system-wide
```Bash
cargo install --path .
```
## Usage

### Using make
Compile the binary:
```Bash
make build
```
Run the VM by providing an LC-3 .obj file as argument:
```Bash
make run ARGS="./image.obj"
```
### Using cargo (Manual)
For better performance always use `--release` flag

Build:
```Bash
cargo build --release
```
Run:
```Bash
cargo run -- <path_to_obj_file>
```

### Testing
The suite includes integration tests and unit tests.
```Bash
make test
```

### Technical Details

#### Memory Map
The VM emulates a 16-bit address space ($2^{16}$) words.
- **0x0000 - 0x00FF**: Trap vector table.
- **0xFE00 - 0xFFFF**: Memory-mapped I/0 Registers.

#### Supported trap codes
The following system calls are implemented to handle I/0 and execution contro:


 Vector | Name  | Description                                                     |
|--------|-------|-----------------------------------------------------------------|
| x20    | GETC  | Read a single character from keyboard (no echo).               |
| x21    | OUT   | Write the character in R0 to the display.                      |
| x22    | PUTS  | Write a null-terminated string to the display.                 |
| x23    | IN    | Print a prompt and read a character (with echo).               |
| x24    | PUTSP | Write a packed string (2 characters per word).                 |
| x25    | HALT  | Stop execution and terminate the virtual machine.              |

#### Terminal Raw Mode
The emulator puts the terminal into Raw Mode during execution. This allows the VM to capture keystrokes instantly (without waiting for the `Enter` key).

#### Multiplatform support
The codebase is designed to be cross-platform:
- Unix/Linux/macOS: Uses `termios` for raw mode management.
- Windows: Uses the Windows API to handle console mode flags.
