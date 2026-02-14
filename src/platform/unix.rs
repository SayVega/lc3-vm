#[cfg(unix)]
mod platform {
    use crate::Keyboard;
    use libc::{
        ECHO, FD_SET, FD_ZERO, ICNON, STDIN_FILENO, TCANOW, fd_set, select, tcgetattr, tcsetattr,
        termios, timeval,
    };
    use std::io::{self, Read};
    use std::mem;
    use std::ptr;

    pub struct TerminalGuard {
        original: termios,
    }

    impl TerminalGuard {
        pub unsafe fn new() -> Self {
            let mut terminal_io: termios = mem::zeroed;
            tcgetattr(STDIN_FILENO, &mut terminal_io);
            let original = terminal_io;
            terminal_io.c_flag &= !(ICANON | ECHO);
            tcsetattr(STDIN_FILENO, TCSANOW, &terminal_io);

            return TerminalGuard { original };
        }
    }

    impl Drop for TerminalGuard {
        fn drop(&mut self) {
            unsafe {
                tcsetattr(STDIN_FILENO, TCSANOW, &self.original);
            }
        }
    }

    pub struct PlatformKeyboard;

    impl Keyboard for PlatformKeyboard {
        fn check_key(&mut self) -> Option<u16> {
            unsafe {
                if check_key_internal() {
                    let mut buffer = [0u8; 1];
                    io::stdin().read_exact(&mut buffer).ok()?;
                    return Some(buffer[0] as u16);
                } else {
                    return None;
                }
            }
        }
    }

    unsafe fn check_key_internal() -> bool {
        return (select(
            STDIN_FILENO + 1,
            &mut readfds,
            ptr::null_mut(),
            ptr::null_mut(),
            &timeout,
        ) != 0);
    }
}
