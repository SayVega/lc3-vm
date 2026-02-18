#[cfg(unix)]
use crate::Keyboard;
use libc::{
    ECHO, FD_SET, FD_ZERO, ICANON, STDIN_FILENO, TCSANOW, VMIN, VTIME, fd_set, select, tcgetattr, tcsetattr,
    termios, timeval,
};
use std::io::{self, Read};
use std::mem;
use std::ptr;

pub struct TerminalGuard {
    original: termios,
}

impl TerminalGuard {
    pub fn new() -> Self {
        unsafe {
            let mut terminal_io: termios = mem::zeroed();
            tcgetattr(STDIN_FILENO, &mut terminal_io);
            let original = terminal_io;
            terminal_io.c_lflag &= !(ICANON | ECHO);
            terminal_io.c_cc[VMIN] = 1;
            terminal_io.c_cc[VTIME] = 0;
            tcsetattr(STDIN_FILENO, TCSANOW, &terminal_io);
            return TerminalGuard { original };
        }
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

impl PlatformKeyboard {
    pub fn new() -> Self {
        Self
    }
}

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
    unsafe {
        let mut readfds: fd_set = mem::zeroed();
        FD_ZERO(&mut readfds);
        FD_SET(STDIN_FILENO, &mut readfds);
        let mut timeout = timeval {
            tv_sec: 0,
            tv_usec: 0,
        };
        return select(
            STDIN_FILENO + 1,
            &mut readfds,
            ptr::null_mut(),
            ptr::null_mut(),
            &mut timeout,
        ) != 0;
    }
}
