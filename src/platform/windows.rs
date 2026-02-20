#[cfg(windows)]
use crate::vm::Keyboard;
use std::io::{self, Read};
use windows_sys::Win32::Foundation::{HANDLE, INVALID_HANDLE_VALUE};
use windows_sys::Win32::System::Console::*;
use windows_sys::Win32::System::Threading::WaitForSingleObject;

pub struct TerminalGuard {
    handle: HANDLE,
    original_mode: u32,
}

impl TerminalGuard {
    pub fn new() -> Self {
        unsafe {
            let handle = GetStdHandle(STD_INPUT_HANDLE);
            if handle == INVALID_HANDLE_VALUE {
                panic!("Failed to get STDIN handle");
            }

            let mut original_mode: u32 = 0;
            if GetConsoleMode(handle, &mut original_mode) == 0 {
                panic!("Failed to get console mode");
            }

            let new_mode = original_mode & !ENABLE_ECHO_INPUT & !ENABLE_LINE_INPUT;
            if SetConsoleMode(handle, new_mode) == 0 {
                panic!("Failed to set console mode");
            }

            FlushConsoleInputBuffer(handle);

            return TerminalGuard {
                handle,
                original_mode,
            };
        }
    }
}
impl Drop for TerminalGuard {
    fn drop(&mut self) {
        unsafe {
            SetConsoleMode(self.handle, self.original_mode);
        }
    }
}

pub struct PlatformKeyboard;

impl PlatformKeyboard {
    pub fn new() -> Self {
        return Self;
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
        let handle = GetStdHandle(STD_INPUT_HANDLE);
        if handle == INVALID_HANDLE_VALUE {
            return false;
        }
        WaitForSingleObject(handle, 0) == windows_sys::Win32::Foundation::WAIT_OBJECT_0
    }
}
