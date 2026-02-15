#[cfg(unix)]
mod unix;
#[cfg(unix)]
pub use unix::PlatformKeyboard;
#[cfg(unix)]
pub use unix::TerminalGuard;

#[cfg(windows)]
mod windows;
#[cfg(windows)]
pub use windows::PlatformKeyboard;
#[cfg(windows)]
pub use windows::TerminalGuard;
