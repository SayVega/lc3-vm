# Contributing

Contributions are welcome via pull requests.

## Guidelines

- Keep the code simple and explicit
- Follow standard Rust formatting (`make fmt`)
- New functionality should include tests
- **Performance:** Prefer `wrapping_add` for 16-bit arithmetic.
- **I/O:** Use the existing `Keyboard` and `TerminalOutput` traits; do not use `stdin`/`stdout` directly in instruction logic.