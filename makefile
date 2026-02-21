.PHONY: build run test fmt clean

build:
	cargo build --release

run:
	cargo run --release -- $(ARGS)

test:
	cargo test

fmt:
	cargo fmt --all -- --check

clean:
	cargo clean