.PHONY: build run test fmt

build:
	cargo build

run:
	cargo run

test:
	cargo test

fmt:
	cargo fmt --all -- --check