# SPDX-FileCopyrightText: The im-pathtree authors
# SPDX-License-Identifier: CC0-1.0

# just manual: https://github.com/casey/just/#readme

_default:
    @just --list

# Format source code
fmt:
    cargo fmt --all

# Run clippy with selected feature selections
clippy:
    cargo clippy --locked --no-deps --all-targets --no-default-features -- -D warnings --cap-lints warn
    cargo clippy --locked --no-deps --all-targets --all-features -- -D warnings --cap-lints warn

# Run tests with selected feature selections
test:
    RUST_BACKTRACE=1 cargo test --locked --no-default-features -- --nocapture
    RUST_BACKTRACE=1 cargo test --locked --all-features -- --nocapture

# Set up (and update) tooling
setup:
    # Ignore rustup failures, because not everyone might use it
    rustup self update || true
    # cargo-edit is needed for `cargo upgrade`
    cargo install cargo-edit just
    pip install -U pre-commit
    #pre-commit install --hook-type commit-msg --hook-type pre-commit

# Upgrade (and update) dependencies
upgrade: setup
    pre-commit autoupdate
    cargo upgrade --incompatible --pinned
    cargo update

# Run pre-commit hooks
pre-commit:
    pre-commit run --all-files
