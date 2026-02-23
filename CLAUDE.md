# bats-poc

## Goals

bats-poc must be:

1. **Complete replacement**: Full feature parity with the Rust `bats` compiler at `/home/moshez/src/bats-lang/bats/`. All CLI commands, flags, and behaviors must match.

2. **Safe**: `unsafe = false` (or no `unsafe` key) in `bats.toml`. No `$UNSAFE begin...end` blocks in bats-poc source. C code belongs in library packages (file, process, sha256, etc.) that expose safe typed APIs.

## Build & Test

Only use bats-poc to build bats-poc. Never use the Rust bats.

```bash
dist/debug/bats-poc check --repository /home/moshez/src/bats-lang/repository-prototype
dist/debug/bats-poc build --repository /home/moshez/src/bats-lang/repository-prototype
```

## Architecture

Single binary: `src/bin/bats-poc.bats`

Dependencies: argparse, array, arith, builder, env, file, path, process, result, sha256, str, toml

## Workflow

All changes, even one byte, in ANY repo in bats-lang, must go through branch -> PR -> green -> merge. NEVER commit directly to main. Use `gh pr merge --merge` (no squash).

Never blocked by another PR — add finishing that PR to the task list instead.

Never ask permission to keep going. Keep going until the success criterion is met.

## Allowed Divergences from Rust bats

bats-poc uses `--only <value>` (repeatable) instead of the Rust bats' `--release` flag and `--only native|wasm`. Values: `debug`, `release`, `native`, `wasm`. Multiple `--only` flags narrow the build matrix. Default (no `--only`): build all. Example: `--only debug --only native` builds only debug native. This is the only allowed divergence. All other flags and behaviors must match the Rust bats exactly.

## Task Rules

A task should never be more than one thing: if it requires the word "and", for example, it should be broken up. If it refers to plurals, it should be broken up. If it has a comma, it should be broken up.
