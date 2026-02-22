# bats-poc

## Goals

bats-poc must be:

1. **Complete replacement**: Full feature parity with the Rust `bats` compiler at `/home/moshez/src/bats-lang/bats/`. All CLI commands, flags, and behaviors must match.

2. **Safe**: `unsafe = false` (or no `unsafe` key) in `bats.toml`. No `$UNSAFE begin...end` blocks in bats-poc source. C code belongs in library packages (file, process, sha256, etc.) that expose safe typed APIs.

## Build & Test

```bash
PATSHOME=~/.bats/ats2 dist/debug/bats-poc build   # build self
bats --run-in /home/moshez/src/bats-lang/bats-poc build --repository /home/moshez/src/bats-lang/repository-prototype
bats --run-in /home/moshez/src/bats-lang/bats-poc check --repository /home/moshez/src/bats-lang/repository-prototype
```

## Architecture

Single binary: `src/bin/bats-poc.bats`

Dependencies: array, arith, builder, env, file, path, process, result, sha256, str, toml

## Workflow

All changes via PRs (never direct to main). Use `gh pr merge --merge` (no squash).

## Task Rules

A task should never be more than one thing: if it requires the word "and", for example, it should be broken up. If it refers to plurals, it should be broken up. If it has a comma, it should be broken up.
