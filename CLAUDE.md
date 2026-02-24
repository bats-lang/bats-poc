# bats

## Goals

bats must be:

1. **The bats compiler**: Self-hosting bats compiler written in Bats. The old Rust implementation is archived at `/home/moshez/src/bats-lang/bats-old/`.

2. **Safe**: `unsafe = false` (or no `unsafe` key) in `bats.toml`. No `$UNSAFE begin...end` blocks in bats source. C code belongs in library packages (file, process, sha256, etc.) that expose safe typed APIs. If a package must be `unsafe = true`, keep the unsafety minimal — expose safe wrappers so dependents can be `unsafe = false`.

## Build & Test

```bash
dist/debug/bats check --repository /home/moshez/src/bats-lang/repository-prototype
dist/debug/bats build --repository /home/moshez/src/bats-lang/repository-prototype
```

## Architecture

Single binary: `src/bin/bats.bats`

Dependencies: argparse, array, arith, builder, env, file, path, process, result, sha256, str, toml

## Workflow

All changes, even one byte, in ANY repo in bats-lang, must go through branch -> PR -> green -> merge. NEVER commit directly to main. Use `gh pr merge --merge` (no squash).

When creating a new repo: push an empty initial commit to main first (`git commit --allow-empty -m "Initial commit" && git push -u origin main`), then create a feature branch for the actual content. The first branch you push becomes the default, so main must exist before any feature branches.

Never blocked by another PR — add finishing that PR to the task list instead.

Never ask permission to keep going. Keep going until the success criterion is met.

## Allowed Divergences from old Rust bats

bats uses `--only <value>` (repeatable) instead of the old Rust bats' `--release` flag and `--only native|wasm`. Values: `debug`, `release`, `native`, `wasm`. Multiple `--only` flags narrow the build matrix. Default (no `--only`): build all. Example: `--only debug --only native` builds only debug native. This is the only allowed divergence. All other flags and behaviors must match the old Rust bats exactly.

## Task Rules

A task should never be more than one thing: if it requires the word "and", for example, it should be broken up. If it refers to plurals, it should be broken up. If it has a comma, it should be broken up.
