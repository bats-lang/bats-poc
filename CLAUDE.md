# bats

## Goals

bats must be:

1. **The bats compiler**: Self-hosting bats compiler written in Bats. The old Rust implementation is archived at `/home/moshez/src/bats-lang/bats-old/`.

2. **Safe**: `unsafe = false` (or no `unsafe` key) in `bats.toml`. No `$UNSAFE begin...end` blocks in bats source. No `$extfcall` — it is an unsafe construct. C code belongs in library packages (file, process, sha256, etc.) that expose safe typed APIs. If a package must be `unsafe = true`, keep the unsafety minimal — expose safe wrappers so dependents can be `unsafe = false`. Being in an unsafe package is not carte blanche to add more unsafety.

## Build & Test

```bash
dist/debug/bats check --repository /home/moshez/src/bats-lang/repository-prototype
dist/debug/bats build --repository /home/moshez/src/bats-lang/repository-prototype
```

## Architecture

Entry point: `src/bin/bats.bats`
Shared modules: `src/helpers.bats`, `src/lexer.bats`, `src/emitter.bats`, `src/build.bats`, `src/commands.bats`

Dependencies: argparse, array, arith, builder, env, file, path, process, result, sha256, str, toml

## Workflow

All changes, even one byte, in ANY repo in bats-lang, must go through branch -> PR -> green -> merge. NEVER commit directly to main. Use `gh pr merge --merge` (no squash).

When creating a new repo: push an empty initial commit to main first (`git commit --allow-empty -m "Initial commit" && git push -u origin main`), then create a feature branch for the actual content. The first branch you push becomes the default, so main must exist before any feature branches.

Never blocked by another PR — add finishing that PR to the task list instead.

Never ask permission to keep going. Keep going until the success criterion is met.

## Allowed Divergences from old Rust bats

bats uses `--only <value>` (repeatable) instead of the old Rust bats' `--release` flag and `--only native|wasm`. Values: `debug`, `release`, `native`, `wasm`. Multiple `--only` flags narrow the build matrix. Default (no `--only`): build all. Example: `--only debug --only native` builds only debug native. This is the only allowed divergence. All other flags and behaviors must match the old Rust bats exactly.

## Safety Enforcement

Unsafe constructs (`castfn`, `$extfcall`, `$extval`, `$extype`, `$extkind`, `praxi`, `extern`, `assume`, `fun` without termination metric, `#pub prfun`/`prfn` without `primplement`) are detected by the lexer (span kind 5) and **enforced** by the emitter. They are rejected outside `$UNSAFE begin...end` blocks in ALL packages — both safe and unsafe. `$UNSAFE begin...end` blocks themselves are rejected in `unsafe = false` packages.

## Problem Resolution

A problem already existing is never a good reason to ignore it. Problems must be fixed. Safety problems must be prioritized.

## Safety Philosophy

Never add runtime checks (assertions, bounds checks at runtime, abort-on-overflow). The type system must prevent bad states at compile time. If you cannot prove safety statically, the API is wrong — fix the API, don't add a runtime check. Runtime checks are a sign that the type system is not being used correctly. The whole point of ATS2 and Bats is that safety is enforced by the compiler, not by runtime guards.

Segfaults must never happen. A segfault means something is fundamentally wrong — do not work around it, do not accept it, do not split files to avoid it. Find the root cause and fix it systemically. If it's caused by unbounded recursion, figure out how ATS2 is supposed to handle this (it has tail-call optimization). Use web search to understand the correct solution. Do not settle for less than correct.

Don't guess. Don't "try" things. Read the code. Carefully reason about what is happening. Understand before acting.

Do not assume Linux. Code must be portable (macOS, Linux, BSDs). Do not use `/proc/self/exe` or other Linux-specific paths.

Do not use bats-old unless it's an emergency. The self-hosting compiler is the primary build tool.

Fix problems regardless of size. Never say "too large for this session" or defer work. Do the work.

## Task Rules

A task should never be more than one thing: if it requires the word "and", for example, it should be broken up. If it refers to plurals, it should be broken up. If it has a comma, it should be broken up.
