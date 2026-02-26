# bats

The self-hosting Bats compiler. Bats is a programming language that compiles to ATS2.

## Pipeline

`.bats` → lexer → emitter → `.sats`/`.dats` → patsopt → `_dats.c` → cc → binary

## Build

```bash
# Bootstrap build (first time, requires bats-old)
bats-old build --repository ../repository-prototype

# Self-compilation
dist/debug/bats build --repository ../repository-prototype

# Type-check only
dist/debug/bats check --repository ../repository-prototype
```

## Architecture

- `src/bin/bats.bats` — entry point (argument parsing, command dispatch)
- `src/helpers.bats` — globals, string/builder helpers, process spawning, file I/O
- `src/lexer.bats` — tokenizer (produces spans from `.bats` source)
- `src/emitter.bats` — code generator (produces `.sats`/`.dats` from spans)
- `src/build.bats` — build pipeline (preprocessing, patsopt, cc, link)
- `src/commands.bats` — subcommands (init, test, upload, check, run, etc.)

## Commands

- `bats build [--only debug|release|wasm]` — compile the project
- `bats check` — type-check without linking
- `bats run [--bin name]` — build and run a binary
- `bats lock --repository <dir>` — resolve dependencies
- `bats init binary|library` — create a new project
- `bats test` — build and run tests
- `bats upload --repository <dir>` — package and publish a library
- `bats clean` — remove build artifacts
- `bats tree` — show dependency tree
- `bats add <package>` / `bats remove <package>` — manage dependencies

## Dependencies

argparse, array, arith, builder, env, file, path, process, result, sha256, str, toml
