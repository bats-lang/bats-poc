# Writing Bats

Bats is a language that compiles to ATS2. You write `.bats` files and the
compiler generates `.sats` (declarations) and `.dats` (implementations)
automatically. You never write `.sats` or `.dats` files by hand.

## Build commands

```bash
bats build [--release]    # Build binary project
bats check                # Type-check without linking
bats clean                # Remove generated artifacts
```

## Project layout

- `bats.toml` — package config (`[package]` with `name`, `kind`, optional `version`, `trunk`)
- `src/lib.bats` — library entry point (kind = "lib")
- `src/bin/<name>.bats` — binary entry points (kind = "bin")
- `src/*.bats` — shared modules (available to all binaries)

## Bats-specific syntax

Everything not listed below is standard ATS2 syntax passed through unchanged.

### `#pub` — public declarations

Marks a declaration as public (exported to `.sats`). Continues until a blank
line or a top-level keyword (`fun`, `val`, `implement`, `typedef`, etc.):

```bats
#pub fun greet (name: string): void

implement greet (name) = println! ("hello ", name)
```

### `#use` — package imports

```bats
#use example.com/world as W
#use mylib as M no_mangle
```

Access imported items with `$ALIAS.member`:

```bats
val x = $W.greeting ()
```

### `#target` — platform target

```bats
#target native
#target wasm
```

### `$UNSAFE begin...end` — unsafe blocks

Required wrapper for inline C code (`%{...%}`):

```bats
$UNSAFE begin

%{
int square(int x) { return x * x; }
%}

end
```

### Entry point

Binary entry points use `implement main0`:

```bats
implement main0 () = println! ("hello, world!")
```

## ATS2 essentials

- `println!` has a bang: `println! ("text")`
- `fun` declares and defines functions
- `val` binds immutable values
- `var` binds mutable values
- `implement` provides function bodies
- Pattern matching: `case+ x of | 0 => ... | n => ...`
- Closures: `lam (x: int): int => x + 1`
- Types: `int`, `string`, `bool`, `void`, `list0(int)`, etc.
- No semicolons at end of expressions (except `val _ = expr;` to discard)
- `let...in...end` for local bindings:
  ```
  val result = let
    val x = 1
    val y = 2
  in
    x + y
  end
  ```

## Common patterns

Library with public API:

```bats
#pub fun add (x: int, y: int): int

implement add (x, y) = x + y
```

Binary using a library:

```bats
#use example.com/mylib as M

implement main0 () = println! (M.add (1, 2))
```

## Important rules

- Never edit files in `build/` — `.sats`, `.dats`, and `_dats.c` files there are generated
- Every `#pub fun` needs a corresponding `implement` in the same file
- Only files in `src/bin/` should have `implement main0`
- Shared modules in `src/` must NOT have `implement main0`
