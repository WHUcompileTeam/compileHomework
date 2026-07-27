# ToyC Compiler in OCaml

This project implements a ToyC-to-RISC-V32 compiler for the compiler practice assignment.

## Build

```sh
dune build
```

The local Windows environment used during development runs Dune through opam:

```sh
opam exec -- dune build
```

## Run

```sh
dune exec compiler -- < input.tc > output.s
dune exec compiler -- -opt < input.tc > output.s
```

The compiler reads ToyC from `stdin` and writes RISC-V32 assembly to `stdout`.

## Assignment Constraints Reflected Here

- Implementation language: OCaml.
- Build system: Dune, with `(lang dune 3.19)`.
- No Clang/LLVM or ready compiler framework is used.
- Front-end generation uses `ocamllex` and `ocamlyacc`, both within the standard OCaml toolchain.
- `-opt` enables AST constant propagation/folding, dead-branch cleanup, unreachable-tail cleanup, and assembly peephole cleanup.

## Module Layout

- `lib/ast.ml`: ToyC AST.
- `lib/lexer_impl.mll` / `lib/lexer.ml`: `ocamllex`-based scanning plus the public lexer wrapper.
- `lib/grammar.mly` / `lib/parser.ml`: `ocamlyacc` grammar plus the public parser wrapper.
- `lib/semant.ml`: global/function environment and compile-time global constant evaluation.
- `lib/tcg.ml`, `lib/cfg.ml`, `lib/opt.ml`: explicit IR/CFG/optimization stage boundaries.
- `lib/asm_opt.ml`: simple assembly peephole optimization for `-opt`.
- `lib/codegen.ml`: RISC-V32 assembly backend with stack frames, short-circuit branches, function calls, and stack-passed arguments after `a0`-`a7`.
- `lib/driver.ml`: stdin/stdout CLI and error handling.
- `bin/compiler.ml`: executable entry point.
- `REPORT.md`: practice report.

## Smoke Tests

ToyC samples live in `test/`.

```sh
dune exec compiler -- -opt < test/basic.tc > /tmp/basic.s
dune exec compiler -- -opt < test/functions.tc > /tmp/functions.s
python tools/run_smoke_tests.py
```

`tools/run_smoke_tests.py` builds the project, compiles all valid samples in normal and `-opt` modes, runs the emitted assembly with a RISC-V32 subset interpreter, and checks invalid semantic samples are rejected.

No external RISC-V assembler/emulator was available in the local Windows environment. Winget installation attempts for LLVM and QEMU failed during download, so generated assembly was validated with the checked-in interpreter for the emitted instruction subset.
