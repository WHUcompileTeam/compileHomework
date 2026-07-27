# ToyC OCaml Compiler Handoff

## Source Constraints Read From PDF

- Language choice: OCaml, target version in PDF is OCaml 5.3.0.
- Build system: Dune 3.19. This project uses `(lang dune 3.19)`.
- Input/output contract: read ToyC source from `stdin`; write RISC-V32 assembly to `stdout`; `stderr` is unrestricted.
- Optional runtime flag: accept `-opt` for optimization mode. The compiler may enable optimizations or ignore it.
- Allowed third-party/parser tooling for OCaml: `ocamllex`, `ocamlyacc`, `Menhir`.
- Chosen implementation: `ocamllex` + `ocamlyacc`, staying within the standard OCaml toolchain and assignment-allowed parser tooling.
- Forbidden approach: do not wrap or reuse ready compiler frameworks such as Clang/LLVM.
- Required source language: ToyC with global/local `int` variables, `const`, functions returning `int` or `void`, block scopes, `if/else`, `while`, `break`, `continue`, `return`, arithmetic/relational/logical expressions, comments, and C-like semantics.
- Required target: executable RISC-V32 assembly. Program result is `main` return value / process exit code.

## Planned Pipeline

Teacher-suggested pipeline:

```text
code -> parser_to_AST -> cg_to_CFG(DAG) -> opt_to_CFG -> TCG_TO_TR -> schedule and ra_to_asm
```

Implemented project mapping:

- `Lexer`: source text to tokens.
- `Parser` / `Grammar`: parser_to_AST implemented with an `ocamlyacc` grammar and a small wrapper module.
- `Ast`: shared syntax tree.
- `Semant`: semantic checks for scopes, const rules, calls, returns, loops, void values, globals, and compile-time initialization.
- `Asm_opt`: assembly peephole pass used by `-opt`.
- `Cfg` / `Tcg` / `Opt`: explicit intermediate-stage modules for CFG/three-address/DAG-style optimization hooks.
- `Codegen`: TCG/TR lowering plus local scheduling/register-allocation decisions, emitting RISC-V32 assembly.
- `bin/compiler.ml`: CLI, stdin/stdout, `-opt` flag.
- `REPORT.md`: practice report covering design, semantics, backend, optimization, and tests.

## Task Progress

- [x] Locate and read `编译系统实践(1).pdf`.
- [x] Extract PDF constraints and write them here.
- [x] Choose Dune OCaml project structure.
- [x] Implement AST, lexer, and parser.
- [x] Implement semantic environment and constant evaluation.
- [x] Implement IR/CFG/optimization scaffolding.
- [x] Implement RISC-V32 assembly backend.
- [x] Add CLI and `-opt` handling.
- [x] Add tests and sample ToyC programs.
- [x] Add practice report document.
- [x] Build with `opam exec -- dune build`.
- [x] Run end-to-end compiler smoke tests.
- [x] If a RISC-V assembler/emulator is unavailable locally, document that verification gap.

## Verification Completed

- `opam exec -- dune build` succeeds.
- `opam exec -- dune exec compiler --` generated assembly for every `test/*.tc` sample.
- `opam exec -- dune exec compiler -- -opt` generated assembly for every `test/*.tc` sample.
- `python tools/run_smoke_tests.py` succeeds.
- The checked-in RISC-V subset interpreter produced the expected `main` return values for 6 valid samples in normal and `-opt` modes.
- Invalid semantic samples under `test/invalid/` are rejected.
- Manual static inspection of `test/functions.tc` output confirmed:
  - `main` is emitted as a global symbol.
  - non-main functions are emitted as internal `fn_*` labels.
  - the 9th argument is stored in caller stack argument space and loaded by the callee from `0(s0)`.

## Remaining Risk

- No local `riscv64-unknown-elf-gcc`, `riscv64-linux-gnu-gcc`, `riscv32-unknown-elf-gcc`, or `qemu-riscv32` was available, so target assembly was not executed with a real RISC-V toolchain.
- Attempted `winget install --id LLVM.LLVM` and `winget install --id SoftwareFreedomConservancy.QEMU`; both failed during download with `InternetOpenUrl()` errors.
- Semantic checking is now broad enough to reject duplicate globals, invalid main, invalid calls, forward calls, const assignment, invalid const initialization, void value misuse, break/continue outside loops, and missing int returns.

## Local Tooling Status

- Plain `ocamlc` and `dune` are not on PATH.
- `opam` is available.
- `opam exec -- ocamlc -version` reports `5.4.1` locally; code should stay OCaml 5.3-compatible.
- `opam exec -- dune --version` reports `3.23.1` locally; project requests Dune language 3.19 for the evaluator.
