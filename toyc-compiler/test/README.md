# Smoke Tests

These ToyC files are small compiler smoke tests. They are intended to be run as:

```sh
dune exec compiler -- < test/basic.tc > /tmp/basic.s
dune exec compiler -- -opt < test/control.tc > /tmp/control.s
```

Expected `main` return values:

- `basic.tc`: `5`
- `control.tc`: `31`
- `functions.tc`: `85`
- `globals_shortcircuit.tc`: `42`
- `infinite_return.tc`: `77`
- `recursion_void_global.tc`: `120`

Run the full local regression suite with:

```sh
python tools/run_smoke_tests.py
```

The script checks both normal and `-opt` compiler output with the project's RISC-V32 subset interpreter, and also verifies semantic-invalid programs under `test/invalid/` are rejected.
