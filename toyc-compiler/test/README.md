# Smoke Tests

These ToyC files are small compiler smoke tests. They are intended to be run as:

```sh
dune exec compiler -- < test/basic.tc > /tmp/basic.s
dune exec compiler -- -opt < test/control.tc > /tmp/control.s
```

Expected `main` return values:

- `basic.tc`: `5`
- `control.tc`: `31`
- `copy_branch_merge.tc`: `2`
- `functions.tc`: `85`
- `global_call_global_read.tc`: `2`
- `gvn_temp_redef_loop.tc`: `4`
- `globals_shortcircuit.tc`: `42`
- `infinite_return.tc`: `77`
- `isel_immediates.tc`: `157`
- `licm_global_invariant.tc`: `24`
- `licm_reassociate_add_sub.tc`: `16`
- `licm_reassociate_sub_add.tc`: `20`
- `regalloc_call_live.tc`: `89`
- `regalloc_loop_call_global.tc`: `38`
- `regalloc_many_args.tc`: `100`
- `recursion_void_global.tc`: `120`

Run the full local regression suite with:

```sh
python tools/run_smoke_tests.py
```

The script checks both normal and `-opt` compiler output with the project's RISC-V32 subset interpreter, and also verifies semantic-invalid programs under `test/invalid/` are rejected.
