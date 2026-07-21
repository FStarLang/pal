# Verifying a single function

`make verify` re-checks **every** generated `.fst`/`.fsti` in `out/`, which is
slow and — while `func_pointer.c` still contains not-yet-verified examples —
stops at the first module that fails. To iterate on one function, verify just
that module.

## Module-name mapping

Every C function becomes its own F\* module named `Func_<name>` (the file
`out/Func_<name>.fst`). For example:

| C function        | Module file                    |
| ----------------- | ------------------------------ |
| `reassign_join`   | `out/Func_reassign_join.fst`   |
| `use_conditional` | `out/Func_use_conditional.fst` |
| `add`             | `out/Func_add.fst`             |

## The easy way: `make verify-one`

```sh
make verify-one MODULE=Func_reassign_join
```

This translates `func_pointer.c`, builds the module's dependencies (in order),
then verifies the target. Replace the module name as needed.

## The manual way

If you want to run F\* directly (e.g. to add extra flags):

1. **Translate** (regenerates `out/` from `func_pointer.c`):

   ```sh
   make translate
   ```

2. **Verify one module** by calling the F\* runner directly on its `.fst`,
   reusing the same flags the Makefile uses:

   ```sh
   ../opt/run-fstar.sh \
     --cache_checked_modules \
     --cache_dir _cache \
     --already_cached 'Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' \
     --include out \
     out/Func_reassign_join.fst
   ```

Success prints:

```
Verified module: Func_reassign_join
All verification conditions discharged successfully
```

## Clean up stale dependencies first

**F\* trusts the `_cache/` blindly.** A `*.fst.checked` file is reused as-is
whenever it looks up to date — even if the real dependency it was built against
has since changed. Two things go stale in practice:

- **Regenerated modules.** After editing the transpiler and re-running
  `make translate`, an `out/Func_foo.fst` may change while a *dependent* module's
  cached `.checked` still reflects the old interface. Verifying the dependent
  then either fails confusingly or (worse) succeeds against the outdated
  interface.
- **The Pulse library.** The axiom file `pulse/Pulse.Lib.C.FuncPtr.fsti` (and the
  rest of `pulse/`) is checked into `pulse/_cache/`. After editing an `.fsti`
  there, or after pulling changes that touch `pulse/` (a fresh checkout, a
  rebase, a `git pull`), the library cache is stale and F\* will either use the
  old axioms or report errors like *"Expected Pulse.Lib.C.MaybeUninit to be
  already checked but could not find it."*

**Before checking `.fst` files, clear the stale caches:**

```sh
# Rebuild the Pulse support library after any change under pulse/ (or a pull):
make -C .. lib          # runs `make -C pulse`; repopulates pulse/_cache/

# Drop this workspace's stale module caches:
rm -f _cache/Func_<name>.fst.checked      # one module
rm -rf _cache .depend                     # everything, the safe default
```

Then re-run `make verify-one MODULE=Func_<name>` (or the manual F\* command).
When in doubt, `rm -rf _cache .depend` and let it rebuild from scratch — it is
slower but always correct.

## Notes

- **Pass exactly one file.** Do not pass both the `.fsti` and `.fst` on the same
  command line — F\* checks the `.fst` and picks up its interface automatically.
  Passing both triggers a spurious error.
- **Dependencies are resolved via `--include out`.** Any dependency not already
  in `_cache/` is checked on the fly and its `*.fst.checked` written to `_cache/`,
  so subsequent runs sharing that dependency are fast (subject to the staleness
  caveat above).
- The flags above are exactly what `make verify` / `make verify-one` pass and
  what the editor uses (see `fstar.fst.config.json`), so a module that passes
  here passes there too.
