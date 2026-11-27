# Development

- `LeanClove/Seq.lean`: finite sequence operations and laws.
- `LeanClove/Map.lean`: hash-map operations, grouping, and tallying.
- `LeanClove/Function.lean`: function combinators.
- `LeanCloveTest.lean`: executable examples checked by `lake test`.

Use the Lean version pinned in `lean-toolchain` and keep the library free of external Lake dependencies.
Use Lean's standard library for existing operations and prove the laws of the public API.
Run `nix develop -c make check` and `nix build` before committing.
