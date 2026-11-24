# VENDORED: the library `CookLevin`

`vendor/CookLevin/` is a copy of **cook-levin-lean** by Dominic Breuker
(<https://github.com/DominicBreuker/cook-levin-lean>), a Lean 4 development of the Cook–Levin
theorem: `theorem CookLevin.cook_levin : CookLevin.NPcomplete SATStr` in `CookLevin/Theorem.lean`.

| | |
| --- | --- |
| Upstream commit | `fb3e61c989d021f8a641a8d99155b953c62a1b74` (2026-10-02, "Merge pull request #190 … inNP: certificate bound is an explicit polynomial") |
| Upstream pins | Lean `v4.30.0-rc2`, Mathlib `b9cac3012115e37d51d1b3c9156a94db19d1d064` |
| Pins here | Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (this tree's `lean-toolchain` and `lake-manifest.json`) |
| Licence | MIT, upstream's `LICENSE`, kept at `vendor/CookLevin/LICENSE`. It covers the files under `vendor/CookLevin/` only, nothing else of this tree. |

## Layout

- `vendor/CookLevin/CookLevin.lean` and `vendor/CookLevin/CookLevin/**.lean` are upstream's
  `CookLevin.lean` and `CookLevin/**.lean` (105 modules), at the same paths below `vendor/CookLevin/`,
  so every module keeps its upstream name (`CookLevin.Theorem`, `CookLevin.Basic.Definitions`, …).
  Every declaration keeps its upstream name too, including the many upstream declares outside the
  `CookLevin` namespace (`FlatTM`, `SAT`, `cnf`, `var`, `inOPoly`, …).
- `lakefile.toml` declares it as the library `CookLevin` with `srcDir = "vendor/CookLevin"` and
  upstream's options (`autoImplicit` and `relaxedAutoImplicit` off), and builds it by default.
- Not vendored: upstream's `Verify.lean`, `README.md`, `GUIDE.md`, `lakefile.lean`,
  `lake-manifest.json`, `lean-toolchain`, `.gitignore` and `.github/`. This tree's own Lake files
  replace upstream's; `GUIDE.md` and `README.md` are read at the commit above.

## The two build-time gates

Both run on every `lake build` of the library and fail it when they do not hold:

- **The reading list**: `CookLevin/ReadingList.lean`'s `#assert_statement_surface
  CookLevin.cook_levin => …` (`CookLevin/Meta/StatementSurface.lean`) recomputes the definitions the
  statement of `cook_levin` depends on and requires them to be exactly its list. On Lean v4.36.0:
  "statement surface of 'CookLevin.cook_levin': 68 repository definitions (91 including generated
  companions) — list verified exact". Those 68 names are `AUDIT.md` section 5 and the end of the
  campaign's reading list.
- **The library axiom check**: the root module `CookLevin.lean` imports every module and ends with
  `#assert_library_axiom_clean CookLevin` (`CookLevin/Meta/AxiomGate.lean`): every declaration of
  every module under `CookLevin` depends on no axiom beyond `propext`, `Classical.choice` and
  `Quot.sound`, so none uses `sorry`. On Lean v4.36.0: "axiom gate: 11099 declarations in 104
  modules under 'CookLevin' are clean (no `sorry`, no bespoke axiom)". `CookLevin/Theorem.lean`'s
  `#assert_axioms_clean` on the headline theorems passes too, and `#print axioms
  CookLevin.cook_levin` (upstream's `Verify.lean`) prints `[propext, Classical.choice, Quot.sound]`.

## Files changed for Lean v4.36.0 and Mathlib fc4f59e

Twelve of the 105 modules; every other file is byte for byte upstream's. No statement and no
definition's body changed: the changes are proof steps, two counters' types and attributes that
only widen what Lean's elaborator unfolds when it checks a term's type. The statement surface above
is the same 68 names upstream lists.

Most of the breaks come from Lean's transparency work in v4.31.0 to v4.33.0: `simpa … using e` now
closes its goal at reducible transparency (`using!` keeps the old, default-transparency close), a
metavariable's type is compared with its value's at implicit transparency
(`backward.isDefEq.respectTransparency.types`, on by default since v4.33.0), and `rw` finds no
instance whose type only checks after unfolding an ordinary definition. The release notes'
recommended fix for the second is `@[implicit_reducible]` on the definitions involved; for the
third it is not to unfold the definition inside a decidability instance's proposition.

- `CookLevin/Meta/AxiomGate.lean`: `let mut nModules : Nat := 0` and `let mut nDecls : Nat := 0`
  in `elabAssertLibraryClean`. Unannotated, Lean v4.36.0 elaborates both counters as `MessageData`
  (their use in the closing `m!` message) and the gate itself does not compile.
- `CookLevin/Basic/Definitions.lean`: `@[implicit_reducible]` on `ofFlatType` and
  `list_ofFlatType`.
- `CookLevin/Problems/FlatCC.lean`: `@[implicit_reducible]` on `CCCard_ofFlatType`,
  `isValidFlatCards`, `isValidFlatFinal`, `isValidFlatInitial`, so `simp` again rewrites with
  `flatten_unflattenList`, `flatten_unflattenCards` and `flatten_unflattenFinal` under the proofs
  the unflattening functions carry; `flattenCC` added to the `simpa` set in `flattenCC_wellformed`.
- `CookLevin/Problems/FlatTCC.lean`: `@[implicit_reducible]` on `TCCCardP_ofFlatType`,
  `TCCCard_ofFlatType`, `isValidFlatCards`, `isValidFlatFinal`, `isValidFlatInitial`, for the same
  reason. With these, `CookLevin/Reductions/FlatTCC_to_FlatCC.lean` builds unchanged.
- `CookLevin/Reductions/FlatCC_to_BinaryCC.lean`: `CC_to_BinaryCC` added to the `simpa` set in
  `BinaryCC_to_CC_lang`, so `(CC_to_BinaryCC C).steps` is `C.steps` before the reducible close.
- `CookLevin/Lang/Compile/RunEqBit.lean`: `simpa … using!` in four places
  (`Compile.navTestRewindM_run_content`, `Compile.navTestRewindM_run_delim`, the `a = 0, b = 0` case
  of `Compile.bitCompareM_run`, `Compile.compareBody_done_run`), where the goal and the hypothesis
  agree only after unfolding a machine's definition.
- `CookLevin/Lang/FormatCheck.lean`: `scanRegs_seg`'s base case `simpa [Compile.encodeRegs_nil]`:
  `simp` no longer reduces `(Compile.encodeRegs []).length` to `0` on its own.
- `CookLevin/Lang/Compile/OpSound.lean`: `List.length_nil` added to one `simp only` in
  `Compile.opConcat_run`'s first stage, for the same reason.
- `CookLevin/Lang/Compile/RunClear.lean`: two `simp only [] at hc` removed in
  `Compile.opAppendBit_physical_residue`: `congrArg` already
  gives the beta-reduced hypothesis, and a `simp` that changes nothing is now an error.
- `CookLevin/Simulation/Zipper.lean`: in `zip_write` and `zip_move`'s left move, the
  `if (zip h right).exc = 0` is decided before `zip` is unfolded (`rw [if_pos (show (zip h right).exc
  = 0 …)]`, then `simp only [zip, …]`). Unfolding `zip` first rewrote the condition but left its
  `Decidable` instance on `(zip h right).exc = 0`, a term `rw` no longer matches.
- `CookLevin/Tableau/CookTableau.lean`: `@[implicit_reducible]` on `confRow`, so
  `confRow_getElem` and `confRow_getElem_last` index the unfolded row with the bound stated for
  `confRow`.
- `CookLevin/Reductions/BinaryCC_to_FSAT_free.lean`: in `buildFSAT_cost_le`'s two branches,
  `rw [buildFSATBound]; delta buildFSATK; rw [← hKs, …]` instead of `rw [buildFSATBound,
  buildFSATK, ← hKs, …]`. Generating the equation lemma `buildFSATK.eq_1` that `rw [buildFSATK]`
  asks for now evaluates the `Cmd.flatK` numerals and exceeds the recursion limit; `delta` needs no
  equation lemma.

Lean v4.36.0 reports deprecation and linter warnings on the vendored sources (`if_pos` and `if_neg`
now `ite_eq_left` and `ite_eq_right`, unused `simp` arguments, unused variables); they are left as
upstream wrote them.

## Updating

To move to a newer upstream commit: copy its `CookLevin.lean`, `CookLevin/` and `LICENSE` over
`vendor/CookLevin/`, re-apply the changes above that still apply, build, and update the commit and
the list of changed files here. Where the statement surface changes, `#assert_statement_surface`
fails the build: then `AUDIT.md` section 5 and the campaign's reading list change with it, and
the change is read like any other change to the reading list.
