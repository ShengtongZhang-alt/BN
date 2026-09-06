# Verification record

Date: 2026-09-05 (UTC-7)

Toolchain:

- Lean `v4.33.0-rc1`
- Mathlib `79d0395a1825a6264ad5d269e35e60537518955e` (tag `v4.33.0-rc1`)

Commands run from the repository root on a clean tree (`rm -rf .lake/build`):

```bash
lake build                                  # BN, Challenge, Solution
ruby scripts/check-submission-files.rb
scripts/check-metadata-schema.sh
ruby scripts/check-axioms.rb
# Comparator, run locally with the pinned comparator / lean4export / nanoda
# revisions of scripts/verify-comparator.sh and Comparator's own
# scripts/fake-landrun.sh in place of Landrun (macOS has no Landlock):
COMPARATOR_LANDRUN=.../fake-landrun.sh COMPARATOR_LEAN4EXPORT=.../lean4export \
  COMPARATOR_NANODA=.../nanoda_bin lake env .../comparator comparator.json
```

Results:

- The library build succeeded: all 31 `BN.*` modules, `Challenge` and
  `Solution` compile from scratch with no errors. The only `sorry` warnings are
  the five deliberate holes in `Challenge.lean`.
- `#print axioms` for each of `BN.lambda1_sq_add_lambda2_sq_le`, `BN.weighted`,
  `BN.matrix_theorem`, `BN.gram_le`, `BN.chiVec3_eq_cliqueNum` reports exactly
  `propext`, `Classical.choice`, `Quot.sound` (`scripts/check-axioms.rb`:
  "axiom reports agree with comparator.json and formalization.yaml").
- `scripts/check-submission-files.rb`: "submission files OK".
- `scripts/check-metadata-schema.sh`: formalization.yaml validates against the
  pinned upstream v0.4 schema.
- Comparator (commit `68a0641`, lean4export `af5aa64` at `v4.33.0-rc1`, nanoda
  `68d5ca9`): the five statements in `Solution` match `Challenge`, "Nanoda
  kernel accepts the solution", "Lean default kernel accepts the solution",
  "Your solution is okay!".
- The `pp.all` printouts of the five theorem types and of the fifteen
  definitions they use are byte-identical in the `Challenge` and `Solution`
  environments.

No `sorry`, `admit`, `native_decide`, or new `axiom` is present in `BN/`.
