/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import BN.Main
import BN.M.Main
import BN.Spectral.Gram
import BN.Spectral.Conic

/-!
# Proved solution

This module imports the full proof development.  The five declarations named in
`comparator.json`,

* `BN.lambda1_sq_add_lambda2_sq_le` (`BN/Main.lean`, Conjecture `conj:BN`),
* `BN.weighted` (`BN/Spectral/Weighted.lean`, Theorem `thm:weighted`),
* `BN.matrix_theorem` (`BN/M/Main.lean`, Theorem `thm:matrix`),
* `BN.gram_le` (`BN/Spectral/Gram.lean`, Theorem `thm:gram`),
* `BN.chiVec3_eq_cliqueNum` (`BN/Spectral/Conic.lean`, Corollary `cor:parameter`),

are proved there with the same names and statements as in `Challenge.lean` and are therefore
present in this module's environment.  Comparator checks that each one has exactly the same
statement as its counterpart in `Challenge.lean`, that every definition appearing in those
statements (`adjacencyEigenvalues₀`, `lambda1`, `lambda2`, `F`, `turanFactor`, `inner`,
`posPart`, `e`, `IsCompletelyPositive`, `laplacianCoeff`, `M`, `gram`, `offEdgeMatrix`,
`ChiVec3Feasible`, `chiVec3`) is identical in both modules, and that the proofs use only the
axioms `propext`, `Classical.choice`, and `Quot.sound`.

The `example`s below are a readable local witness of the same facts: they type-check only if
the proved theorems have the advertised types.
-/

namespace BN

open Matrix
open scoped Matrix

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] (hG : G ≠ ⊤) :
    lambda1 G ^ 2 + lambda2 G ^ 2 ≤
      2 * (1 - 1 / (G.cliqueNum : ℝ)) * (G.edgeFinset.card : ℝ) :=
  lambda1_sq_add_lambda2_sq_le G hG

example {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℝ} [Nontrivial n]
    {G : SimpleGraph n} [DecidableRel G.Adj]
    (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j)
    (hdiag : ∀ i, B i i = 0) (hsupp : ∀ i j, ¬ G.Adj i j → B i j = 0) :
    F hB ≤ turanFactor G * inner B B :=
  weighted hB hnn hdiag hsupp

example {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (z : n → Fin 2 → ℝ) {w : Fin 2 → ℝ} (hw : w ≠ 0) (hwz : ∀ i, 0 ≤ w ⬝ᵥ z i) :
    IsCompletelyPositive (M (gram z)) :=
  matrix_theorem z hw hwz

example {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} (hX : X.PosSemidef) (hr : X.rank ≤ 2) :
    ∑ i, ∑ j, G.adjMatrix ℝ i j * (posPart X i j) ^ 2 ≤ turanFactor G * inner X X :=
  gram_le hX hr

example {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    [Nonempty V] : chiVec3 G = G.cliqueNum :=
  chiVec3_eq_cliqueNum

end BN
