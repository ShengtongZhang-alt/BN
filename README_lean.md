## Lean statements

**Status: complete.** All five headline results of [`docs/sol.tex`](docs/sol.tex)
are proved in full: they build without `sorry`, and `#print axioms` reports only
`propext`, `Classical.choice` and `Quot.sound` for each of them. The
statement-level plan is [`docs/formalization_dag.md`](docs/formalization_dag.md)
(one lemma or definition per node); node-by-node status is tracked in
[`docs/PROGRESS.md`](docs/PROGRESS.md).

The spectral conventions are in [`BN/Definition.lean`](BN/Definition.lean):

```lean
/-- The adjacency eigenvalues in nonincreasing order (Mathlib's antitone
`eigenvalues₀` of the real adjacency matrix); index `i` is the paper's `λ_{i+1}`. -/
noncomputable def adjacencyEigenvalues₀ (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (Fintype.card V) → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀

noncomputable def lambda1 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩

noncomputable def lambda2 (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩
```

The target theorems, all in namespace `BN`, are:

```lean
-- Conjecture 1.1 (conj:BN), BN/Main.lean
theorem lambda1_sq_add_lambda2_sq_le (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G ≠ ⊤) :
    lambda1 G ^ 2 + lambda2 G ^ 2 ≤
      2 * (1 - 1 / (G.cliqueNum : ℝ)) * (G.edgeFinset.card : ℝ)

-- Theorem 1.2 (thm:weighted), BN/Spectral/Weighted.lean
-- `F hB` is the sum of the squares of the two largest positive eigenvalues of `B`,
-- `turanFactor G = 1 - 1 / ω(G)`, and `inner B C = (Bᵀ * C).trace`.
theorem weighted {G : SimpleGraph n} [DecidableRel G.Adj]
    (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j)
    (hdiag : ∀ i, B i i = 0)
    (hsupp : ∀ i j, ¬ G.Adj i j → B i j = 0) :
    F hB ≤ turanFactor G * inner B B

-- Theorem 1.3 (thm:matrix), BN/M/Main.lean
-- `gram z` is the Gram matrix of `z : n → Fin 2 → ℝ`; `M X = X ⊙ X + ∑_{i<j, X i j<0} …`.
theorem matrix_theorem {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (z : n → Fin 2 → ℝ) {w : Fin 2 → ℝ} (hw : w ≠ 0)
    (hwz : ∀ i, 0 ≤ w ⬝ᵥ z i) :
    IsCompletelyPositive (M (gram z))

-- Theorem 1.4 (thm:gram), BN/Spectral/Gram.lean
theorem gram_le [Fintype V] [DecidableEq V] {X : Matrix V V ℝ}
    (hX : X.PosSemidef) (hr : X.rank ≤ 2) :
    ∑ i, ∑ j, G.adjMatrix ℝ i j * (posPart X i j) ^ 2 ≤
      turanFactor G * inner X X

-- Corollary 5.3 (cor:parameter), BN/Spectral/Conic.lean
theorem chiVec3_eq_cliqueNum [Nonempty V] :
    chiVec3 G = G.cliqueNum
```

## Proof architecture

Following `docs/sol.tex` and the DAG, the development has four parts.

1. **Complete positivity and total nonnegativity** (`BN/CP/`, `BN/MS/`,
   `BN/TN/`). The completely positive cone, the pair lemma (a rank-one update
   that decreases an off-diagonal entry) and its weighted-Laplacian corollary,
   closedness of the cone, the Motzkin–Straus inequality in completely
   positive form, and total nonnegativity of the truncated-square and convex
   kernels via truncated and convex Cauchy–Binet identities.
2. **Three-column factorization** (`BN/Kernel/`). An explicit nonnegative
   factorization of a kernel matrix built from two rectangular totally
   nonnegative matrices, with the sign calculations.
3. **Elimination and Schur complement** (`BN/M/`). The map `M`, the
   configuration of planar vectors, the ordered elimination producing
   nonnegative columns, the Schur complement identified as a weighted
   Laplacian plus a matrix with the three-column factorization, the `γ = 0`
   degenerate case, and the half-plane argument assembling `thm:matrix`.
4. **Spectral deduction** (`BN/Spectral/`). Perron eigenvectors of symmetric
   nonnegative matrices, Cauchy interlacing, the weighted inequality
   `thm:weighted`, the variational lemma removing the half-plane restriction
   (`thm:gram`), and the conic parameter (`cor:parameter`). `BN/Main.lean`
   derives the conjecture from `thm:weighted`.

## File guide

| File / directory | Contents |
| --- | --- |
| [`BN/Definition.lean`](BN/Definition.lean) | Ordered and unordered adjacency eigenvalues, `lambda1`, `lambda2`. |
| [`BN/Main.lean`](BN/Main.lean) | The Bollobás–Nikiforov inequality (`conj:BN`). |
| [`BN/Basic/`](BN/Basic) | Frobenius pairing, positive part, `F`, `turanFactor`, clique-number facts. |
| [`BN/CP/`](BN/CP), [`BN/MS/`](BN/MS), [`BN/TN/`](BN/TN) | Completely positive cone, Motzkin–Straus, total nonnegativity. |
| [`BN/Kernel/`](BN/Kernel) | The three-column nonnegative factorization. |
| [`BN/M/`](BN/M) | `M`, configurations, elimination, Schur complement, `thm:matrix`. |
| [`BN/Spectral/`](BN/Spectral) | Perron, interlacing, `thm:weighted`, `thm:gram`, `cor:parameter`. |
| [`docs/sol.tex`](docs/sol.tex) | The note being formalized. |
| [`docs/formalization_dag.md`](docs/formalization_dag.md) | Statement-level DAG, one node per lemma. |
| [`docs/PROGRESS.md`](docs/PROGRESS.md) | Node-by-node status. |
| [`FORMALIZATION.md`](FORMALIZATION.md) | Correspondence between the note and the Lean statements. |
| [`VERIFICATION.md`](VERIFICATION.md) | Reproducible build and check record. |

## Build

```sh
lake exe cache get  # download the precompiled Mathlib cache
lake build
```

The repository pins the Lean toolchain to `leanprover/lean4:v4.33.0-rc1` and
Mathlib to `v4.33.0-rc1`. `lake build` builds the library `BN` together with
the `Challenge` and `Solution` modules below.

## Palomar submission surface

The repository follows the layout of the
[Palomar registry](https://palomar-registry.org/) starter template so that the
headline statements can be checked independently of the proof development:

| File | Role |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | Mathlib-only statement module: restates the definitions used in the statements (`adjacencyEigenvalues₀`, `lambda1`, `lambda2`, `F`, `turanFactor`, `inner`, `posPart`, `e`, `IsCompletelyPositive`, `laplacianCoeff`, `M`, `gram`, `offEdgeMatrix`, `ChiVec3Feasible`, `chiVec3`) and the five theorems with `sorry`. This is the surface a reader should audit. |
| [`Solution.lean`](Solution.lean) | Imports the development, which proves the same declarations. |
| [`comparator.json`](comparator.json) | Names the five compared theorems and the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`). |
| [`formalization.yaml`](formalization.yaml) | Structured metadata: result description, sources, authorship, automation, review status, scope, and fidelity. |
| [`scripts/verify-comparator.sh`](scripts/verify-comparator.sh) | Runs the pinned [Comparator](https://github.com/leanprover/comparator), lean4export (`v4.33.0-rc1`), NanoDa and Landrun to check `Solution` against `Challenge` (Linux; used by the `Palomar checks` workflow). |
| [`scripts/check-submission-files.rb`](scripts/check-submission-files.rb) | Checks the files above against Palomar's mechanical requirements, including that `status.axioms` / `status.main_results` in `formalization.yaml` agree with `comparator.json`. |
| [`scripts/check-metadata-schema.sh`](scripts/check-metadata-schema.sh) | Validates `formalization.yaml` against the pinned upstream v0.4 JSON schema with `check-jsonschema`. |
| [`scripts/check-axioms.rb`](scripts/check-axioms.rb) | Runs `#print axioms` on the compared theorems and requires the result to match `permitted_axioms` and the axiom lists in `formalization.yaml` (called at the end of `verify-comparator.sh`). |

Before submitting a commit, run the three metadata checks locally (the first two
need only Ruby and `pip install check-jsonschema`; the third builds the project):

```
ruby scripts/check-submission-files.rb
scripts/check-metadata-schema.sh
ruby scripts/check-axioms.rb
```

Submissions are made through [https://submit.palomar-registry.org/](https://submit.palomar-registry.org/)
with the full 40-character SHA of a pushed commit.
