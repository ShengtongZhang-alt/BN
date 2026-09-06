# Formalization notes

## Target statements

The five headline results of [`docs/sol.tex`](docs/sol.tex) are declared in the
`BN/` development and are fully proved: the axiom report of each of them
(`#print axioms`) contains only `propext`, `Classical.choice` and `Quot.sound`.

| Source | Lean declaration | Module |
| --- | --- | --- |
| Conjecture 1.1 (`conj:BN`) | `BN.lambda1_sq_add_lambda2_sq_le` | `BN/Main.lean` |
| Theorem 1.2 (`thm:weighted`) | `BN.weighted` | `BN/Spectral/Weighted.lean` |
| Theorem 1.3 (`thm:matrix`) | `BN.matrix_theorem` | `BN/M/Main.lean` |
| Theorem 1.4 (`thm:gram`) | `BN.gram_le` | `BN/Spectral/Gram.lean` |
| Corollary 5.3 (`cor:parameter`) | `BN.chiVec3_eq_cliqueNum` | `BN/Spectral/Conic.lean` |

The same five statements, together with every definition they use, are
restated verbatim in the Mathlib-only module `Challenge.lean` for the Palomar
registry; `comparator.json` lists them, and Comparator checks that
`Solution.lean` (which imports the development) proves exactly those statements
from the standard axioms.

```lean
theorem BN.lambda1_sq_add_lambda2_sq_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G ≠ ⊤) :
    lambda1 G ^ 2 + lambda2 G ^ 2 ≤
      2 * (1 - 1 / (G.cliqueNum : ℝ)) * (G.edgeFinset.card : ℝ)
```

## Correspondence with the paper

- **Finite, simple, undirected graph.** `[Fintype V]` makes the vertex type
  finite. `SimpleGraph V` is Mathlib's loopless symmetric graph structure.
- **At least two vertices.** `[Nontrivial V]` is equivalent to
  `1 < Fintype.card V`, matching the paper's `n ≥ 2`.
- **Noncomplete.** `G ≠ ⊤`, where `⊤` is Mathlib's complete graph
  (`completeGraph V = ⊤`, `ne_top_iff_exists_not_adj`).
- **Ordered spectrum.** `adjacencyEigenvalues₀` is
  `Matrix.IsHermitian.eigenvalues₀` of the real adjacency matrix, which is
  antitone on `Fin n`. Thus `lambda1 G` is `λ₁(G)` and `lambda2 G` is
  `λ₂(G)`, counted with algebraic multiplicity.
- **Clique number and edges.** `ω(G)` is `SimpleGraph.cliqueNum`; `|E(G)|` is
  `G.edgeFinset.card`, which stores each undirected edge once, so the factor
  `2` in the inequality is the paper's coefficient.
- **The functional `F`.** `BN.F hA` is `(max λ₁ 0)² + (max λ₂ 0)²` computed
  from `eigenvalues₀`, with the second term omitted when `n = 1` and `F = 0`
  when `n = 0`; this is the paper's "sum of the squares of the two largest
  positive eigenvalues, missing terms replaced by zero".
- **Frobenius pairing.** `BN.inner B C = (Bᵀ * C).trace`, so
  `inner B B = ‖B‖_F²`. `BN.turanFactor G = 1 - 1 / ω(G)`.
- **Support of `B`.** `hsupp : ∀ i j, ¬ G.Adj i j → B i j = 0` is
  "`B_{ij} = 0` whenever `{i,j} ∉ E(G)`"; together with `hdiag` it covers
  the diagonal. `weighted` carries a `[Nontrivial n]` hypothesis inherited
  from its section; for a one-vertex graph the only admissible `B` is `0`.
- **Completely positive.** `IsCompletelyPositive C` is
  `∃ q (p : Fin q → n → ℝ), (∀ a i, 0 ≤ p a i) ∧ C = ∑ a, vecMulVec (p a) (p a)`.
- **The map `M`.** `M X = X ⊙ X + ∑ i j, laplacianCoeff X i j • vecMulVec (e i - e j) (e i - e j)`
  with `laplacianCoeff X i j = if i < j ∧ X i j < 0 then X i j ^ 2 else 0`;
  the `[LinearOrder n]` hypothesis fixes the meaning of `i < j`, as the
  paper's indexing `1, …, n` does. `gram z` is the Gram matrix
  `(z i ⬝ᵥ z j)` of `z : n → Fin 2 → ℝ`, and the half-plane hypothesis is
  `w ≠ 0` with `0 ≤ w ⬝ᵥ z i` for all `i`.
- **Rank-two Gram inequality.** `posPart X i j = max (X i j) 0`; the sum in
  `gram_le` runs over all ordered pairs, counting each edge twice, exactly as
  the paper's display.
- **The conic parameter.** `ChiVec3Feasible G X` is
  `X.PosSemidef ∧ X.rank ≤ 2 ∧ inner (offEdgeMatrix G) (X ⊙ X) = 1 ∧ ∀ i j, G.Adj i j → 0 ≤ X i j`
  with `offEdgeMatrix G = 1 + Gᶜ.adjMatrix ℝ = I + A_{Ḡ}`, and
  `chiVec3 G = sSup (inner X X '' {X | ChiVec3Feasible G X})`; the objective
  `⟨J, X∘²⟩ = ‖X‖_F²` is `inner X X`. The paper's maximum is attained; the
  Lean statement is about the supremum, which the theorem shows equals `ω(G)`.
- **Typeclass artifacts.** `[DecidableEq _]` and `[DecidableRel G.Adj]`
  support the adjacency matrix, `edgeFinset`, and eigenvalue indexing.
  Definitions involving spectral decomposition are `noncomputable`.

## Hypotheses that are deliberately absent

- No irreducibility or connectivity assumption in the spectral results: the
  half-plane hypothesis of `thm:matrix` is supplied by a nonnegative Perron
  eigenvector.
- No lower bound on the clique number in `cor:parameter`.
- No restriction on the weights in `thm:weighted` beyond nonnegativity, zero
  diagonal and support on `E(G)`.

## Toolchain

The repository pins Lean to `leanprover/lean4:v4.33.0-rc1` in
`lean-toolchain` and Mathlib to `v4.33.0-rc1` in `lakefile.toml`.
