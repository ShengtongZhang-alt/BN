/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# The Bollobás--Nikiforov inequality: advertised statements

This is the small, self-contained statement surface for the
[Palomar](https://palomar-registry.org/) submission.  It imports only Mathlib, restates the
definitions appearing in the statements (identical, binder for binder, to the ones in the
`BN/` development), and states the five headline results of `docs/sol.tex` with deliberate
`sorry` holes.  The proved versions, with exactly the same names and types, are supplied by
`Solution.lean`, which imports the full development.

## The problem

Let `G` be a finite simple graph with adjacency eigenvalues `λ₁(G) ≥ λ₂(G) ≥ ⋯`, `|E(G)|`
edges and clique number `ω(G)`.  Bollobás and Nikiforov (2007) conjectured that every
noncomplete graph on at least two vertices satisfies
`λ₁(G)² + λ₂(G)² ≤ 2 (1 - 1/ω(G)) |E(G)|`.

## The results

* **`lambda1_sq_add_lambda2_sq_le`** (Conjecture `conj:BN`): the Bollobás--Nikiforov
  inequality for every finite noncomplete simple graph on at least two vertices.
* **`weighted`** (Theorem `thm:weighted`): for a symmetric entrywise nonnegative matrix `B` with
  zero diagonal supported on the edges of `G`, the sum `F(B)` of the squares of the two largest
  positive eigenvalues of `B` is at most `(1 - 1/ω(G)) ‖B‖_F²`.
* **`matrix_theorem`** (Theorem `thm:matrix`): if `z₁, …, zₙ ∈ ℝ²` lie in a closed half-plane
  through the origin, then `M(X)` is completely positive, where `X` is their Gram matrix and
  `M(X) = X ∘ X + ∑_{i<j, X_{ij}<0} X_{ij}² (eᵢ - eⱼ)(eᵢ - eⱼ)ᵀ`.
* **`gram_le`** (Theorem `thm:gram`): for every real positive semidefinite `X` of rank at most
  two, `∑_{i,j} (A_G)_{ij} (X_{ij})₊² ≤ (1 - 1/ω(G)) ‖X‖_F²`.
* **`chiVec3_eq_cliqueNum`** (Corollary `cor:parameter`): the rank-two conic parameter
  `χ''_{vec,3}(G)` of Coutinho, Spier and Zhang equals `ω(G)`.

## Conventions

* Graphs are `SimpleGraph V` on a `Fintype V`; the complete graph is `⊤`, so "noncomplete" is
  `G ≠ ⊤`, and "at least two vertices" is `[Nontrivial V]`.
* Adjacency eigenvalues are those of the real adjacency matrix `G.adjMatrix ℝ`, ordered
  nonincreasingly by Mathlib's `Matrix.IsHermitian.eigenvalues₀` and counted with algebraic
  multiplicity; `lambda1 G` and `lambda2 G` are the values at indices `0` and `1`.
* `G.edgeFinset.card` counts each undirected edge once, so `2 * … * G.edgeFinset.card` is the
  paper's `2 (1 - 1/ω) |E(G)|`; `G.cliqueNum` is `ω(G)`.
* `inner B C = (Bᵀ * C).trace` is the real Frobenius pairing, so `inner B B = ‖B‖_F²`;
  `posPart X` is the entrywise positive part; `⊙` is the Hadamard (entrywise) product.
* A real matrix is `IsCompletelyPositive` if it is a finite sum of outer products
  `vecMulVec p p` of entrywise nonnegative vectors `p`.
* The `[DecidableEq _]`, `[DecidableRel G.Adj]` and `[LinearOrder n]` hypotheses are
  typeclass artifacts (adjacency matrix, edge finset, and the index order `i < j` in `M`);
  `[Nontrivial n]` in `weighted` is likewise an artifact of the ambient section (for a
  one-vertex graph the only admissible `B` is `0`).
-/

-- With the whole of Mathlib imported, `Fintype (Fin 2)` (needed by `w ⬝ᵥ z i` in `gram` and
-- `matrix_theorem`) would be found through an instance from the simplex category rather than
-- through `Fin.fintype`, as it is in the development (whose imports are narrower).  Comparator
-- requires the statements to be syntactically identical, so that instance is switched off here.
attribute [-instance] SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat

namespace BN

noncomputable section

open Matrix
open scoped Matrix

/-! ### Adjacency eigenvalues (`BN/Definition.lean`) -/

section Definition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency eigenvalues of a finite simple graph, indexed with algebraic
multiplicity by its vertex type. (Restated so that the auxiliary proof term shared with
`adjacencyEigenvalues₀` is generated under the same name as in the development.) -/
noncomputable def adjacencyEigenvalues
    (G : SimpleGraph V) [DecidableRel G.Adj] : V → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues

/-- The adjacency eigenvalues in nonincreasing order. The value at `i` is the
paper's `λ_{i+1}(G)`. -/
noncomputable def adjacencyEigenvalues₀
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fin (Fintype.card V) → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀

/-- The largest adjacency eigenvalue `λ₁(G)`. -/
noncomputable def lambda1
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩

/-- The second-largest adjacency eigenvalue `λ₂(G)`. -/
noncomputable def lambda2
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩

end Definition

/-! ### The functional `F` (`BN/Basic/Spectrum.lean`) -/

section Spectrum

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

/-- The sum of squares of the two largest positive eigenvalues of a Hermitian
matrix, with missing terms replaced by zero. -/
noncomputable def F (hA : A.IsHermitian) : ℝ :=
  if h0 : 0 < Fintype.card n then
    let t0 := (max (hA.eigenvalues₀ ⟨0, h0⟩) 0) ^ 2
    if h1 : 1 < Fintype.card n then
      t0 + (max (hA.eigenvalues₀ ⟨1, h1⟩) 0) ^ 2
    else t0
  else 0

end Spectrum

/-! ### The Turán factor (`BN/Basic/Graph.lean`) -/

section Graph

variable {V : Type*}

/-- The coefficient `1 - 1 / ω(G)` appearing in Turán-type bounds. -/
noncomputable def turanFactor (G : SimpleGraph V) : ℝ :=
  1 - 1 / (G.cliqueNum : ℝ)

end Graph

/-! ### Frobenius pairing, positive part, basis vectors (`BN/Basic/Inner.lean`) -/

section Inner

variable {m n : Type*}

/-- The real Frobenius pairing `⟨B, C⟩ = tr(Bᵀ C)`. -/
def inner [Fintype n] (B C : Matrix n n ℝ) : ℝ :=
  (Bᵀ * C).trace

/-- The entrywise positive part `(posPart X) i j = max (X i j) 0`. -/
def posPart (X : Matrix m n ℝ) : Matrix m n ℝ :=
  of fun i j => max (X i j) 0

/-- The standard basis vector `e k` in `n → ℝ`. -/
def e [DecidableEq n] (k : n) : n → ℝ :=
  Pi.single k 1

end Inner

/-! ### Complete positivity (`BN/CP/Basic.lean`) -/

section CP

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real matrix is completely positive if it is a sum of outer products of
entrywise nonnegative vectors. -/
def IsCompletelyPositive (C : Matrix n n ℝ) : Prop :=
  ∃ (q : ℕ) (p : Fin q → n → ℝ),
    (∀ a i, 0 ≤ p a i) ∧ C = ∑ a, vecMulVec (p a) (p a)

end CP

/-! ### The map `M` (`BN/M/Basic.lean`) and planar Gram matrices (`BN/M/HalfPlane.lean`) -/

section M

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- The correction weight on the pair `{i,j}`: `(X i j)²` when `i < j` and the
entry is negative, and `0` otherwise. -/
def laplacianCoeff (X : Matrix n n ℝ) (i j : n) : ℝ :=
  if i < j ∧ X i j < 0 then (X i j) ^ 2 else 0

/-- The map of `docs/sol.tex` (eq:matrix). -/
def M (X : Matrix n n ℝ) : Matrix n n ℝ :=
  X ⊙ X + ∑ i, ∑ j, laplacianCoeff X i j • vecMulVec (e i - e j) (e i - e j)

/-- The Gram matrix of a family of planar vectors. -/
def gram (z : n → Fin 2 → ℝ) : Matrix n n ℝ :=
  of fun i j => z i ⬝ᵥ z j

end M

/-! ### The conic parameter `χ''_{vec,3}` (`BN/Spectral/Conic.lean`) -/

section Conic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Off-edge indicator `I + A_{Gᶜ} = J - A_G`. Equals `1` on the diagonal and
on non-edges of `G`, and `0` on edges. -/
def offEdgeMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  1 + Gᶜ.adjMatrix ℝ

/-- Feasible matrices for `χ''_{vec,3}`. -/
def ChiVec3Feasible (G : SimpleGraph V) [DecidableRel G.Adj] (X : Matrix V V ℝ) : Prop :=
  X.PosSemidef ∧ X.rank ≤ 2 ∧
    inner (offEdgeMatrix G) (X ⊙ X) = 1 ∧
    ∀ i j, G.Adj i j → 0 ≤ X i j

/-- The parameter `χ''_{vec,3}(G)`. -/
noncomputable def chiVec3 (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup ((fun X : Matrix V V ℝ => inner X X) '' {X | ChiVec3Feasible G X})

end Conic

/-! ### The five headline statements -/

-- The binders of `weighted` and `gram_le` reproduce the ambient sections of the development
-- verbatim (Comparator requires identical statements); two instance arguments are unused.
set_option linter.unusedDecidableInType false

section ConjBN

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Conjecture `conj:BN` (Bollobás--Nikiforov).**
Every finite noncomplete simple undirected graph on at least two vertices
satisfies `λ₁(G)² + λ₂(G)² ≤ 2 (1 - 1/ω(G)) |E(G)|`. -/
theorem lambda1_sq_add_lambda2_sq_le
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G ≠ ⊤) :
    lambda1 G ^ 2 + lambda2 G ^ 2 ≤
      2 * (1 - 1 / (G.cliqueNum : ℝ)) * (G.edgeFinset.card : ℝ) := by
  sorry

end ConjBN

section Weighted

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B : Matrix n n ℝ}
variable [Nontrivial n]

/-- **Theorem `thm:weighted`.**  If `B` is symmetric, entrywise nonnegative, has zero
diagonal and vanishes off the edges of `G`, then `F(B) ≤ (1 - 1/ω(G)) ‖B‖_F²`. -/
theorem weighted {G : SimpleGraph n} [DecidableRel G.Adj]
    (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j)
    (hdiag : ∀ i, B i i = 0)
    (hsupp : ∀ i j, ¬ G.Adj i j → B i j = 0) :
    F hB ≤ turanFactor G * inner B B := by
  sorry

end Weighted

/-- **Theorem `thm:matrix`.**  If the planar vectors `z i ∈ ℝ²` all lie in the closed
half-plane `{v | w ⬝ᵥ v ≥ 0}` for some `w ≠ 0`, then `M` of their Gram matrix is completely
positive. -/
theorem matrix_theorem {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (z : n → Fin 2 → ℝ) {w : Fin 2 → ℝ} (hw : w ≠ 0)
    (hwz : ∀ i, 0 ≤ w ⬝ᵥ z i) :
    IsCompletelyPositive (M (gram z)) := by
  sorry

section Gram

variable {V : Type*}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Theorem `thm:gram`.**  For every real positive semidefinite `X` of rank at most two,
`∑ᵢⱼ (A_G)ᵢⱼ (Xᵢⱼ)₊² ≤ (1 - 1/ω(G)) ‖X‖_F²` (each edge counted twice on the left). -/
theorem gram_le [Fintype V] [DecidableEq V] {X : Matrix V V ℝ}
    (hX : X.PosSemidef) (hr : X.rank ≤ 2) :
    ∑ i, ∑ j, G.adjMatrix ℝ i j * (posPart X i j) ^ 2 ≤
      turanFactor G * inner X X := by
  sorry

end Gram

section Parameter

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Corollary `cor:parameter`.**  The rank-two conic parameter `χ''_{vec,3}(G)` of
Coutinho, Spier and Zhang equals the clique number. -/
theorem chiVec3_eq_cliqueNum [Nonempty V] :
    chiVec3 G = G.cliqueNum := by
  sorry

end Parameter

end

end BN
