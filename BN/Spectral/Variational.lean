/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import BN.Basic.Spectrum
import BN.Basic.Inner
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Variational comparison for rank-at-most-two PSD matrices

The two-dimensional variational bound on a pair of orthonormal Rayleigh
quotients, the rank-two spectral writing of a PSD matrix, and
`lem:variational` of `docs/sol.tex`.
-/

namespace BN

open Matrix Finset
open scoped InnerProductSpace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B : Matrix n n ℝ}

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Coordinate form of the eigenbasis -/

lemma eigenvectorBasis_dotProduct_self (hB : B.IsHermitian) (i : n) :
    (hB.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hB.eigenvectorBasis i : n → ℝ) = 1 := by
  have hn : ‖hB.eigenvectorBasis i‖ = 1 := hB.eigenvectorBasis.orthonormal.1 i
  have hsq := EuclideanSpace.real_norm_sq_eq (hB.eigenvectorBasis i)
  simp [dotProduct, pow_two] at hsq ⊢
  simpa [hn] using hsq.symm

lemma eigenvectorBasis_dotProduct (hB : B.IsHermitian) {i j : n} (hij : i ≠ j) :
    (hB.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hB.eigenvectorBasis j : n → ℝ) = 0 := by
  have h0 : ⟪hB.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ = 0 :=
    hB.eigenvectorBasis.orthonormal.inner_eq_zero hij
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h0
  simpa [dotProduct_comm] using h0

lemma parseval_eigenvectorBasis (hB : B.IsHermitian) (x : n → ℝ) :
    ∑ k, ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ x) ^ 2 = x ⬝ᵥ x := by
  have h := OrthonormalBasis.sum_sq_inner_right (hB.eigenvectorBasis) (WithLp.toLp 2 x)
  have hinter (k : n) :
      ⟪hB.eigenvectorBasis k, WithLp.toLp 2 x⟫_ℝ =
        (hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  simp only [hinter] at h
  have hnorm : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, pow_two]
  exact h.trans hnorm

lemma vecMulVec_mulVec_real (u v x : n → ℝ) :
    vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

lemma isHermitian_quadratic (hB : B.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ B *ᵥ x =
      ∑ k, hB.eigenvalues k *
        ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ x) ^ 2 := by
  have hx :
      B = ∑ k, hB.eigenvalues k •
        vecMulVec (hB.eigenvectorBasis k : n → ℝ)
          (hB.eigenvectorBasis k : n → ℝ) := by
    simpa [IsHermitian.eigenvectorUnitary_col_eq] using
      isHermitian_eq_sum_smul_vecMulVec hB
  conv_lhs => rw [hx]
  rw [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [smul_mulVec, dotProduct_smul, vecMulVec_mulVec_real, dotProduct_smul]
  rw [dotProduct_comm x]
  ring

lemma eigenvalues_le_lambdaMax [Nonempty n] (hB : B.IsHermitian) (i : n) :
    hB.eigenvalues i ≤ lambdaMax hB := by
  have : hB.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i) ≤
      hB.eigenvalues₀ ⟨0, Fintype.card_pos⟩ :=
    hB.eigenvalues₀_antitone (Fin.zero_le _)
  simpa [IsHermitian.eigenvalues, lambdaMax, eigs₀] using this

lemma rayleigh_le_lambdaMax [Nonempty n] (hB : B.IsHermitian) {u : n → ℝ}
    (hu : u ⬝ᵥ u = 1) :
    u ⬝ᵥ B *ᵥ u ≤ lambdaMax hB := by
  rw [isHermitian_quadratic hB]
  have hle :
      ∑ k, hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 ≤
        ∑ k, lambdaMax hB * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 :=
    Finset.sum_le_sum fun k _ ↦
      mul_le_mul_of_nonneg_right (eigenvalues_le_lambdaMax hB k) (sq_nonneg _)
  refine hle.trans_eq ?_
  rw [← Finset.mul_sum, parseval_eigenvectorBasis, hu, mul_one]

/-! ### CG02: rank-two writing -/

lemma exists_rankTwo_writing [Nontrivial n] {X : Matrix n n ℝ}
    (hX : X.PosSemidef) (hr : X.rank ≤ 2) :
    ∃ (u v : n → ℝ) (α β : ℝ),
      0 ≤ β ∧ β ≤ α ∧ u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 ∧
        X = α • vecMulVec u u + β • vecMulVec v v := by
  let hA := hX.isHermitian
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  let i0 : n := e ⟨0, Fintype.card_pos⟩
  let i1 : n := e ⟨1, Fintype.one_lt_card⟩
  let u : n → ℝ := hA.eigenvectorBasis i0
  let v : n → ℝ := hA.eigenvectorBasis i1
  let α := hA.eigenvalues i0
  let β := hA.eigenvalues i1
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val (e.injective h)
    exact Nat.zero_ne_one this
  have hβ : 0 ≤ β := hX.eigenvalues_nonneg i1
  have hβα : β ≤ α := by
    have : hA.eigenvalues₀ ⟨1, Fintype.one_lt_card⟩ ≤
        hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩ :=
      hA.eigenvalues₀_antitone (Fin.zero_le _)
    simpa [α, β, i0, i1, e, IsHermitian.eigenvalues] using this
  have hu : u ⬝ᵥ u = 1 := eigenvectorBasis_dotProduct_self hA i0
  have hv : v ⬝ᵥ v = 1 := eigenvectorBasis_dotProduct_self hA i1
  have huv : u ⬝ᵥ v = 0 := eigenvectorBasis_dotProduct hA hne
  have htail (k : n) (hk0 : k ≠ i0) (hk1 : k ≠ i1) : hA.eigenvalues k = 0 := by
    by_contra hnz
    have hkpos : 0 < hA.eigenvalues k :=
      lt_of_le_of_ne (hX.eigenvalues_nonneg k) (Ne.symm hnz)
    have h0 : e.symm k ≠ ⟨0, Fintype.card_pos⟩ := by
      intro h
      apply hk0
      simpa [i0, e] using (e.apply_symm_apply k).symm.trans (congrArg e h)
    have h1 : e.symm k ≠ ⟨1, Fintype.one_lt_card⟩ := by
      intro h
      apply hk1
      simpa [i1, e] using (e.apply_symm_apply k).symm.trans (congrArg e h)
    have hval : 2 ≤ (e.symm k).val := by
      have : (e.symm k).val ≠ 0 ∧ (e.symm k).val ≠ 1 :=
        ⟨fun h ↦ h0 (Fin.ext h), fun h ↦ h1 (Fin.ext h)⟩
      omega
    have h0pos : 0 < hA.eigenvalues i0 := by
      have : hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩ ≥ hA.eigenvalues₀ (e.symm k) :=
        hA.eigenvalues₀_antitone (Fin.zero_le _)
      have : α ≥ hA.eigenvalues k := by
        simpa [α, i0, e, IsHermitian.eigenvalues] using this
      exact lt_of_lt_of_le hkpos this
    have h1pos : 0 < hA.eigenvalues i1 := by
      have : hA.eigenvalues₀ ⟨1, Fintype.one_lt_card⟩ ≥ hA.eigenvalues₀ (e.symm k) :=
        hA.eigenvalues₀_antitone
          (Fin.le_iff_val_le_val.mpr (by
            change 1 ≤ (e.symm k).val
            omega))
      have : β ≥ hA.eigenvalues k := by
        simpa [β, i1, e, IsHermitian.eigenvalues] using this
      exact lt_of_lt_of_le hkpos this
    have hsubset :
        ({i0, i1, k} : Finset n) ⊆
          univ.filter (fun j ↦ hA.eigenvalues j ≠ 0) := by
      intro j hj
      simp only [mem_insert, mem_singleton] at hj
      simp only [mem_filter, mem_univ, true_and]
      rcases hj with rfl | rfl | rfl
      · exact h0pos.ne'
      · exact h1pos.ne'
      · exact hnz
    have hcard3 : ({i0, i1, k} : Finset n).card = 3 := by
      have h01 : i0 ∉ ({i1, k} : Finset n) := by
        simp [mem_insert, mem_singleton, hne, hk0.symm]
      have h1k : i1 ∉ ({k} : Finset n) := by
        simp [mem_singleton, hk1.symm]
      rw [card_insert_of_notMem h01, card_insert_of_notMem h1k, card_singleton]
    have hle := card_le_card hsubset
    have hfilter :
        (univ.filter (fun j ↦ hA.eigenvalues j ≠ 0)).card =
          Fintype.card {j // hA.eigenvalues j ≠ 0} :=
      (Fintype.card_subtype _).symm
    have hrank : Fintype.card {j // hA.eigenvalues j ≠ 0} ≤ 2 := by
      rwa [← hA.rank_eq_card_non_zero_eigs]
    omega
  refine ⟨u, v, α, β, hβ, hβα, hu, hv, huv, ?_⟩
  have hx :
      X = ∑ k, hA.eigenvalues k •
        vecMulVec (hA.eigenvectorBasis k : n → ℝ)
          (hA.eigenvectorBasis k : n → ℝ) := by
    simpa [IsHermitian.eigenvectorUnitary_col_eq] using
      isHermitian_eq_sum_smul_vecMulVec hA
  have hdecomp :=
    (sum_add_sum_compl ({i0, i1} : Finset n)
      (fun k => hA.eigenvalues k •
        vecMulVec (hA.eigenvectorBasis k : n → ℝ)
          (hA.eigenvectorBasis k : n → ℝ))).symm
  have hpair :
      ∑ k ∈ ({i0, i1} : Finset n),
          hA.eigenvalues k •
            vecMulVec (hA.eigenvectorBasis k : n → ℝ)
              (hA.eigenvectorBasis k : n → ℝ) =
        α • vecMulVec u u + β • vecMulVec v v := by
    rw [sum_pair hne]
  have hrest :
      ∑ k ∈ ({i0, i1} : Finset n)ᶜ,
          hA.eigenvalues k •
            vecMulVec (hA.eigenvectorBasis k : n → ℝ)
              (hA.eigenvectorBasis k : n → ℝ) =
        0 := by
    refine sum_eq_zero fun k hk ↦ ?_
    have hk' : k ≠ i0 ∧ k ≠ i1 := by
      simpa [mem_compl, mem_insert, mem_singleton] using hk
    simp [htail k hk'.1 hk'.2]
  rw [hx, hdecomp, hpair, hrest, add_zero]

/-! ### CG01: two-dimensional variational comparison -/

lemma bessel_two {u v x : n → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) :
    (u ⬝ᵥ x) ^ 2 + (v ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  set a := u ⬝ᵥ x
  set b := v ⬝ᵥ x
  set w := a • u + b • v
  set y := x - w
  have hy : 0 ≤ y ⬝ᵥ y := by
    simp only [dotProduct]
    exact sum_nonneg fun _ _ ↦ mul_self_nonneg _
  have hxu : x ⬝ᵥ u = a := by rw [dotProduct_comm]
  have hxv : x ⬝ᵥ v = b := by rw [dotProduct_comm]
  have hxw : x ⬝ᵥ w = a ^ 2 + b ^ 2 := by
    simp [w, dotProduct_add, dotProduct_smul, hxu, hxv, pow_two]
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm, huv]
  have hww : w ⬝ᵥ w = a ^ 2 + b ^ 2 := by
    simp [w, dotProduct_add, dotProduct_smul, smul_dotProduct, hu, hv, huv, hvu]
    ring
  have hexpand : y ⬝ᵥ y = x ⬝ᵥ x - 2 * (x ⬝ᵥ w) + w ⬝ᵥ w := by
    simp [y, dotProduct_sub, dotProduct_comm w x]
    ring
  linarith

lemma sum_antitone_le_two_largest {m : ℕ} (hm : 2 ≤ m)
    (lam q : Fin m → ℝ) (hlam : Antitone lam)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hsum : ∑ i, q i = 2) :
    ∑ i, lam i * q i ≤ lam ⟨0, by omega⟩ + lam ⟨1, by omega⟩ := by
  set a : Fin m := ⟨0, by omega⟩
  set b : Fin m := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  have hdecomp :=
    (sum_add_sum_compl ({a, b} : Finset (Fin m)) (fun i ↦ lam i * q i)).symm
  rw [hdecomp, sum_pair hab]
  have hlamb (i : Fin m) (hi : i ∈ ({a, b} : Finset (Fin m))ᶜ) : lam i ≤ lam b := by
    have hib : i ≠ a ∧ i ≠ b := by
      simpa [mem_compl, mem_insert, mem_singleton] using hi
    have : b ≤ i := Fin.le_iff_val_le_val.mpr (by
      change 1 ≤ i.val
      have : i.val ≠ 0 ∧ i.val ≠ 1 :=
        ⟨fun h ↦ hib.1 (Fin.ext h), fun h ↦ hib.2 (Fin.ext h)⟩
      omega)
    exact hlam this
  have hrest :
      ∑ i ∈ ({a, b} : Finset (Fin m))ᶜ, lam i * q i ≤
        lam b * ∑ i ∈ ({a, b} : Finset (Fin m))ᶜ, q i := by
    rw [mul_sum]
    exact sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_right (hlamb i hi) (hq0 i)
  have hsum_rest :
      ∑ i ∈ ({a, b} : Finset (Fin m))ᶜ, q i = 2 - q a - q b := by
    have := (sum_add_sum_compl ({a, b} : Finset (Fin m)) q).symm
    simp only [sum_pair hab] at this
    linarith [hsum, this]
  have hstep :
      lam a * q a + lam b * q b +
          lam b * ∑ i ∈ ({a, b} : Finset (Fin m))ᶜ, q i =
        2 * lam b + (lam a - lam b) * q a := by
    rw [hsum_rest]
    ring
  have hlamab : lam b ≤ lam a :=
    hlam (show a ≤ b from Fin.le_iff_val_le_val.mpr (by simp [a, b]))
  have hfinal :
      2 * lam b + (lam a - lam b) * q a ≤ lam a + lam b := by
    have := mul_le_mul_of_nonneg_left (hq1 a) (sub_nonneg.mpr hlamab)
    linarith
  linarith [hrest, hstep, hfinal]

lemma orthonormal_pair_le_lambdaMax_add_lambdaSecond [Nontrivial n]
    (hB : B.IsHermitian) {u v : n → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) :
    u ⬝ᵥ B *ᵥ u + v ⬝ᵥ B *ᵥ v ≤ lambdaMax hB + lambdaSecond hB := by
  rw [isHermitian_quadratic hB, isHermitian_quadratic hB, ← sum_add_distrib]
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  let p : n → ℝ := fun k ↦
    ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 +
      ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ v) ^ 2
  have hterm (k : n) :
      hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 +
          hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ v) ^ 2 =
        hB.eigenvalues k * p k := by
    simp [p]
    ring
  simp_rw [hterm]
  let q : Fin (Fintype.card n) → ℝ := fun i ↦ p (e i)
  have hsumq : ∑ i, q i = 2 := by
    have hre := Fintype.sum_equiv e (fun i => p (e i)) p (fun _ => rfl)
    have hu' := parseval_eigenvectorBasis hB u
    have hv' := parseval_eigenvectorBasis hB v
    have hsump : ∑ k, p k = 2 := by
      simp only [p, sum_add_distrib]
      rw [hu', hv', hu, hv]
      norm_num
    simpa [q] using hre.trans hsump
  have hq0 (i : Fin (Fintype.card n)) : 0 ≤ q i :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hq1 (i : Fin (Fintype.card n)) : q i ≤ 1 := by
    have := bessel_two hu hv huv (x := (hB.eigenvectorBasis (e i) : n → ℝ))
    simpa [q, p, eigenvectorBasis_dotProduct_self hB, dotProduct_comm] using this
  have hreindex :
      ∑ k, hB.eigenvalues k * p k = ∑ i, hB.eigenvalues₀ i * q i := by
    have := Fintype.sum_equiv e
      (fun i ↦ hB.eigenvalues (e i) * p (e i))
      (fun k ↦ hB.eigenvalues k * p k) (fun _ ↦ rfl)
    refine this.symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    simp [q, IsHermitian.eigenvalues, e]
  rw [hreindex]
  have htwo : 2 ≤ Fintype.card n := Nat.succ_le_of_lt Fintype.one_lt_card
  have hbound :=
    sum_antitone_le_two_largest htwo hB.eigenvalues₀ q hB.eigenvalues₀_antitone
      hq0 hq1 hsumq
  simpa [lambdaMax, lambdaSecond, eigs₀] using hbound

/-! ### Inner products against rank-one terms -/

lemma inner_vecMulVec (C : Matrix n n ℝ) (u : n → ℝ) :
    inner C (vecMulVec u u) = u ⬝ᵥ C *ᵥ u := by
  rw [inner_eq_sum]
  simp_rw [vecMulVec_apply]
  have h : ∑ i, ∑ j, C i j * (u i * u j) = ∑ i, u i * ∑ j, C i j * u j := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    calc
      ∑ j, C i j * (u i * u j) = ∑ j, u i * (C i j * u j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring
      _ = u i * ∑ j, C i j * u j := (Finset.mul_sum _ _ _).symm
  rw [h]
  simp [dotProduct, mulVec]

lemma inner_smul_vecMulVec (r : ℝ) (C : Matrix n n ℝ) (u : n → ℝ) :
    inner C (r • vecMulVec u u) = r * (u ⬝ᵥ C *ᵥ u) := by
  rw [inner_smul_right, inner_vecMulVec]

lemma inner_vecMulVec_vecMulVec (u v : n → ℝ) :
    inner (vecMulVec u u) (vecMulVec v v) = (u ⬝ᵥ v) ^ 2 := by
  rw [inner_vecMulVec, vecMulVec_mulVec_real, dotProduct_smul, smul_eq_mul,
    mul_comm, dotProduct_comm, pow_two]

lemma inner_rankTwo (C : Matrix n n ℝ) (u v : n → ℝ) (α β : ℝ) :
    inner C (α • vecMulVec u u + β • vecMulVec v v) =
      α * (u ⬝ᵥ C *ᵥ u) + β * (v ⬝ᵥ C *ᵥ v) := by
  simp [inner_add_right, inner_smul_vecMulVec]

lemma inner_self_rankTwo {u v : n → ℝ} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : u ⬝ᵥ v = 0) (α β : ℝ) :
    inner (α • vecMulVec u u + β • vecMulVec v v)
        (α • vecMulVec u u + β • vecMulVec v v) =
      α ^ 2 + β ^ 2 := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm, huv]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  simp [inner_vecMulVec_vecMulVec, hu, hv, huv, hvu]
  ring

lemma cauchySchwarz_two (α β a b : ℝ) :
    α * a + β * b ≤
      Real.sqrt (α ^ 2 + β ^ 2) * Real.sqrt (a ^ 2 + b ^ 2) := by
  have hcs : (α * a + β * b) ^ 2 ≤ (α ^ 2 + β ^ 2) * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (α * b - β * a)]
  have hnn : 0 ≤ α ^ 2 + β ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    α * a + β * b
        ≤ |α * a + β * b| := le_abs_self _
    _ = Real.sqrt ((α * a + β * b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((α ^ 2 + β ^ 2) * (a ^ 2 + b ^ 2)) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (α ^ 2 + β ^ 2) * Real.sqrt (a ^ 2 + b ^ 2) :=
      Real.sqrt_mul hnn _

/-! ### Order-one writing -/

lemma exists_card_one_writing (hn : Fintype.card n = 1) {X : Matrix n n ℝ}
    (hX : X.PosSemidef) :
    ∃ (u : n → ℝ) (α : ℝ),
      0 ≤ α ∧ u ⬝ᵥ u = 1 ∧ X = α • vecMulVec u u := by
  haveI : Nonempty n := Fintype.card_pos_iff.mp (by rw [hn]; norm_num)
  let hA := hX.isHermitian
  let i0 : n := Classical.arbitrary n
  let u : n → ℝ := hA.eigenvectorBasis i0
  let α := hA.eigenvalues i0
  have huniq : ∀ k : n, k = i0 := fun k ↦
    Fintype.card_le_one_iff.mp (by rw [hn]) k i0
  refine ⟨u, α, hX.eigenvalues_nonneg i0, eigenvectorBasis_dotProduct_self hA i0, ?_⟩
  have hx :
      X = ∑ k, hA.eigenvalues k •
        vecMulVec (hA.eigenvectorBasis k : n → ℝ)
          (hA.eigenvectorBasis k : n → ℝ) := by
    simpa [IsHermitian.eigenvectorUnitary_col_eq] using
      isHermitian_eq_sum_smul_vecMulVec hA
  rw [hx, Fintype.sum_eq_single i0]
  intro k hk
  exact absurd (huniq k) hk

/-! ### CG03: `lem:variational` -/

lemma variational_lemma (hB : B.IsHermitian) {X : Matrix n n ℝ}
    (hX : X.PosSemidef) (hr : X.rank ≤ 2) :
    inner B X ≤ Real.sqrt (F hB) * Real.sqrt (inner X X) := by
  by_cases hnt : Nontrivial n
  · haveI := hnt
    obtain ⟨u, v, α, β, hβ, hβα, hu, hv, huv, hXeq⟩ :=
      exists_rankTwo_writing hX hr
    have hα : 0 ≤ α := hβ.trans hβα
    rw [hXeq, inner_rankTwo, inner_self_rankTwo hu hv huv]
    have hcomb :
        α * (u ⬝ᵥ B *ᵥ u) + β * (v ⬝ᵥ B *ᵥ v) =
          (α - β) * (u ⬝ᵥ B *ᵥ u) +
            β * (u ⬝ᵥ B *ᵥ u + v ⬝ᵥ B *ᵥ v) := by ring
    rw [hcomb]
    have hR := rayleigh_le_lambdaMax hB hu
    have h2 := orthonormal_pair_le_lambdaMax_add_lambdaSecond hB hu hv huv
    have hle :
        (α - β) * (u ⬝ᵥ B *ᵥ u) +
            β * (u ⬝ᵥ B *ᵥ u + v ⬝ᵥ B *ᵥ v) ≤
          (α - β) * lambdaMax hB + β * (lambdaMax hB + lambdaSecond hB) :=
      add_le_add (mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr hβα))
        (mul_le_mul_of_nonneg_left h2 hβ)
    have hsimp :
        (α - β) * lambdaMax hB + β * (lambdaMax hB + lambdaSecond hB) =
          α * lambdaMax hB + β * lambdaSecond hB := by ring
    refine (hle.trans_eq hsimp).trans ?_
    have hpos :
        α * lambdaMax hB + β * lambdaSecond hB ≤
          α * max (lambdaMax hB) 0 + β * max (lambdaSecond hB) 0 :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hα)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hβ)
    refine hpos.trans ?_
    have hCS := cauchySchwarz_two α β (max (lambdaMax hB) 0) (max (lambdaSecond hB) 0)
    have hF : F hB = (max (lambdaMax hB) 0) ^ 2 + (max (lambdaSecond hB) 0) ^ 2 :=
      F_eq hB
    simpa [hF, mul_comm] using hCS
  · have hcard : Fintype.card n ≤ 1 :=
      Nat.not_lt.mp (mt Fintype.one_lt_card_iff_nontrivial.mp hnt)
    by_cases hpos : 0 < Fintype.card n
    · have hn : Fintype.card n = 1 := le_antisymm hcard hpos
      haveI : Nonempty n := Fintype.card_pos_iff.mp hpos
      obtain ⟨u, α, hα, hu, hXeq⟩ := exists_card_one_writing hn hX
      rw [hXeq, inner_smul_vecMulVec]
      have hXX : inner (α • vecMulVec u u) (α • vecMulVec u u) = α ^ 2 := by
        simp [inner_smul_left, inner_smul_right, inner_vecMulVec_vecMulVec, hu, pow_two]
      rw [hXX]
      have hR := rayleigh_le_lambdaMax hB hu
      have hle : α * (u ⬝ᵥ B *ᵥ u) ≤ α * max (lambdaMax hB) 0 :=
        mul_le_mul_of_nonneg_left (hR.trans (le_max_left _ _)) hα
      refine hle.trans ?_
      have hF : F hB = (max (lambdaMax hB) 0) ^ 2 := by
        unfold F lambdaMax eigs₀
        have hz : 0 < Fintype.card n := hpos
        have h1 : ¬ 1 < Fintype.card n := by rw [hn]; norm_num
        rw [dif_pos hz, dif_neg h1]
      have hCS := cauchySchwarz_two α 0 (max (lambdaMax hB) 0) 0
      simpa [hF, mul_comm] using hCS
    · have hF : F hB = 0 := by
        unfold F
        rw [dif_neg hpos]
      have hinter : inner B X = 0 := by
        have : IsEmpty n := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hpos)
        simp [inner_eq_sum]
      simp [hF, hinter]

end

end BN
