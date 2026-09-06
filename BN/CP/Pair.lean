/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import BN.CP.Basic
import BN.Basic.Inner
import Mathlib.Data.Finset.Prod

/-!
# Pair updates in the completely positive cone

A rank-one Laplacian update `h • vecMulVec (e i - e j) (e i - e j)` with
`0 ≤ h ≤ C i j` stays inside the completely positive cone. Summing such
updates yields the weighted-Laplacian corollary.
-/

open Matrix

namespace BN

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option linter.unusedSectionVars false

/-- Replace coordinates `(i, j)` of `p` by `(p i + p j, 0)`. -/
def pairLeft (p : n → ℝ) (i j : n) : n → ℝ :=
  fun k => if k = i then p i + p j else if k = j then 0 else p k

/-- Replace coordinates `(i, j)` of `p` by `(0, p i + p j)`. -/
def pairRight (p : n → ℝ) (i j : n) : n → ℝ :=
  fun k => if k = i then 0 else if k = j then p i + p j else p k

lemma pairLeft_nonneg {p : n → ℝ} (hp : 0 ≤ p) (i j : n) : 0 ≤ pairLeft p i j := by
  intro k
  simp only [pairLeft]
  split_ifs
  · exact add_nonneg (hp i) (hp j)
  · exact le_rfl
  · exact hp k

lemma pairRight_nonneg {p : n → ℝ} (hp : 0 ≤ p) (i j : n) : 0 ≤ pairRight p i j := by
  intro k
  simp only [pairRight]
  split_ifs
  · exact le_rfl
  · exact add_nonneg (hp i) (hp j)
  · exact hp k

lemma pairLeft_eq (p : n → ℝ) {i j : n} (hij : i ≠ j) :
    pairLeft p i j = p + p j • (e i - e j) := by
  ext k
  change (if k = i then p i + p j else if k = j then 0 else p k) =
    p k + p j * (e i - e j) k
  rw [sub_single_apply hij]
  split_ifs with hki hkj
  · subst hki; ring
  · subst hkj; ring
  · ring

lemma pairRight_eq (p : n → ℝ) {i j : n} (hij : i ≠ j) :
    pairRight p i j = p - p i • (e i - e j) := by
  ext k
  change (if k = i then 0 else if k = j then p i + p j else p k) =
    p k - p i * (e i - e j) k
  rw [sub_single_apply hij]
  split_ifs with hki hkj
  · subst hki; ring
  · subst hkj; ring
  · ring

lemma vecMulVec_add_self (x y : n → ℝ) :
    vecMulVec (x + y) (x + y) =
      vecMulVec x x + vecMulVec x y + vecMulVec y x + vecMulVec y y := by
  rw [add_vecMulVec, vecMulVec_add, vecMulVec_add]
  abel

lemma vecMulVec_sub_self (x y : n → ℝ) :
    vecMulVec (x - y) (x - y) =
      vecMulVec x x - vecMulVec x y - vecMulVec y x + vecMulVec y y := by
  rw [sub_vecMulVec, vecMulVec_sub, vecMulVec_sub]
  abel

lemma vecMulVec_smul_self (c : ℝ) (x : n → ℝ) :
    vecMulVec (c • x) (c • x) = (c * c) • vecMulVec x x := by
  rw [smul_vecMulVec, vecMulVec_smul, smul_smul]

/-- **CP08.** Rank-one pair identity. -/
lemma rankOne_pair_identity {p : n → ℝ} {i j : n} (hij : i ≠ j)
    (hab : 0 < p i + p j) :
    vecMulVec p p + (p i * p j) • vecMulVec (e i - e j) (e i - e j) =
      (p i / (p i + p j)) • vecMulVec (pairLeft p i j) (pairLeft p i j) +
        (p j / (p i + p j)) • vecMulVec (pairRight p i j) (pairRight p i j) := by
  set a := p i
  set b := p j
  set s := a + b
  set d := e i - e j
  have hs : s ≠ 0 := hab.ne'
  have hU : pairLeft p i j = p + b • d := pairLeft_eq p hij
  have hV : pairRight p i j = p - a • d := pairRight_eq p hij
  have hUU :
      vecMulVec (pairLeft p i j) (pairLeft p i j) =
        vecMulVec p p + b • (vecMulVec p d + vecMulVec d p) + (b * b) • vecMulVec d d := by
    rw [hU, vecMulVec_add_self, vecMulVec_smul, smul_vecMulVec, vecMulVec_smul_self]
    rw [smul_add]
    abel
  have hVV :
      vecMulVec (pairRight p i j) (pairRight p i j) =
        vecMulVec p p - a • (vecMulVec p d + vecMulVec d p) + (a * a) • vecMulVec d d := by
    rw [hV, vecMulVec_sub_self, vecMulVec_smul, smul_vecMulVec, vecMulVec_smul_self]
    rw [smul_add]
    abel
  ext x y
  have h1 := congr_fun (congr_fun hUU x) y
  have h2 := congr_fun (congr_fun hVV x) y
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at h1 h2 ⊢
  rw [h1, h2]
  field_simp [hs]
  ring

lemma IsCompletelyPositive.sum {q : ℕ} (C : Fin q → Matrix n n ℝ)
    (hC : ∀ a, IsCompletelyPositive (C a)) :
    IsCompletelyPositive (∑ a, C a) := by
  induction q with
  | zero =>
    refine ⟨0, fun _ => 0, fun _ _ => le_rfl, ?_⟩
    simp
  | succ q ih =>
    rw [Fin.sum_univ_succ]
    exact (hC 0).add (ih (fun a => C a.succ) fun a => hC a.succ)

/-- Split a nonnegative `h` into summands bounded by a nonnegative family. -/
lemma exists_split_of_le_sum {q : ℕ} (bound : Fin q → ℝ) (h : ℝ)
    (h0 : 0 ≤ h) (hb : ∀ a, 0 ≤ bound a) (hle : h ≤ ∑ a, bound a) :
    ∃ alloc : Fin q → ℝ,
      (∀ a, 0 ≤ alloc a) ∧ (∀ a, alloc a ≤ bound a) ∧ ∑ a, alloc a = h := by
  induction q generalizing h with
  | zero =>
    refine ⟨fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun a => Fin.elim0 a, ?_⟩
    simp at hle ⊢
    linarith
  | succ q ih =>
    set b0 := bound 0
    set h0' := min h b0
    set h' := h - h0'
    have hh' : 0 ≤ h' := sub_nonneg.mpr (min_le_left _ _)
    have hle' : h' ≤ ∑ a : Fin q, bound a.succ := by
      rw [Fin.sum_univ_succ] at hle
      rcases le_total h b0 with hle0 | hge0
      · simp [h', h0', min_eq_left hle0]
        exact Finset.sum_nonneg fun a _ => hb a.succ
      · simp [h', h0', min_eq_right hge0]
        linarith
    obtain ⟨alloc', hnn, hbd, hsum⟩ :=
      ih (fun a => bound a.succ) h' hh' (fun a => hb a.succ) hle'
    refine ⟨Fin.cons h0' alloc', ?_, ?_, ?_⟩
    · intro a
      induction a using Fin.cases with
      | zero =>
        change 0 ≤ min h (bound 0)
        exact le_min_iff.2 ⟨h0, hb 0⟩
      | succ a => simpa using hnn a
    · intro a
      induction a using Fin.cases with
      | zero =>
        change min h (bound 0) ≤ bound 0
        exact min_le_right _ _
      | succ a => simpa using hbd a
    · rw [Fin.sum_univ_succ]
      simp [hsum, h']

lemma interpolate_pair {p : n → ℝ} {i j : n} {h t : ℝ}
    (ht : t * (p i * p j) = h) :
    (1 - t) • vecMulVec p p +
        t • (vecMulVec p p + (p i * p j) • vecMulVec (e i - e j) (e i - e j)) =
      vecMulVec p p + h • vecMulVec (e i - e j) (e i - e j) := by
  set L := vecMulVec (e i - e j) (e i - e j)
  set P := vecMulVec p p
  calc
    (1 - t) • P + t • (P + (p i * p j) • L)
        = (1 - t) • P + t • P + t • ((p i * p j) • L) := by
          rw [smul_add, add_assoc]
    _ = (1 - t + t) • P + (t * (p i * p j)) • L := by
          rw [← add_smul, smul_smul]
    _ = P + h • L := by
          simp [ht]

/-- **CP09.** A rank-one pair update with `0 ≤ h ≤ pᵢ pⱼ` stays completely positive. -/
lemma isCompletelyPositive_vecMulVec_add_smul_sub_single {p : n → ℝ} (hp : 0 ≤ p)
    {i j : n} (hij : i ≠ j) {h : ℝ} (h0 : 0 ≤ h) (hle : h ≤ p i * p j) :
    IsCompletelyPositive
      (vecMulVec p p + h • vecMulVec (e i - e j) (e i - e j)) := by
  set a := p i
  set b := p j
  by_cases hab0 : a * b = 0
  · have hh : h = 0 := le_antisymm (hle.trans_eq hab0) h0
    simpa [hh] using isCompletelyPositive_vecMulVec hp
  · have habpos : 0 < a * b :=
      lt_of_le_of_ne (mul_nonneg (hp i) (hp j)) (Ne.symm hab0)
    have ha : 0 < a := pos_of_mul_pos_left habpos (hp j)
    have hb : 0 < b := pos_of_mul_pos_right habpos (hp i)
    have habs : 0 < a + b := add_pos ha hb
    set t := h / (a * b)
    have ht0 : 0 ≤ t := div_nonneg h0 habpos.le
    have ht1 : t ≤ 1 := (div_le_one habpos).mpr hle
    have hth : t * (a * b) = h := div_mul_cancel₀ h hab0
    have hCP :
        IsCompletelyPositive
          (vecMulVec p p + (a * b) • vecMulVec (e i - e j) (e i - e j)) := by
      rw [rankOne_pair_identity hij habs]
      refine ((isCompletelyPositive_vecMulVec (pairLeft_nonneg hp i j)).smul ?_).add
        ((isCompletelyPositive_vecMulVec (pairRight_nonneg hp i j)).smul ?_)
      · exact div_nonneg ha.le habs.le
      · exact div_nonneg hb.le habs.le
    have hleft : IsCompletelyPositive ((1 - t) • vecMulVec p p) :=
      (isCompletelyPositive_vecMulVec hp).smul (sub_nonneg.mpr ht1)
    have := hleft.add (hCP.smul ht0)
    convert this using 1
    exact (interpolate_pair (p := p) (i := i) (j := j) (h := h) (t := t) hth).symm

/-- **CP10.** Lemma `lem:pair`. -/
lemma IsCompletelyPositive.add_smul_sub_single {C : Matrix n n ℝ}
    (hC : IsCompletelyPositive C) {i j : n} (hij : i ≠ j) {h : ℝ}
    (h0 : 0 ≤ h) (hle : h ≤ C i j) :
    IsCompletelyPositive (C + h • vecMulVec (e i - e j) (e i - e j)) := by
  obtain ⟨q, p, hp, rfl⟩ := hC
  have hCij : (∑ a, vecMulVec (p a) (p a)) i j = ∑ a, p a i * p a j := by
    simp [Matrix.sum_apply, vecMulVec_apply]
  rw [hCij] at hle
  have hbnd : ∀ a, 0 ≤ p a i * p a j := fun a => mul_nonneg (hp a i) (hp a j)
  obtain ⟨alloc, hnn, hbd, hsum⟩ :=
    exists_split_of_le_sum (fun a => p a i * p a j) h h0 hbnd hle
  have hdecomp :
      (∑ a, vecMulVec (p a) (p a)) + h • vecMulVec (e i - e j) (e i - e j) =
        ∑ a, (vecMulVec (p a) (p a) +
          alloc a • vecMulVec (e i - e j) (e i - e j)) := by
    rw [← hsum, Finset.sum_smul, ← Finset.sum_add_distrib]
  rw [hdecomp]
  exact IsCompletelyPositive.sum _ fun a =>
    isCompletelyPositive_vecMulVec_add_smul_sub_single (fun k => hp a k) hij (hnn a) (hbd a)

lemma vecMulVec_sub_single_offDiag {p q x y : n} (hpq : p ≠ q) (hxy : x ≠ y)
    (hpair : ({p, q} : Set n) ≠ {x, y}) :
    vecMulVec (e p - e q) (e p - e q) x y = 0 := by
  rw [vecMulVec_sub_single_apply hpq]
  split_ifs with h1 h2 h3 h4
  · exact (hxy (h1.1.trans h1.2.symm)).elim
  · exact (hxy (h2.1.trans h2.2.symm)).elim
  · exact (hpair (by simp [h3.1, h3.2])).elim
  · exact (hpair (by simp [h4.1, h4.2, Set.pair_comm])).elim
  · rfl

variable [LinearOrder n]

/-- Strictly upper-triangular off-diagonal pairs. -/
def offDiagLt : Finset (n × n) :=
  Finset.univ.offDiag.filter (fun p => p.1 < p.2)

lemma mem_offDiagLt {i j : n} : (i, j) ∈ offDiagLt ↔ i < j := by
  constructor
  · intro h
    simp [offDiagLt, Finset.mem_filter, Finset.mem_offDiag] at h
    exact h.2
  · intro h
    simp [offDiagLt, Finset.mem_filter, Finset.mem_offDiag, h.ne, h]

lemma eq_of_lt_pair {a b c d : n} (hab : a < b) (hcd : c < d)
    (h : ({a, b} : Set n) = {c, d}) : a = c ∧ b = d := by
  rcases Set.pair_eq_pair_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact (lt_irrefl _ (hab.trans hcd)).elim

/-- Weighted graph Laplacian `∑_{i<j} ℓᵢⱼ (eᵢ - eⱼ)(eᵢ - eⱼ)ᵀ`. -/
def weightedLaplacian (ℓ : n → n → ℝ) : Matrix n n ℝ :=
  ∑ p ∈ offDiagLt, ℓ p.1 p.2 • vecMulVec (e p.1 - e p.2) (e p.1 - e p.2)

lemma weightedLaplacian_apply_of_lt (ℓ : n → n → ℝ) {i j : n} (hij : i < j) :
    weightedLaplacian ℓ i j = -ℓ i j := by
  simp only [weightedLaplacian, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have himem : (i, j) ∈ offDiagLt := mem_offDiagLt.2 hij
  refine (Finset.sum_eq_single (i, j) ?_ ?_).trans ?_
  · intro p hp hne
    have hpq : p.1 ≠ p.2 :=
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).2.2
    have hplt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hpair : ({p.1, p.2} : Set n) ≠ {i, j} := by
      intro h
      exact hne (Prod.ext_iff.mpr (eq_of_lt_pair hplt hij h))
    simp [vecMulVec_sub_single_offDiag hpq hij.ne hpair]
  · intro h
    exact (h himem).elim
  · rw [vecMulVec_sub_single_apply hij.ne]
    simp [hij.ne, hij.ne.symm]

lemma weightedLaplacian_sum_apply_of_ne (s : Finset (n × n)) (hs : s ⊆ offDiagLt)
    (ℓ : n → n → ℝ) {i j : n} (hij : i ≠ j)
    (hmiss : ∀ p ∈ s, ({p.1, p.2} : Set n) ≠ {i, j}) :
    (∑ p ∈ s, ℓ p.1 p.2 • vecMulVec (e p.1 - e p.2) (e p.1 - e p.2)) i j = 0 := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpq : p.1 ≠ p.2 :=
    (Finset.mem_offDiag.mp (Finset.mem_filter.mp (hs hp)).1).2.2
  simp [vecMulVec_sub_single_offDiag hpq hij (hmiss p hp)]

lemma isCompletelyPositive_add_sum_pairs {C : Matrix n n ℝ} (hC : IsCompletelyPositive C)
    (ℓ : n → n → ℝ) (s : Finset (n × n)) (hs : s ⊆ offDiagLt)
    (hℓ : ∀ p ∈ s, 0 ≤ ℓ p.1 p.2) (hslack : ∀ p ∈ s, ℓ p.1 p.2 ≤ C p.1 p.2) :
    IsCompletelyPositive
      (C + ∑ p ∈ s, ℓ p.1 p.2 • vecMulVec (e p.1 - e p.2) (e p.1 - e p.2)) := by
  revert hℓ hslack hs
  refine s.induction_on ?empty ?insert
  · intro _ _ _
    simpa using hC
  · intro p s hps ih hs hℓ hslack
    have hp : p ∈ offDiagLt := hs (Finset.mem_insert_self _ _)
    have hplt : p.1 < p.2 := mem_offDiagLt.1 hp
    have hpne : p.1 ≠ p.2 := hplt.ne
    have hs' : s ⊆ offDiagLt := (Finset.subset_insert p s).trans hs
    have hℓ' : ∀ q ∈ s, 0 ≤ ℓ q.1 q.2 := fun q hq => hℓ q (Finset.mem_insert_of_mem hq)
    have hslack' : ∀ q ∈ s, ℓ q.1 q.2 ≤ C q.1 q.2 :=
      fun q hq => hslack q (Finset.mem_insert_of_mem hq)
    rw [Finset.sum_insert hps, add_comm (ℓ p.1 p.2 • _), ← add_assoc]
    refine (ih hs' hℓ' hslack').add_smul_sub_single hpne (hℓ p (Finset.mem_insert_self _ _)) ?_
    have hcur :
        (C + ∑ q ∈ s, ℓ q.1 q.2 • vecMulVec (e q.1 - e q.2) (e q.1 - e q.2)) p.1 p.2 =
          C p.1 p.2 := by
      simp only [Matrix.add_apply]
      have : (∑ q ∈ s, ℓ q.1 q.2 • vecMulVec (e q.1 - e q.2) (e q.1 - e q.2)) p.1 p.2 = 0 := by
        refine weightedLaplacian_sum_apply_of_ne s hs' ℓ hpne fun q hq hpair => ?_
        have hqlt : q.1 < q.2 := mem_offDiagLt.1 (hs' hq)
        have := eq_of_lt_pair hqlt hplt hpair
        exact hps (by simpa [Prod.ext_iff.mpr this] using hq)
      simp [this]
    simpa [hcur] using hslack p (Finset.mem_insert_self _ _)

/-- **CP11.** Corollary `cor:laplacian`. -/
lemma IsCompletelyPositive.add_weightedLaplacian {C : Matrix n n ℝ}
    (hC : IsCompletelyPositive C) {ℓ : n → n → ℝ} (hℓ : ∀ i j, i < j → 0 ≤ ℓ i j)
    (hCL : ∀ i j, 0 ≤ (C + weightedLaplacian ℓ) i j) :
    IsCompletelyPositive (C + weightedLaplacian ℓ) := by
  refine isCompletelyPositive_add_sum_pairs hC ℓ offDiagLt (Finset.Subset.refl _) ?_ ?_
  · intro p hp
    exact hℓ p.1 p.2 (mem_offDiagLt.1 hp)
  · intro p hp
    have hpij : p.1 < p.2 := mem_offDiagLt.1 hp
    have hnn : 0 ≤ (C + weightedLaplacian ℓ) p.1 p.2 := hCL _ _
    have hL : weightedLaplacian ℓ p.1 p.2 = -ℓ p.1 p.2 :=
      weightedLaplacian_apply_of_lt ℓ hpij
    have : 0 ≤ C p.1 p.2 - ℓ p.1 p.2 := by
      simpa [Matrix.add_apply, hL] using hnn
    linarith

end BN
