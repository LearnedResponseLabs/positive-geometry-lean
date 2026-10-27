/-
Conj43/CotCycle.lean — L1: proof of the cotangent cycle inequality (paper lem:cot).

Paper: main.tex of the accompanying paper, lem:cot.
Argument (paper-verbatim): at most one angle exceeds π/2.  If none does, all
cotangents are nonnegative and positivity of a single surviving term suffices.
If α j > π/2, set S := π - α j = ∑_{i ≠ j} α i < π/2; weighted Cauchy–Schwarz
(Engel form, `Finset.sq_sum_div_le_sum_sq_div`) bounds the i ≠ j part below by
(∑_{i≠j} d i)² / ∑_{i≠j} tan (α i) = d j² / ∑_{i≠j} tan (α i), and strict
superadditivity of tan on (0, π/2) gives ∑_{i≠j} tan (α i) < tan S, so when
d j ≠ 0 the total exceeds d j² / tan S + cot (α j) · d j² = 0.
-/
import Mathlib

namespace Conj43

/-! ### Strict superadditivity of `tan` on `(0, π/2)` -/

/-- Two-variable step: `tan x + tan y < tan (x + y)` for positive `x, y` with
`x + y < π/2`.  Via `tan x + tan y = sin (x+y) / (cos x · cos y)` and
`cos (x+y) = cos x · cos y - sin x · sin y < cos x · cos y`. -/
lemma tan_add_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y < Real.pi / 2) :
    Real.tan x + Real.tan y < Real.tan (x + y) := by
  have hpi := Real.pi_pos
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcxy : 0 < Real.cos (x + y) := Real.cos_pos_of_mem_Ioo ⟨by linarith, hxy⟩
  have hsxy : 0 < Real.sin (x + y) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h1 : Real.tan x + Real.tan y = Real.sin (x + y) / (Real.cos x * Real.cos y) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
      div_add_div _ _ hcx.ne' hcy.ne', Real.sin_add]
  have h2 : Real.cos (x + y) < Real.cos x * Real.cos y := by
    have hs : 0 < Real.sin x * Real.sin y :=
      mul_pos (Real.sin_pos_of_pos_of_lt_pi hx (by linarith))
        (Real.sin_pos_of_pos_of_lt_pi hy (by linarith))
    rw [Real.cos_add]; linarith
  rw [h1, Real.tan_eq_sin_div_cos]
  exact div_lt_div_of_pos_left hsxy hcxy h2

/-- Superadditivity of `tan` over a finite sum of positive angles with total
below `π/2` (non-strict; empty and singleton sums are equalities). -/
lemma sum_tan_le_tan_sum {ι : Type*} {s : Finset ι} {α : ι → ℝ}
    (hpos : ∀ i ∈ s, 0 < α i) (hlt : ∑ i ∈ s, α i < Real.pi / 2) :
    ∑ i ∈ s, Real.tan (α i) ≤ Real.tan (∑ i ∈ s, α i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hat ih =>
    rw [Finset.sum_cons] at hlt ⊢
    rw [Finset.sum_cons]
    have ha : 0 < α a := hpos a (Finset.mem_cons_self ..)
    have hpos' : ∀ i ∈ t, 0 < α i := fun i hi => hpos i (Finset.mem_cons_of_mem hi)
    have ht0 : 0 ≤ ∑ i ∈ t, α i := Finset.sum_nonneg fun i hi => (hpos' i hi).le
    have ih' := ih hpos' (by linarith)
    rcases ht0.eq_or_lt with h0 | h0
    · rw [← h0, add_zero]
      rw [← h0, Real.tan_zero] at ih'
      linarith
    · have hstep := tan_add_lt ha h0 hlt
      linarith

/-- Strict superadditivity of `tan`: at least two positive angles, total below
`π/2`. -/
lemma sum_tan_lt_tan_sum {ι : Type*} {s : Finset ι} {α : ι → ℝ}
    (hcard : 2 ≤ s.card) (hpos : ∀ i ∈ s, 0 < α i)
    (hlt : ∑ i ∈ s, α i < Real.pi / 2) :
    ∑ i ∈ s, Real.tan (α i) < Real.tan (∑ i ∈ s, α i) := by
  classical
  obtain ⟨j, hj⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hjα := Finset.add_sum_erase s α hj
  have hjtan := Finset.add_sum_erase s (fun i => Real.tan (α i)) hj
  have hne : (s.erase j).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hj]; omega
  have hpos' : ∀ i ∈ s.erase j, 0 < α i := fun i hi =>
    hpos i (Finset.mem_of_mem_erase hi)
  have ht0 : 0 < ∑ i ∈ s.erase j, α i := Finset.sum_pos hpos' hne
  have hαj : 0 < α j := hpos j hj
  have hle := sum_tan_le_tan_sum hpos' (by linarith)
  have hstep := tan_add_lt hαj ht0 (by rw [hjα]; exact hlt)
  rw [← hjα, ← hjtan]
  linarith

/-! ### Sign facts for `cot` -/

/-- `cot` is positive on `(0, π/2)`. -/
lemma cot_pos_of_lt_pi_div_two {x : ℝ} (h0 : 0 < x) (h2 : x < Real.pi / 2) :
    0 < Real.cot x := by
  have hpi := Real.pi_pos
  rw [Real.cot_eq_cos_div_sin]
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, h2⟩)
    (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith))

/-- `cot` is nonnegative on `(0, π/2]`. -/
lemma cot_nonneg_of_le_pi_div_two {x : ℝ} (h0 : 0 < x) (h2 : x ≤ Real.pi / 2) :
    0 ≤ Real.cot x := by
  have hpi := Real.pi_pos
  rw [Real.cot_eq_cos_div_sin]
  exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩)
    (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)).le

/-- The supplement identity `cot (π - x) = -cot x`. -/
lemma cot_pi_sub (x : ℝ) : Real.cot (Real.pi - x) = -Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub,
    Real.sin_pi_sub, neg_div]

/-! ### The cotangent cycle inequality -/

/-- Strict form of lem:cot: if some `d k ≠ 0`, the cotangent-weighted sum is
strictly positive. -/
theorem cot_cycle_pos {m : ℕ} (hm : 3 ≤ m) {α d : Fin m → ℝ}
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = Real.pi) (hd : ∑ i, d i = 0)
    (hne : ∃ k, d k ≠ 0) : 0 < ∑ i, Real.cot (α i) * d i ^ 2 := by
  have hpi := Real.pi_pos
  by_cases hex : ∃ j, Real.pi / 2 < α j
  · -- paper case 2: one angle exceeds π/2; Cauchy–Schwarz + strict tan bound
    obtain ⟨j, hj⟩ := hex
    have hjmem : j ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ j
    have hSα := Finset.add_sum_erase Finset.univ α hjmem
    have hSd := Finset.add_sum_erase Finset.univ d hjmem
    have hScot := Finset.add_sum_erase Finset.univ
      (fun i => Real.cot (α i) * d i ^ 2) hjmem
    rw [hsum] at hSα
    rw [hd] at hSd
    have hcard : 2 ≤ (Finset.univ.erase j).card := by
      rw [Finset.card_erase_of_mem hjmem, Finset.card_univ, Fintype.card_fin]
      omega
    have hsne : (Finset.univ.erase j).Nonempty := Finset.card_pos.mp (by omega)
    have hpos' : ∀ i ∈ Finset.univ.erase j, 0 < α i := fun i _ => hα i
    have hS0 : 0 < ∑ i ∈ Finset.univ.erase j, α i := Finset.sum_pos hpos' hsne
    have hS2 : ∑ i ∈ Finset.univ.erase j, α i < Real.pi / 2 := by linarith
    have hαlt : ∀ i ∈ Finset.univ.erase j, α i < Real.pi / 2 := fun i hi => by
      have hle : α i ≤ ∑ l ∈ Finset.univ.erase j, α l :=
        Finset.single_le_sum (fun l _ => (hα l).le) hi
      linarith
    have htanpos : ∀ i ∈ Finset.univ.erase j, 0 < Real.tan (α i) := fun i hi =>
      Real.tan_pos_of_pos_of_lt_pi_div_two (hα i) (hαlt i hi)
    have hT0 : 0 < ∑ i ∈ Finset.univ.erase j, Real.tan (α i) :=
      Finset.sum_pos htanpos hsne
    have hTlt := sum_tan_lt_tan_sum hcard hpos' hS2
    have hEngel : (∑ i ∈ Finset.univ.erase j, d i) ^ 2
          / ∑ i ∈ Finset.univ.erase j, Real.tan (α i)
        ≤ ∑ i ∈ Finset.univ.erase j, Real.cot (α i) * d i ^ 2 := by
      refine (Finset.sq_sum_div_le_sum_sq_div _ d htanpos).trans_eq
        (Finset.sum_congr rfl fun i _ => ?_)
      rw [div_eq_mul_inv, Real.tan_inv_eq_cot, mul_comm]
    by_cases hdj : d j = 0
    · -- the obtuse term vanishes; a positive acute term survives
      obtain ⟨k, hk⟩ := hne
      have hkj : k ≠ j := fun h => hk (h ▸ hdj)
      have hkmem : k ∈ Finset.univ.erase j :=
        Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩
      have hterm : Real.cot (α j) * d j ^ 2 = 0 := by rw [hdj]; ring
      rw [← hScot, hterm, zero_add]
      exact Finset.sum_pos'
        (fun i hi => mul_nonneg (cot_nonneg_of_le_pi_div_two (hα i) (hαlt i hi).le)
          (sq_nonneg _))
        ⟨k, hkmem, mul_pos (cot_pos_of_lt_pi_div_two (hα k) (hαlt k hkmem))
          (sq_pos_of_ne_zero hk)⟩
    · -- d j ≠ 0: the paper's strict chain
      have hd2 : 0 < d j ^ 2 := sq_pos_of_ne_zero hdj
      have hsd : ∑ i ∈ Finset.univ.erase j, d i = -d j := by linarith
      have hsq : (∑ i ∈ Finset.univ.erase j, d i) ^ 2 = d j ^ 2 := by
        rw [hsd]; ring
      have h1 : d j ^ 2 / Real.tan (∑ i ∈ Finset.univ.erase j, α i)
          < d j ^ 2 / ∑ i ∈ Finset.univ.erase j, Real.tan (α i) :=
        div_lt_div_of_pos_left hd2 hT0 hTlt
      have hαjS : α j = Real.pi - ∑ i ∈ Finset.univ.erase j, α i := by linarith
      have hcotj : Real.cot (α j) * d j ^ 2
          = -(d j ^ 2 / Real.tan (∑ i ∈ Finset.univ.erase j, α i)) := by
        rw [hαjS, cot_pi_sub, ← Real.tan_inv_eq_cot, neg_mul, inv_mul_eq_div]
      rw [← hScot, hcotj]
      rw [hsq] at hEngel
      linarith
  · -- paper case 1: all angles ≤ π/2, all cotangents nonnegative
    push Not at hex
    have key : ∃ i, d i ≠ 0 ∧ α i < Real.pi / 2 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨k, hk⟩ := hne
      have hk2 : Real.pi / 2 ≤ α k := hcon k hk
      have hzero : ∀ i, i ≠ k → d i = 0 := by
        intro i hik
        by_contra hdi
        have hi2 : Real.pi / 2 ≤ α i := hcon i hdi
        -- two right-or-more angles plus a third positive angle exceed π
        have hkmem : k ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ k
        have h1 := Finset.add_sum_erase Finset.univ α hkmem
        have himem : i ∈ Finset.univ.erase k :=
          Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩
        have h2 := Finset.add_sum_erase (Finset.univ.erase k) α himem
        have hres : ((Finset.univ.erase k).erase i).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem himem,
            Finset.card_erase_of_mem hkmem, Finset.card_univ, Fintype.card_fin]
          omega
        have h3 : 0 < ∑ l ∈ (Finset.univ.erase k).erase i, α l :=
          Finset.sum_pos (fun l _ => hα l) hres
        rw [hsum] at h1
        linarith
      have hdk : d k = 0 := by
        have h1 := Finset.add_sum_erase Finset.univ d (Finset.mem_univ k)
        have h2 : ∑ i ∈ Finset.univ.erase k, d i = 0 :=
          Finset.sum_eq_zero fun i hi => hzero i (Finset.mem_erase.mp hi).1
        rw [h2, add_zero, hd] at h1
        exact h1
      exact hk hdk
    obtain ⟨i0, hd0, hα0⟩ := key
    exact Finset.sum_pos'
      (fun i _ => mul_nonneg (cot_nonneg_of_le_pi_div_two (hα i) (hex i)) (sq_nonneg _))
      ⟨i0, Finset.mem_univ i0, mul_pos (cot_pos_of_lt_pi_div_two (hα i0) hα0)
        (sq_pos_of_ne_zero hd0)⟩

/-- **lem:cot**, full form: the cotangent-weighted quadratic form on a cycle of
length ≥ 3 with angles summing to π is PSD on the zero-sum hyperplane, with
kernel exactly `d = 0`. -/
theorem cot_cycle_inequality_proof (m : ℕ) (hm : 3 ≤ m) (α d : Fin m → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = Real.pi) (hd : ∑ i, d i = 0) :
    0 ≤ ∑ i, Real.cot (α i) * d i ^ 2 ∧
      ((∑ i, Real.cot (α i) * d i ^ 2) = 0 ↔ ∀ i, d i = 0) := by
  by_cases hzero : ∀ i, d i = 0
  · have h0 : ∑ i, Real.cot (α i) * d i ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hzero i]; ring
    exact ⟨h0.ge, ⟨fun _ => hzero, fun _ => h0⟩⟩
  · have hne : ∃ k, d k ≠ 0 := not_forall.mp hzero
    have hpos := cot_cycle_pos hm hα hsum hd hne
    exact ⟨hpos.le, ⟨fun h0 => absurd h0 hpos.ne', fun h => absurd h hzero⟩⟩

end Conj43
