/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionComponents
namespace Conj43

/-- A concrete interval enumeration, identified by its order and range. -/
lemma reduction_labels_affine {n : ℕ} (C : Finset (Fin n)) (a : ℕ)
    (hbound : a + C.card ≤ n)
    (hrange : ∀ x : Fin n, x ∈ C ↔ a ≤ x.val ∧ x.val < a + C.card)
    (j : Fin C.card) : (labelsOf C j).val = a + j.val := by
  let f : Fin C.card → Fin n := fun i => ⟨a + i.val, by have := i.isLt; omega⟩
  have he : f = C.orderEmbOfFin rfl := Finset.orderEmbOfFin_unique rfl
    (fun i => (hrange _).mpr ⟨by dsimp [f]; omega, by dsimp [f]; have := i.isLt; omega⟩)
    (by intro i j hij; change a + i.val < a + j.val; exact Nat.add_lt_add_left hij a)
  exact congrArg Fin.val (congrFun he j).symm

theorem component_not_sigma_stable :
    component FSwap 0 = {0} ∧ FSwap.σ 0 ∉ component FSwap 0 := by
  decide

theorem entryMapOn_not_bijective :
    ¬ Function.Bijective (entryMapOn FTop3 {0, 1}) := by
  have hc : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have lab (j : Fin ({0, 1} : Finset (Fin 3)).card) :
      (labelsOf ({0, 1} : Finset (Fin 3)) j).val = j.val := by
    simpa using reduction_labels_affine ({0, 1} : Finset (Fin 3)) 0 (by decide)
      (by decide) j
  let i : Fin ({0, 1} : Finset (Fin 3)).card := ⟨0, by omega⟩
  let j : Fin ({0, 1} : Finset (Fin 3)).card := ⟨1, by omega⟩
  have hi : labelsOf ({0, 1} : Finset (Fin 3)) i = 0 := Fin.ext (lab i)
  have hj : labelsOf ({0, 1} : Finset (Fin 3)) j = 1 := Fin.ext (lab j)
  intro h
  have he : entryMapOn FTop3 {0, 1} i = entryMapOn FTop3 {0, 1} j := by
    apply Fin.ext
    simp only [entryMapOn, hi, hj]
    decide
  have := congrArg Fin.val (h.1 he)
  change 0 = 1 at this
  omega

theorem restrict_coloop_fixed :
    (component FColoop 0).card = 1 ∧ ∃ i, (restrictBAP FColoop 0).σ i = i := by
  have hc : (component FColoop 0).card = 1 := by decide
  refine ⟨hc, ⟨0, by omega⟩, ?_⟩
  apply Fin.ext
  have := ((restrictBAP FColoop 0).σ ⟨0, by omega⟩).isLt
  omega

theorem fixture_two_components :
    component FTwo 0 = {0, 1, 2} ∧ component FTwo 3 = {3, 4, 5} ∧
      (∀ j, (restrictEntry FTwo 0 j : ℕ) = ((j : ℕ) + 1) % 3) ∧
      (∀ j, (restrictEntry FTwo 3 j : ℕ) = ((j : ℕ) + 1) % 3) := by
  have h0 : component FTwo 0 = {0, 1, 2} := by decide +kernel
  have h3 : component FTwo 3 = {3, 4, 5} := by decide +kernel
  refine ⟨h0, h3, ?_, ?_⟩
  · intro j
    have hc : (component FTwo 0).card = 3 := by rw [h0]; decide
    have hl : (labelsOf (component FTwo 0) j).val = j.val := by
      simpa using reduction_labels_affine (component FTwo 0) 0 (by rw [h0]; decide)
        (by rw [h0]; decide) j
    have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by have := j.isLt; omega
    rcases hj with hj | hj | hj
    all_goals
      have hv : labelsOf (component FTwo 0) j = ⟨j.val, by omega⟩ := Fin.ext hl
      simp only [restrictEntry, entryMapOn, hv, h0, hj]
      norm_num [FTwo, Equiv.Perm.inv_def, Finset.filter_insert, Finset.filter_singleton, Fin.le_def]
      all_goals exact of_decide_eq_true rfl
  · intro j
    have hc : (component FTwo 3).card = 3 := by rw [h3]; decide
    have hl : (labelsOf (component FTwo 3) j).val = 3 + j.val :=
      reduction_labels_affine (component FTwo 3) 3 (by rw [h3]; decide)
        (by rw [h3]; decide) j
    have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by have := j.isLt; omega
    rcases hj with hj | hj | hj
    all_goals
      have hv : labelsOf (component FTwo 3) j = ⟨3 + j.val, by omega⟩ := Fin.ext hl
      simp only [restrictEntry, entryMapOn, hv, h3, hj]
      norm_num [FTwo, Equiv.Perm.inv_def, Finset.filter_insert, Finset.filter_singleton, Fin.le_def]
      all_goals exact of_decide_eq_true rfl
end Conj43
