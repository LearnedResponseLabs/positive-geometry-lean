/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsTanPath

noncomputable section
namespace Conj43

lemma extensions_cot_shift (x φ : ℝ) (hs : Real.sin x ≠ 0) (hc : Real.cos φ ≠ 0) :
    Real.cot x - Real.tan φ = Real.cos (x + φ) / (Real.sin x * Real.cos φ) := by
  rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, div_sub_div _ _ hs hc,
    Real.cos_add]

lemma extensions_cot_shift_inv (x φ : ℝ) (hs : Real.sin x ≠ 0)
    (hc : Real.cos φ ≠ 0) (hcx : Real.cos (x + φ) ≠ 0) :
    (Real.cot x - Real.tan φ)⁻¹ =
      (Real.tan (x + φ) - Real.tan φ) * Real.cos φ ^ 2 := by
  have ht : Real.tan (x + φ) - Real.tan φ =
      Real.sin x / (Real.cos (x + φ) * Real.cos φ) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
      div_sub_div _ _ hcx hc, ← Real.sin_sub, add_sub_cancel_right]
  rw [extensions_cot_shift x φ hs hc, ht]
  field_simp

/-- Tangent reciprocal sums decrease from the equal small-angle boundary.
The final distinguished angle is represented as the complement of the sum. -/
lemma extensions_reciprocal_path {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (β : ι → ℝ) (η φ : ℝ)
    (hη : 0 < η) (hφ : 0 < φ) (hr : 2 ≤ s.card)
    (hloc : 2 * φ < ((s.card : ℝ) - 1) * η)
    (hβ : ∀ i ∈ s, η ≤ β i)
    (hβacute : ∀ i ∈ s, β i + φ < Real.pi / 2)
    (hSacute : (∑ i ∈ s, β i) - φ < Real.pi / 2) :
    (∑ i ∈ s, Real.tan (β i + φ)) - Real.tan ((∑ i ∈ s, β i) - φ) ≤
      (s.card : ℝ) * Real.tan (η + φ) - Real.tan ((s.card : ℝ) * η - φ) := by
  let w := fun i => β i - η
  have hw (i : ι) (hi : i ∈ s) : 0 ≤ w i := sub_nonneg.mpr (hβ i hi)
  have hW : (∑ i ∈ s, w i) = (∑ i ∈ s, β i) - (s.card : ℝ) * η := by
    simp [w, Finset.sum_sub_distrib]
  have hrl : (2 : ℝ) ≤ s.card := by exact_mod_cast hr
  have hstart : 0 < (s.card : ℝ) * η - φ := by nlinarith
  have hslo : (s.card : ℝ) * η ≤ ∑ i ∈ s, β i := by
    simpa using Finset.sum_le_sum hβ
  have hdom (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : ι) (hi : i ∈ s) :
      η ≤ η + t * w i ∧ η + t * w i ≤ β i := by
    have hwi := hw i hi
    dsimp [w] at *
    constructor <;> nlinarith [ht.1, ht.2]
  have hsumdom (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (s.card : ℝ) * η ≤ (s.card : ℝ) * η + t * ∑ i ∈ s, w i ∧
      (s.card : ℝ) * η + t * ∑ i ∈ s, w i ≤ ∑ i ∈ s, β i := by
    rw [hW]
    constructor <;> nlinarith [ht.1, ht.2]
  have ho (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : ι) (hi : i ∈ s) :
      η + φ + t * w i ≤ (s.card : ℝ) * η - φ + t * ∑ i ∈ s, w i := by
    have hwi : w i ≤ ∑ j ∈ s, w j := Finset.single_le_sum hw hi
    nlinarith [ht.1]
  have h := extensions_tan_path_le s w (η + φ) ((s.card : ℝ) * η - φ) hw
    (fun t ht i hi => by
      have hh := hdom t ht i hi
      constructor <;> linarith [hβacute i hi])
    (fun t ht => by
      have hh := hsumdom t ht
      constructor <;> linarith)
    ho
  have hi (i : ι) : η + φ + w i = β i + φ := by dsimp [w]; ring
  simp_rw [hi] at h
  rw [hW] at h
  have he : (s.card : ℝ) * η - φ + ((∑ i ∈ s, β i) - (s.card : ℝ) * η) =
      (∑ i ∈ s, β i) - φ := by ring
  rw [he] at h
  simpa using h

end Conj43
