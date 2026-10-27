/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs

noncomputable section
namespace Conj43

/-- Along an affine path, the larger acute angle has the larger tangent derivative.
This is the one-dimensional form of the paper's coordinate monotonicity argument. -/
theorem extensions_tan_path_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (b B : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i ∈ s,
      0 < b + t * w i ∧ b + t * w i < Real.pi / 2)
    (hU : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < B + t * ∑ i ∈ s, w i ∧ B + t * ∑ i ∈ s, w i < Real.pi / 2)
    (horder : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i ∈ s,
      b + t * w i ≤ B + t * ∑ i ∈ s, w i) :
    (∑ i ∈ s, Real.tan (b + w i)) - Real.tan (B + ∑ i ∈ s, w i) ≤
      (∑ _i ∈ s, Real.tan b) - Real.tan B := by
  let W := ∑ i ∈ s, w i
  let Q := fun t : ℝ => (∑ i ∈ s, Real.tan (b + t * w i)) - Real.tan (B + t * W)
  let D := fun t : ℝ => (∑ i ∈ s, (1 / Real.cos (b + t * w i) ^ 2) * w i) -
    (1 / Real.cos (B + t * W) ^ 2) * W
  have hc (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : ι) (hi : i ∈ s) :
      0 < Real.cos (b + t * w i) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(hx t ht i hi).1, Real.pi_pos], (hx t ht i hi).2⟩
  have hC (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      0 < Real.cos (B + t * W) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(hU t ht).1, Real.pi_pos], (hU t ht).2⟩
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt Q (D t) t := by
    have hi (i : ι) (his : i ∈ s) :
        HasDerivAt (fun t : ℝ => Real.tan (b + t * w i))
          ((1 / Real.cos (b + t * w i) ^ 2) * w i) t := by
      have hl : HasDerivAt (fun t : ℝ => b + t * w i) (w i) t := by
        simpa using ((hasDerivAt_id t).mul_const (w i)).const_add b
      exact (Real.hasDerivAt_tan (hc t ht i his).ne').comp t hl
    have hl : HasDerivAt (fun t : ℝ => B + t * W) W t := by
      simpa using ((hasDerivAt_id t).mul_const W).const_add B
    have htan : HasDerivAt (fun z : ℝ => Real.tan (B + z * W))
        ((1 / Real.cos (B + t * W) ^ 2) * W) t := by
      have hbase : HasDerivAt Real.tan (1 / Real.cos (B + t * W) ^ 2) (B + t * W) :=
        Real.hasDerivAt_tan (hC t ht).ne'
      simpa only [Function.comp_def] using hbase.comp t hl
    exact (HasDerivAt.fun_sum hi).sub htan
  have hD (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : D t ≤ 0 := by
    have hle : (∑ i ∈ s, (1 / Real.cos (b + t * w i) ^ 2) * w i) ≤
        ∑ i ∈ s, (1 / Real.cos (B + t * W) ^ 2) * w i := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (hw i hi)
      have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (hx t ht i hi).1.le
        (show B + t * W ≤ Real.pi by linarith [(hU t ht).2, Real.pi_pos])
        (horder t ht i hi)
      have hsq : Real.cos (B + t * W) ^ 2 ≤ Real.cos (b + t * w i) ^ 2 := by
        nlinarith [hc t ht i hi, hC t ht]
      exact one_div_le_one_div_of_le (sq_pos_of_pos (hC t ht)) hsq
    rw [← Finset.mul_sum] at hle
    exact sub_nonpos.mpr hle
  have hanti : AntitoneOn Q (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact hD t (interior_subset ht)
  have he := hanti (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  simpa [Q, W] using he

end Conj43
