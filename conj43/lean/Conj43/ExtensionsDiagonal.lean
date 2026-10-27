/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs

noncomputable section
namespace Conj43

/-- The sufficient half of the paper's reciprocal diagonal criterion. -/
theorem extensions_diagonal_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a d : ι → ℝ) (j : ι) (hcard : 2 ≤ Fintype.card ι)
    (hneg : a j < 0) (hpos : ∀ i, i ≠ j → 0 < a i)
    (hd : ∑ i, d i = 0) (hrec : ∑ i, (a i)⁻¹ ≤ 0) :
    0 ≤ ∑ i, a i * d i ^ 2 := by
  let s := Finset.univ.erase j
  have hs : s.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
    omega
  have hpos' (i : ι) (hi : i ∈ s) : 0 < (a i)⁻¹ :=
    inv_pos.mpr (hpos i (Finset.mem_erase.mp hi).1)
  have hT : 0 < ∑ i ∈ s, (a i)⁻¹ := Finset.sum_pos hpos' hs
  have hsd := Finset.add_sum_erase Finset.univ d (Finset.mem_univ j)
  have hsa := Finset.add_sum_erase Finset.univ (fun i => (a i)⁻¹) (Finset.mem_univ j)
  have hsq := Finset.add_sum_erase Finset.univ (fun i => a i * d i ^ 2) (Finset.mem_univ j)
  change d j + ∑ i ∈ s, d i = _ at hsd
  change (a j)⁻¹ + ∑ i ∈ s, (a i)⁻¹ = _ at hsa
  change a j * d j ^ 2 + ∑ i ∈ s, a i * d i ^ 2 = _ at hsq
  rw [hd] at hsd
  have hbound : (a j)⁻¹ + ∑ i ∈ s, (a i)⁻¹ ≤ 0 := by linarith
  have hm := mul_le_mul_of_nonpos_right hbound hneg.le
  have hprod : 0 ≤ 1 + a j * ∑ i ∈ s, (a i)⁻¹ := by
    rw [add_mul, inv_mul_cancel₀ hneg.ne, zero_mul] at hm
    nlinarith
  have hengel := Finset.sq_sum_div_le_sum_sq_div s d hpos'
  simp only [div_inv_eq_mul] at hengel
  have hds : (∑ i ∈ s, d i) ^ 2 = d j ^ 2 := by
    have : ∑ i ∈ s, d i = -d j := by linarith
    rw [this]
    ring
  rw [hds] at hengel
  have hengel' := (div_le_iff₀ hT).mp hengel
  have he : (∑ i ∈ s, d i ^ 2 * a i) = ∑ i ∈ s, a i * d i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at hengel'
  rw [← hsq]
  have hmul := mul_nonneg hprod (sq_nonneg (d j))
  by_contra h
  have hbad := mul_neg_of_pos_of_neg hT (lt_of_not_ge h)
  nlinarith

end Conj43
