/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs
import Conj43.CotCycle

noncomputable section
namespace Conj43

lemma extensions_kappa_endpoint (m : ℕ) (hm : 0 < m) :
    kappaStar m (Real.pi / m) = Real.cot (Real.pi / m) := by
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : ((m : ℝ) - 1) * (Real.pi / m) = Real.pi - Real.pi / m := by
    field_simp
  unfold kappaStar
  rw [he, cot_pi_sub]
  field_simp
  <;> ring

lemma extensions_angle_upper (m : ℕ) (η : ℝ) (α : Fin m → ℝ)
    (hα : ∀ i, η ≤ α i) (hsum : ∑ i, α i = Real.pi) (i : Fin m) :
    α i + ((m : ℝ) - 1) * η ≤ Real.pi := by
  have h := Finset.add_sum_erase Finset.univ α (Finset.mem_univ i)
  have hl : ((m : ℝ) - 1) * η ≤ ∑ j ∈ Finset.univ.erase i, α j := by
    have he : ((Finset.univ.erase i).card : ℝ) = (m : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_sub (by have := i.isLt; omega : 1 ≤ m), Nat.cast_one]
    simpa only [Finset.sum_const, nsmul_eq_mul, he] using
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ.erase i) => hα j)
  rw [hsum] at h
  linarith

lemma extensions_angle_pair (m : ℕ) (η : ℝ) (α : Fin m → ℝ)
    (hα : ∀ i, η ≤ α i) (hsum : ∑ i, α i = Real.pi)
    (i j : Fin m) (hij : i ≠ j) :
    α i + α j + ((m : ℝ) - 2) * η ≤ Real.pi := by
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have h1 := Finset.add_sum_erase Finset.univ α (Finset.mem_univ i)
  have h2 := Finset.add_sum_erase (Finset.univ.erase i) α hj
  have hcard : ((Finset.univ.erase i).erase j).card = m - 2 := by
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hm2 : 2 ≤ m := by
    have hi := i.isLt
    have hj := j.isLt
    have he : i.val ≠ j.val := fun h => hij (Fin.ext h)
    omega
  have hl : ((m : ℝ) - 2) * η ≤ ∑ k ∈ (Finset.univ.erase i).erase j, α k := by
    simpa only [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_sub hm2, Nat.cast_ofNat] using
      Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ.erase i).erase j) => hα k)
  rw [hsum] at h1
  linarith

lemma extensions_boundary_reciprocal (m : ℕ) (hm : 0 < m) (η : ℝ)
    (hA : Real.cot η - kappaStar m η ≠ 0)
    (hB : Real.cot (Real.pi - ((m : ℝ) - 1) * η) - kappaStar m η ≠ 0) :
    ((m : ℝ) - 1) * (Real.cot η - kappaStar m η)⁻¹ +
      (Real.cot (Real.pi - ((m : ℝ) - 1) * η) - kappaStar m η)⁻¹ = 0 := by
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  rw [cot_pi_sub]
  unfold kappaStar
  field_simp
  <;> ring

end Conj43
