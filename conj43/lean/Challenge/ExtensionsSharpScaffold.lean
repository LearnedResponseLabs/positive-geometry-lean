/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs

noncomputable section
namespace Conj43
variable {n : ℕ}

theorem kappaStar_pos (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (hη : 0 < η) (hηm : η ≤ Real.pi / m) :
    0 < kappaStar m η := by
  sorry

theorem kappaStar_lt_tan (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (hη : 0 < η) (hηm : η < Real.pi / m) :
    kappaStar m η < Real.tan (((m : ℝ) - 2) * η / 2) := by
  sorry

theorem sharp_cot_cycle (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (hη : 0 < η) (hηm : η ≤ Real.pi / m)
    (α d : Fin m → ℝ) (hα : ∀ i, η ≤ α i) (hsum : ∑ i, α i = Real.pi) (hd : ∑ i, d i = 0) :
    kappaStar m η * ∑ i, d i ^ 2 ≤ ∑ i, Real.cot (α i) * d i ^ 2 := by
  sorry

theorem sharp_cot_extremizer (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (hη : 0 < η) (hηm : η ≤ Real.pi / m) :
    (∀ i, η ≤ sharpAngles m η i) ∧ ∑ i, sharpAngles m η i = Real.pi ∧ ∑ i, sharpVelocity m i = 0 ∧
      ∑ i, Real.cot (sharpAngles m η i) * sharpVelocity m i ^ 2 =
        kappaStar m η * ∑ i, sharpVelocity m i ^ 2 := by
  sorry

end Conj43
