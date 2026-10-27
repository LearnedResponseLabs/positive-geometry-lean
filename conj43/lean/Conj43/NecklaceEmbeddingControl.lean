-- SPDX-License-Identifier: Apache-2.0
import Conj43.NecklaceEmbeddingDefs
import Conj43.L6Slice

/-! An explicit one-parameter family in the frozen three-label fixture slice. -/
namespace Conj43

noncomputable def fixtureAngle (t : ℝ) : Fin 3 → ℝ := ![0, t, 2]

/-- This is a finite computation in the frozen endpoint conventions. -/
theorem fixture_crossing_iff (p q : Fin 3) :
    CrossEdge fixtureCycle p q ↔
      (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 2) ∨ (p = 2 ∧ q = 0) := by
  revert p q
  decide

/-- Every parameter strictly between zero and two supplies an actual slice point. -/
theorem fixtureAngle_mem {t : ℝ} (ht : 0 < t) (ht2 : t < 2) :
    fixtureAngle t ∈ GaugeSlice fixtureCycle 0 := by
  constructor
  · intro p q hpq
    rcases (fixture_crossing_iff p q).mp hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change 0 < t - 0 + Real.pi * 0 ∧ t - 0 + Real.pi * 0 < Real.pi
      constructor <;> linarith [Real.pi_gt_three]
    · change 0 < 2 - t + Real.pi * 0 ∧ 2 - t + Real.pi * 0 < Real.pi
      constructor <;> linarith [Real.pi_gt_three]
    · change 0 < 0 - 2 + Real.pi * 1 ∧ 0 - 2 + Real.pi * 1 < Real.pi
      constructor <;> linarith [Real.pi_gt_three]
  · intro p hp
    have hzero : SameComponent fixtureCycle p 0 := by
      fin_cases p
      · exact .refl
      · exact .single (Or.inr (by decide : CrossEdge fixtureCycle 0 1))
      · exact .single (Or.inl (by decide : CrossEdge fixtureCycle 2 0))
    have hp0 := hp 0 hzero
    have heq : p = 0 := le_antisymm hp0 (Fin.zero_le p)
    subst p
    rfl

end Conj43
