/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceRefinedDefs
namespace Conj43
variable {n : ℕ}

/-! ### Group `refined`: lem:halfopen and the encoding -/

/-- The `5n` encoding and the refined `2n`-point circle order any four refined points alike. -/
theorem encode_clockwise4 (a b c d : Fin n × Bool) :
    Clockwise4 (5 * n) (pos5 a) (pos5 b) (pos5 c) (pos5 d) ↔
      Clockwise4 (2 * n) (pos2 a) (pos2 b) (pos2 c) (pos2 d) := by
  sorry

/-- **lem:halfopen (a).** The exit points in `J(u⁺, v⁻)` are those of the rows `(u, v]`. -/
theorem halfopen_a (u v r : Fin n) :
    InRefinedArc n u v (refinedExit r) ↔ InHalfOpen n u v r := by
  sorry

/-- **lem:halfopen (b).** No refined point lies strictly between `j⁻` and `j⁺`. -/
theorem halfopen_b (j : Fin n) (pt : ℕ) :
    ¬ (0 < step (2 * n) (refinedExit j) pt ∧
        step (2 * n) (refinedExit j) pt < step (2 * n) (refinedExit j) (refinedEntry j)) := by
  sorry

/-- **lem:halfopen (c), eq:L1.** `a⁺, b⁻, c⁺, d⁻` clockwise: `(a, b]` and `(c, d]` are disjoint. -/
theorem halfopen_L1 (a b c d : Fin n)
    (h : Clockwise4 (2 * n) (refinedEntry a) (refinedExit b) (refinedEntry c) (refinedExit d))
    (r : Fin n) : ¬ (InHalfOpen n a b r ∧ InHalfOpen n c d r) := by
  sorry

/-- **eq:L2.** `a⁺, b⁻, c⁺, d⁻` counterclockwise: `(a, b]` and `(c, d]` cover `[n]`. -/
theorem halfopen_L2 (a b c d : Fin n)
    (h : Clockwise4 (2 * n) (refinedExit d) (refinedEntry c) (refinedExit b) (refinedEntry a))
    (r : Fin n) : InHalfOpen n a b r ∨ InHalfOpen n c d r := by
  sorry

/-- **eq:L3.** `a⁺, c⁺, b⁻, d⁻` clockwise: `(a, b] \ (c, d] = (a, c]`. -/
theorem halfopen_L3 (a b c d : Fin n)
    (h : Clockwise4 (2 * n) (refinedEntry a) (refinedEntry c) (refinedExit b) (refinedExit d))
    (r : Fin n) : (InHalfOpen n a b r ∧ ¬ InHalfOpen n c d r) ↔ InHalfOpen n a c r := by
  sorry

/-- **eq:arc on the refined boundary.** Label `x` is in Lean's necklace row `r` (the paper's `I_{r+1}`)
exactly when the exit `r⁻` lies in `J(s_x⁺, x⁻)`, where `s_x = σ⁻¹(x)` is where the strand into `x` starts. -/
theorem necklace_iff_refinedArc (F : LooplessBAP n) (r x : Fin n) :
    x ∈ necklace F r ↔ InRefinedArc n (F.σ⁻¹ x) x (refinedExit r) := by
  sorry


end Conj43
