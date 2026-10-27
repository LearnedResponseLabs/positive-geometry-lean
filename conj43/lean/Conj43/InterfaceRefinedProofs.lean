/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceRefinedDefs
import Conj43.RowDiff
namespace Conj43
variable {n : ℕ}


private theorem pos5_lt (a : Fin n × Bool) : pos5 a < 5 * n := by
  have := a.1.isLt
  rcases a with ⟨a, e⟩
  cases e <;> simp only [pos5, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem pos2_lt (a : Fin n × Bool) : pos2 a < 2 * n := by
  have := a.1.isLt
  rcases a with ⟨a, e⟩
  cases e <;> simp only [pos2, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem pos_order (a b : Fin n × Bool) : pos5 a < pos5 b ↔ pos2 a < pos2 b := by
  rcases a with ⟨a, ea⟩
  rcases b with ⟨b, eb⟩
  cases ea <;> cases eb <;> simp only [pos5, pos2, Bool.false_eq_true, ↓reduceIte] <;> omega

/-! ### Group `refined`: lem:halfopen and the encoding -/

/-- The `5n` encoding and the refined `2n`-point circle order any four refined points alike. -/
theorem encode_clockwise4 (a b c d : Fin n × Bool) :
    Clockwise4 (5 * n) (pos5 a) (pos5 b) (pos5 c) (pos5 d) ↔
      Clockwise4 (2 * n) (pos2 a) (pos2 b) (pos2 c) (pos2 d) := by
  have hn : 0 < n := Nat.zero_lt_of_lt a.1.isLt
  rw [cw4_iff_linear (by omega) (pos5_lt a) (pos5_lt b) (pos5_lt c) (pos5_lt d),
    cw4_iff_linear (by omega) (pos2_lt a) (pos2_lt b) (pos2_lt c) (pos2_lt d)]
  simp only [pos_order]

/-- **lem:halfopen (a).** The exit points in `J(u⁺, v⁻)` are those of the rows `(u, v]`. -/
theorem halfopen_a (u v r : Fin n) :
    InRefinedArc n u v (refinedExit r) ↔ InHalfOpen n u v r := by
  have hu := u.isLt
  have hv := v.isLt
  have hr := r.isLt
  have hn : 0 < n := by omega
  unfold InRefinedArc InHalfOpen refinedEntry refinedExit
  rcases step_spec (by omega : 0 < 2*n) (by omega : 2*(u:ℕ)+1 < 2*n)
      (by omega : 2*(r:ℕ) < 2*n) with ⟨h1,e1⟩ | ⟨h1,e1⟩ <;>
    rcases step_spec (by omega : 0 < 2*n) (by omega : 2*(u:ℕ)+1 < 2*n)
      (by omega : 2*(v:ℕ) < 2*n) with ⟨h2,e2⟩ | ⟨h2,e2⟩ <;>
      rcases step_spec hn hu hr with ⟨h3,e3⟩ | ⟨h3,e3⟩ <;>
        rcases step_spec hn hu hv with ⟨h4,e4⟩ | ⟨h4,e4⟩ <;> omega

/-- **lem:halfopen (b).** No refined point lies strictly between `j⁻` and `j⁺`. -/
theorem halfopen_b (j : Fin n) (pt : ℕ) :
    ¬ (0 < step (2 * n) (refinedExit j) pt ∧
        step (2 * n) (refinedExit j) pt < step (2 * n) (refinedExit j) (refinedEntry j)) := by
  have hj := j.isLt
  have he : step (2*n) (refinedExit j) (refinedEntry j) = 1 := by
    unfold refinedExit refinedEntry
    rcases step_spec (by omega : 0 < 2*n) (by omega : 2*(j:ℕ) < 2*n)
      (by omega : 2*(j:ℕ)+1 < 2*n) with ⟨h,e⟩ | ⟨h,e⟩ <;> omega
  rw [he]
  omega

/-- **lem:halfopen (c), eq:L1.** `a⁺, b⁻, c⁺, d⁻` clockwise: `(a, b]` and `(c, d]` are disjoint. -/
theorem halfopen_L1 (a b c d : Fin n)
    (h : Clockwise4 (2 * n) (refinedEntry a) (refinedExit b) (refinedEntry c) (refinedExit d))
    (r : Fin n) : ¬ (InHalfOpen n a b r ∧ InHalfOpen n c d r) := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have hr := r.isLt
  have hn : 0 < n := by omega
  unfold refinedEntry refinedExit at h
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at h
  unfold InHalfOpen
  rcases step_spec hn ha hr with ⟨h1,e1⟩ | ⟨h1,e1⟩ <;>
    rcases step_spec hn ha hb with ⟨h2,e2⟩ | ⟨h2,e2⟩ <;>
      rcases step_spec hn hc hr with ⟨h3,e3⟩ | ⟨h3,e3⟩ <;>
        rcases step_spec hn hc hd with ⟨h4,e4⟩ | ⟨h4,e4⟩ <;>
          omega

/-- **eq:L2.** `a⁺, b⁻, c⁺, d⁻` counterclockwise: `(a, b]` and `(c, d]` cover `[n]`. -/
theorem halfopen_L2 (a b c d : Fin n)
    (h : Clockwise4 (2 * n) (refinedExit d) (refinedEntry c) (refinedExit b) (refinedEntry a))
    (r : Fin n) : InHalfOpen n a b r ∨ InHalfOpen n c d r := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have hr := r.isLt
  have hn : 0 < n := by omega
  unfold refinedEntry refinedExit at h
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at h
  unfold InHalfOpen
  rcases step_spec hn ha hr with ⟨h1,e1⟩ | ⟨h1,e1⟩ <;>
    rcases step_spec hn ha hb with ⟨h2,e2⟩ | ⟨h2,e2⟩ <;>
      rcases step_spec hn hc hr with ⟨h3,e3⟩ | ⟨h3,e3⟩ <;>
        rcases step_spec hn hc hd with ⟨h4,e4⟩ | ⟨h4,e4⟩ <;>
          omega

/-- **eq:L3.** `a⁺, c⁺, b⁻, d⁻` clockwise: `(a, b] \ (c, d] = (a, c]`. -/
theorem halfopen_L3 (a b c d : Fin n)
    (h : Clockwise4 (2 * n) (refinedEntry a) (refinedEntry c) (refinedExit b) (refinedExit d))
    (r : Fin n) : (InHalfOpen n a b r ∧ ¬ InHalfOpen n c d r) ↔ InHalfOpen n a c r := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have hr := r.isLt
  have hn : 0 < n := by omega
  unfold refinedEntry refinedExit at h
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at h
  unfold InHalfOpen
  rcases step_spec hn ha hr with ⟨h1,e1⟩ | ⟨h1,e1⟩ <;>
    rcases step_spec hn ha hb with ⟨h2,e2⟩ | ⟨h2,e2⟩ <;>
      rcases step_spec hn hc hr with ⟨h3,e3⟩ | ⟨h3,e3⟩ <;>
        rcases step_spec hn hc hd with ⟨h4,e4⟩ | ⟨h4,e4⟩ <;>
          rcases step_spec hn ha hc with ⟨h5,e5⟩ | ⟨h5,e5⟩ <;> omega

/-- **eq:arc on the refined boundary.** Label `x` is in Lean's necklace row `r` (the paper's `I_{r+1}`)
exactly when the exit `r⁻` lies in `J(s_x⁺, x⁻)`, where `s_x = σ⁻¹(x)` is where the strand into `x` starts. -/
theorem necklace_iff_refinedArc (F : LooplessBAP n) (r x : Fin n) :
    x ∈ necklace F r ↔ InRefinedArc n (F.σ⁻¹ x) x (refinedExit r) := by
  rw [mem_necklace_iff, halfopen_a]
  rfl


end Conj43
