/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceChordsProofs
namespace Conj43

/-- Swapping the second chord's endpoints is an exact symmetry of the definition. -/
theorem chordsInterleave_swap_right (m a b c d : ℕ) :
    chordsInterleave m a b c d ↔ chordsInterleave m a b d c := by
  unfold chordsInterleave
  tauto

/-- A chord never interleaves with itself under the frozen strict-arc definition. -/
theorem chordsInterleave_self (m a b : ℕ) :
    ¬ chordsInterleave m a b a b := by
  simp [chordsInterleave, insideArc, step]

/-- The proposed omitted-hypothesis control is itself a theorem. -/
theorem crossEdge_iff_interleave_without_ne {n : ℕ} (F : LooplessBAP n) (p q : Fin n) :
    (CrossEdge F p q ∨ CrossEdge F q p) ↔
      chordsInterleave (5*n) (entryPos F p) (exitPos p)
        (entryPos F q) (exitPos q) := by
  by_cases hpq : p ≠ q
  · exact crossEdge_iff_interleave F p q hpq
  · have he : p = q := not_ne_iff.mp hpq
    subst q
    simp [crossEdge_irrefl, chordsInterleave_self]

private theorem control_step_formula {m a b : ℕ} (ha : a < m) (hb : b < m) :
    step m a b = if a ≤ b then b-a else b+m-a := by
  unfold step
  split_ifs with h
  · have he : b+m-a = (b-a)+m := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Neither boundary can be hit by a third, distinct position on the circle. -/
theorem arc_steps_avoid_boundaries {m a b c : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hac : a ≠ c) (hbc : b ≠ c) :
    0 < step m a c ∧ step m a c ≠ step m a b := by
  rw [control_step_formula ha hc, control_step_formula ha hb]
  split_ifs <;> omega

/-- All three readings of weakening the strict inequalities agree away from endpoints. -/
theorem insideArc_weak_variants_of_distinct {m a b c : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hac : a ≠ c) (hbc : b ≠ c) :
    (insideArc m a b c ↔ (0 < step m a c ∧ step m a c ≤ step m a b)) ∧
    (insideArc m a b c ↔ (0 ≤ step m a c ∧ step m a c < step m a b)) ∧
    (insideArc m a b c ↔ (0 ≤ step m a c ∧ step m a c ≤ step m a b)) := by
  have h := arc_steps_avoid_boundaries ha hb hc hac hbc
  unfold insideArc
  omega

/-- The weak upper boundary changes the definition at the excluded terminal endpoint. -/
theorem insideArc_weak_upper_endpoint_control :
    ¬ insideArc 5 0 3 3 ∧ (0 < step 5 0 3 ∧ step 5 0 3 ≤ step 5 0 3) := by
  norm_num [insideArc, step]

/-- The weak lower boundary changes the definition at the excluded initial endpoint. -/
theorem insideArc_weak_lower_endpoint_control :
    ¬ insideArc 5 0 3 0 ∧ (0 ≤ step 5 0 0 ∧ step 5 0 0 < step 5 0 3) := by
  norm_num [insideArc, step]
end Conj43
