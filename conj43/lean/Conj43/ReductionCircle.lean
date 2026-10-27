/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionComponents

/-! Elementary cyclic-order reductions ported from the Apache-2.0
`Conj43.InterfaceChordsProofs` at the frozen HEAD (its helper lemmas are private).
The modulus, strict endpoint convention and exit-before-entry order are preserved. -/
namespace Conj43
namespace Reduction
variable {n : ℕ}

lemma step_formula {m a b : ℕ} (ha : a < m) (hb : b < m) :
    step m a b = if a ≤ b then b-a else b+m-a := by
  unfold step
  split_ifs with h
  · have he : b+m-a = (b-a)+m := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

lemma clockwise_cases {m a b c d : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m) :
    Clockwise4 m a b c d ↔
      (a < b ∧ b < c ∧ c < d) ∨ (b < c ∧ c < d ∧ d < a) ∨
      (c < d ∧ d < a ∧ a < b) ∨ (d < a ∧ a < b ∧ b < c) := by
  unfold Clockwise4
  rw [step_formula ha hb, step_formula hb hc, step_formula hc hd, step_formula hd ha]
  split_ifs <;> omega

lemma inside_cases {m a b c : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) :
    insideArc m a b c ↔
      (a < c ∧ c < b) ∨ (b < a ∧ (a < c ∨ c < b)) := by
  unfold insideArc
  rw [step_formula ha hc, step_formula ha hb]
  split_ifs <;> omega

lemma entry_eq (F : LooplessBAP n) (p : Fin n) :
    entryPos F p = 5*(F.σ.symm p : ℕ)+4 := by
  change (5*(F.σ.symm p : ℕ)+4) % (5*n) = _
  have hs := (F.σ.symm p).isLt
  exact Nat.mod_eq_of_lt (by omega)

lemma entry_lt (F : LooplessBAP n) (p : Fin n) : entryPos F p < 5*n := by
  rw [entry_eq]; have := (F.σ.symm p).isLt; omega
lemma exit_lt (p : Fin n) : exitPos p < 5*n := by
  unfold exitPos; have := p.isLt; omega

/-- A crossing pair whose individual chords do not straddle a cut lies on one side of it. -/
lemma crossing_same_side {m a b c d e f : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m) (he : e < m) (hf : f < m)
    (hcross : Clockwise4 m c d e f)
    (hce : insideArc m a b c ↔ insideArc m a b e)
    (hdf : insideArc m a b d ↔ insideArc m a b f) :
    insideArc m a b c ↔ insideArc m a b d := by
  rw [clockwise_cases hc hd he hf] at hcross
  rw [inside_cases ha hb hc, inside_cases ha hb he] at hce
  rw [inside_cases ha hb hd, inside_cases ha hb hf] at hdf
  rw [inside_cases ha hb hc, inside_cases ha hb hd]
  omega

/-- Nonseparation is symmetric for four distinct endpoints. -/
lemma nonseparation_symm {m a b c d : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (insideArc m a b c ↔ insideArc m a b d) ↔
      (insideArc m c d a ↔ insideArc m c d b) := by
  rw [inside_cases ha hb hc, inside_cases ha hb hd,
    inside_cases hc hd ha, inside_cases hc hd hb]
  omega

lemma outside_no_cross (F : LooplessBAP n) (p : Fin n) {r q : Fin n}
    (hr : r ∉ component F p) (hq : q ∈ component F p) : ¬ crossAdj F r q := by
  intro h
  exact hr (reduction_component_closed F p hq h.symm)

lemma outside_chord_same_side (F : LooplessBAP n) (p : Fin n) {r q : Fin n}
    (hr : r ∉ component F p) (hq : q ∈ component F p) :
    insideArc (5*n) (entryPos F r) (exitPos r) (entryPos F q) ↔
      insideArc (5*n) (entryPos F r) (exitPos r) (exitPos q) := by
  have hne : r ≠ q := fun he => hr (he ▸ hq)
  have hn := outside_no_cross F p hr hq
  have hi := crossEdge_iff_interleave F r q hne
  unfold chordsInterleave at hi
  change ¬ (CrossEdge F r q ∨ CrossEdge F q r) at hn
  tauto

lemma outside_component_same_side (F : LooplessBAP n) (p : Fin n) {r q : Fin n}
    (hr : r ∉ component F p) (hq : q ∈ component F p) :
    insideArc (5*n) (entryPos F r) (exitPos r) (entryPos F p) ↔
      insideArc (5*n) (entryPos F r) (exitPos r) (entryPos F q) := by
  have h := (mem_component_iff F p q).mp hq
  induction h with
  | refl => rfl
  | @tail b c hab hbc ih =>
    have hb : b ∈ component F p := (mem_component_iff F p b).mpr hab
    have hc : c ∈ component F p := reduction_component_closed F p hb hbc
    have h1 := outside_chord_same_side F p hr hb
    have h2 := outside_chord_same_side F p hr hc
    have ha := entry_lt F r
    have hd := exit_lt r
    rcases hbc with he | he
    · exact (ih hb).trans (crossing_same_side ha hd (entry_lt F b) (entry_lt F c)
        (exit_lt b) (exit_lt c) he h1 h2)
    · exact (ih hb).trans (crossing_same_side ha hd (entry_lt F c) (entry_lt F b)
        (exit_lt c) (exit_lt b) he h2 h1).symm

/-- An outside strand cannot separate two surviving entries. -/
lemma outside_entry_arc (F : LooplessBAP n) (p : Fin n) {r u v : Fin n}
    (hr : r ∉ component F p) (hu : u ∈ component F p) (hv : v ∈ component F p) :
    insideArc (5*n) (entryPos F u) (entryPos F v) (entryPos F r) ↔
      insideArc (5*n) (entryPos F u) (entryPos F v) (exitPos r) := by
  have hru : r ≠ u := fun h => hr (h ▸ hu)
  have hrv : r ≠ v := fun h => hr (h ▸ hv)
  have du := chord_endpoints_distinct F r u hru
  have dv := chord_endpoints_distinct F r v hrv
  have h := (outside_component_same_side F p hr hu).symm.trans
    (outside_component_same_side F p hr hv)
  exact (nonseparation_symm (entry_lt F r) (exit_lt r) (entry_lt F u) (entry_lt F v)
    du.2.1 dv.2.1 du.2.2.2.1 dv.2.2.2.1).mp h

end Reduction
end Conj43
