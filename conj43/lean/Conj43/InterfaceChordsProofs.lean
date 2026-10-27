/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceChordsDefs
namespace Conj43

-- The two elementary cyclic-order reductions follow the accepted crossing proof.
private theorem step_formula {m a b : ℕ} (ha : a < m) (hb : b < m) :
    step m a b = if a ≤ b then b-a else b+m-a := by
  unfold step
  split_ifs with h
  · have he : b+m-a = (b-a)+m := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem clockwise_cases {m a b c d : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m) :
    Clockwise4 m a b c d ↔
      (a < b ∧ b < c ∧ c < d) ∨ (b < c ∧ c < d ∧ d < a) ∨
      (c < d ∧ d < a ∧ a < b) ∨ (d < a ∧ a < b ∧ b < c) := by
  unfold Clockwise4
  rw [step_formula ha hb, step_formula hb hc, step_formula hc hd, step_formula hd ha]
  split_ifs <;> omega

private theorem inside_cases {m a b c : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) :
    insideArc m a b c ↔
      (a < c ∧ c < b) ∨ (b < a ∧ (a < c ∨ c < b)) := by
  unfold insideArc
  rw [step_formula ha hc, step_formula ha hb]
  split_ifs <;> omega

private theorem entryPos_eq {n : ℕ} (F : LooplessBAP n) (p : Fin n) :
    entryPos F p = 5*(F.σ.symm p : ℕ)+4 := by
  change (5*(F.σ.symm p : ℕ)+4) % (5*n) = _
  have hs := (F.σ.symm p).isLt
  exact Nat.mod_eq_of_lt (by omega)

 theorem crossEdge_irrefl {n : ℕ} (F : LooplessBAP n) (p : Fin n) :
    ¬ CrossEdge F p p := by
  simp [CrossEdge, Clockwise4, step]

 theorem chord_endpoints_distinct {n : ℕ} (F : LooplessBAP n) (p q : Fin n)
    (hpq : p ≠ q) :
    entryPos F p ≠ exitPos p ∧ entryPos F p ≠ entryPos F q ∧
    entryPos F p ≠ exitPos q ∧ exitPos p ≠ entryPos F q ∧
    exitPos p ≠ exitPos q ∧ entryPos F q ≠ exitPos q := by
  have hst : F.σ.symm p ≠ F.σ.symm q := fun h => hpq (F.σ.symm.injective h)
  simp only [ne_eq, Fin.ext_iff] at hpq hst
  rw [entryPos_eq, entryPos_eq]
  unfold exitPos
  omega

private theorem cyclic_interleave {m a b c d : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m)
    (_hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Clockwise4 m a c b d ∨ Clockwise4 m c a d b) ↔
      chordsInterleave m a b c d := by
  rw [clockwise_cases ha hc hb hd, clockwise_cases hc ha hd hb]
  unfold chordsInterleave
  rw [inside_cases ha hb hc, inside_cases ha hb hd]
  omega

 theorem crossEdge_iff_interleave {n : ℕ} (F : LooplessBAP n) (p q : Fin n)
    (hpq : p ≠ q) :
    (CrossEdge F p q ∨ CrossEdge F q p) ↔
      chordsInterleave (5*n) (entryPos F p) (exitPos p)
        (entryPos F q) (exitPos q) := by
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := chord_endpoints_distinct F p q hpq
  have hp := p.isLt
  have hq := q.isLt
  have hs := (F.σ.symm p).isLt
  have ht := (F.σ.symm q).isLt
  have ha : entryPos F p < 5*n := by rw [entryPos_eq]; omega
  have hb : exitPos p < 5*n := by unfold exitPos; omega
  have hc : entryPos F q < 5*n := by rw [entryPos_eq]; omega
  have hd : exitPos q < 5*n := by unfold exitPos; omega
  exact cyclic_interleave ha hb hc hd hab hac had hbc hbd hcd
end Conj43
