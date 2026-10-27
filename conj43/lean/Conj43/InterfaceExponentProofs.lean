/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceRefinedProofs
import Conj43.InterfaceCrossingProofs
import Conj43.PairOrders
namespace Conj43
variable {n : ℕ}


private theorem residue_preimage (hn : 0 < n) (F : LooplessBAP n) (s p : Fin n) :
    (galashinOf F ((s : ℤ)+1)-1) % (n : ℤ) = (p : ℤ) ↔ s = F.σ.symm p := by
  simp only [galashinOf, add_sub_cancel_right, f_mod hn, residue_fin]
  constructor
  · intro h
    have he : F.σ s = p := Fin.ext (by exact_mod_cast h)
    exact F.σ.injective (he.trans (F.σ.apply_symm_apply p).symm)
  · rintro rfl
    simp

private theorem misUD_swap (F : LooplessBAP n) (p q : Fin n) : MisUD F p q ↔ MisUD F q p := by
  unfold MisUD
  exact cw4_rot.trans cw4_rot

private theorem misDU_swap (F : LooplessBAP n) (p q : Fin n) : MisDU F p q ↔ MisDU F q p := by
  unfold MisDU
  exact cw4_rot.trans cw4_rot

/-! ### Group `exponent`: INT3, Galashin's (5.8) -/

theorem misUD_iff_galashin (hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    MisUD F p q ↔ galashinMisUD (galashinOf F) p q := by
  have henc := encode_clockwise4 (n := n) (F.σ.symm p, true) (p, false)
    (F.σ.symm q, true) (q, false)
  simp only [galashinMisUD, residue_preimage hn]
  simp only [exists_and_left, exists_eq_left]
  simpa only [MisUD, entryPos_eq, exitPos, pos5, pos2, refinedEntry, refinedExit,
    Equiv.Perm.inv_def, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using henc

theorem misDU_iff_galashin (hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    MisDU F p q ↔ galashinMisDU (galashinOf F) p q := by
  have hp := p.isLt
  have hq := q.isLt
  have hs := (F.σ.symm p).isLt
  have ht := (F.σ.symm q).isLt
  simp only [galashinMisDU, residue_preimage hn]
  simp only [exists_and_left, exists_eq_left]
  unfold MisDU
  rw [entryPos_eq, entryPos_eq]
  unfold exitPos
  rw [negPos_of_pos (by omega) (by omega), negPos_of_pos (by omega) (by omega),
    negPos_of_pos (by omega) (by omega), negPos_of_pos (by omega) (by omega),
    cw4_mirror (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), cw4_rot]
  simpa only [pos5, pos2, refinedEntry, refinedExit, Equiv.Perm.inv_def, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
    encode_clockwise4 (n := n) (q, false) (F.σ.symm q, true) (p, false) (F.σ.symm p, true)

/-- **INT3.** `pairExponent` is the exponent of the pair `{p, q}` on necklace row `r` in Galashin's (5.8),
with the row read through his affine necklace formula. -/
theorem pairExponent_eq_galashin (hn : 0 < n) (F : LooplessBAP n) (r p q : Fin n) (hpq : p ≠ q) :
    pairExponent F r (p, q) =
      galashinExponent (galashinOf F) (galashinNecklace (galashinOf F) ((r : ℤ) + 1)) p q := by
  classical
  rw [← galashin_necklace hn F r]
  unfold pairExponent galashinExponent
  simp only [← misUD_iff_galashin hn, ← misDU_iff_galashin hn,
    galashinCross, ← crossEdge_iff_affine hn]
  by_cases h : p ≤ q
  · simp only [min_eq_left h, max_eq_right h]
  · have h' : q ≤ p := le_of_not_ge h
    simp only [min_eq_right h', max_eq_left h', misUD_swap F q p, misDU_swap F q p]
    have hu : (MisUD F p q ∧ q ∈ necklace F r ∧ p ∈ necklace F r) ↔
      (MisUD F p q ∧ p ∈ necklace F r ∧ q ∈ necklace F r) := by tauto
    have hd : (MisDU F p q ∧ q ∉ necklace F r ∧ p ∉ necklace F r) ↔
      (MisDU F p q ∧ p ∉ necklace F r ∧ q ∉ necklace F r) := by tauto
    simp only [hu, hd]
    ring


end Conj43
