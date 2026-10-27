/-
Conj43/PairExponentClosed.lean — the necklace-row exponent of a pair in closed form (reading-edition note for
statement S19).

On necklace rows both misalignment terms of `pairExponent` vanish (`misUD_support_empty`, `misDU_support_empty`:
the paper's eq:L1 and eq:L2), so only the crossing terms remain, and on a crossing t → h the exponent is −1 exactly on
the rows of the cyclic arc (s_t, s_h] (`pairExponent_of_cross`, eq:L3). Here s_x = σ⁻¹(x) is where the strand into x
starts. These lemmas are assembled below into one statement, and into the matching statement for the columns of M_N.
-/
import Conj43.FullColumns

namespace Conj43

variable {n : ℕ}

/-- **The exponent in closed form.** The exponent of the pair {p, q} on necklace row r is −1 when p → q is a crossing
and r ∈ (s_p, s_q], −1 when q → p is a crossing and r ∈ (s_q, s_p], and 0 otherwise. At most one of the two
orientations is a crossing, so at most one term is nonzero. -/
theorem pairExponent_closed (F : LooplessBAP n) (r p q : Fin n) :
    pairExponent F r (p, q) =
      (if CrossEdge F p q ∧ inArcN n (F.σ⁻¹ p : ℕ) (F.σ⁻¹ q : ℕ) (r : ℕ) then -1 else 0) +
      (if CrossEdge F q p ∧ inArcN n (F.σ⁻¹ q : ℕ) (F.σ⁻¹ p : ℕ) (r : ℕ) then -1 else 0) := by
  by_cases hpq : CrossEdge F p q
  · have hqp : ¬ CrossEdge F q p := (crossEdge_excl F hpq).2.2.2.2
    rw [pairExponent_of_cross F hpq r]
    simp [hpq, hqp]
  · by_cases hqp : CrossEdge F q p
    · rw [pairExponent_swap, pairExponent_of_cross F hqp r]
      simp [hpq, hqp]
    · rw [pairExponent_nonCross F p q r hpq hqp]
      simp [hpq, hqp]

/-- **The columns of M_N.** The column of a crossing edge t → h is −1 on the rows of (s_t, s_h] and 0 elsewhere. -/
theorem Mmat_closed (F : LooplessBAP n) (r : Fin n) (j : EdgeIdx F) :
    Mmat F r j =
      if inArcN n (F.σ⁻¹ (edgeOf F j).1 : ℕ) (F.σ⁻¹ (edgeOf F j).2 : ℕ) (r : ℕ) then -1 else 0 := by
  have hedge : CrossEdge F (edgeOf F j).1 (edgeOf F j).2 := crossEdge_of_mem F (List.get_mem _ j)
  simp only [Mmat, Matrix.of_apply]
  exact pairExponent_of_cross' F (edgeOf F j) hedge r

end Conj43

#print axioms Conj43.pairExponent_closed
#print axioms Conj43.Mmat_closed
