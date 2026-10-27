/- SPDX-License-Identifier: Apache-2.0 -/
import TPAdapter.CrossingHelpers
import Conj43.Statements
namespace TP
variable {n : ℕ}

/-! ### Group `crossing_adapter`: the decorated extension of CLH-5 -/

/-- Crossings do not see the decoration: they are those of `lean_conj43`'s encoding of the underlying
permutation, in which every fixed point is a coloop. -/
theorem decCrossEdge_iff (hn : 0 < n) (π : DecPerm n) (p q : Fin n) :
    π.CrossEdge p q ↔ Conj43.CrossEdge ⟨π.perm⟩ p q := by
  rw [Conj43.crossEdge_iff_affine hn]
  constructor
  · rintro ⟨P,Q,hP,hQ,hcross⟩
    exact ⟨P+1,Q+1,hP.add_right 1,hQ.add_right 1,
      (affine_crossing_shift ⟨π.perm⟩ P Q).mp ((affine_crossing_ignore_loops hn π P Q).mp hcross)⟩
  · rintro ⟨P,Q,hP,hQ,hcross⟩
    have hp : Int.ModEq (n : ℤ) (P-1) (p : ℤ) := by
      simpa using hP.sub_right 1
    have hq : Int.ModEq (n : ℤ) (Q-1) (q : ℤ) := by
      simpa using hQ.sub_right 1
    refine ⟨P-1,Q-1,hp,hq,(affine_crossing_ignore_loops hn π _ _).mpr ?_⟩
    apply (affine_crossing_shift ⟨π.perm⟩ (P-1) (Q-1)).mpr
    simpa using hcross

theorem decCrossEdges_eq (π : DecPerm n) : π.crossEdges = Conj43.crossEdges ⟨π.perm⟩ := by
  classical
  unfold DecPerm.crossEdges Conj43.crossEdges
  congr 1
  funext p
  congr 1
  funext q
  simp only [decCrossEdge_iff (Nat.zero_lt_of_lt p.isLt)]

/-- **W-P for decorated permutations.** The crossing edges of every decorated permutation, loops allowed,
split into vertex-simple winding-one cycles of length at least three. -/
theorem dec_winding_one_partition (π : DecPerm n) :
    ∃ cycles : List (List (Fin n)),
      (∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ Conj43.winding c = n) ∧
      (cycles.flatMap Conj43.cycleEdges).Perm π.crossEdges := by
  rw [decCrossEdges_eq]
  exact Conj43.winding_one_partition n ⟨π.perm⟩

end TP
