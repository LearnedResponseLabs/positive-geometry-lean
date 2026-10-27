/- SPDX-License-Identifier: Apache-2.0 -/
import TP.CrossingAdapterDefs
namespace TP
variable {n : ℕ}

/-! ### Group `crossing_adapter`: the decorated extension of CLH-5 -/

/-- Crossings do not see the decoration: they are those of `lean_conj43`'s encoding of the underlying
permutation, in which every fixed point is a coloop. -/
theorem decCrossEdge_iff (hn : 0 < n) (π : DecPerm n) (p q : Fin n) :
    π.CrossEdge p q ↔ Conj43.CrossEdge ⟨π.perm⟩ p q := by
  sorry

theorem decCrossEdges_eq (π : DecPerm n) : π.crossEdges = Conj43.crossEdges ⟨π.perm⟩ := by
  sorry

/-- **W-P for decorated permutations.** The crossing edges of every decorated permutation, loops allowed,
split into vertex-simple winding-one cycles of length at least three. -/
theorem dec_winding_one_partition (π : DecPerm n) :
    ∃ cycles : List (List (Fin n)),
      (∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ Conj43.winding c = n) ∧
      (cycles.flatMap Conj43.cycleEdges).Perm π.crossEdges := by
  sorry

end TP
