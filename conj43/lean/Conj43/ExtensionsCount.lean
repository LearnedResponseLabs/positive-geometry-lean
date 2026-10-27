/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs
import Conj43.PartitionCountProofs
import Conj43.Statements

namespace Conj43
variable {n : ℕ}

theorem partition_advance (F : LooplessBAP n) (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F)) :
    n * cycles.length = ((crossEdges F).map fun e => adv e.1 e.2).sum := by
  rw [← (hp.map (fun e => adv e.1 e.2)).sum_eq]
  clear hp
  induction cycles with
  | nil => simp
  | cons c cs ih =>
    have hw := (hc c (by simp)).2.2
    have ht := ih (fun d hd => hc d (List.mem_cons_of_mem _ hd))
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.length_cons]
    change n * (cs.length + 1) = winding c + _
    rw [hw, Nat.mul_add, Nat.mul_one, ht]
    omega

theorem crossEdges_advance (F : LooplessBAP n) :
    ((crossEdges F).map fun e => adv e.1 e.2).sum = n * (crossEdges F).countP (fun e => e.2 < e.1) := by
  obtain ⟨cycles, hc, hp⟩ := winding_one_partition n F
  rw [← partition_advance F cycles hc hp, partition_card F cycles hc hp]

end Conj43
