/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceRefinedDefs
namespace Conj43
variable {n : ℕ}

/-! ### Group `count`: the cycle count of CLH-5 -/

/-- A duplicate-free cycle winds `n` times its number of wrapped edges (edges `p → q` with `q < p`). -/
theorem winding_eq_wrapped (c : List (Fin n)) (hc : c.Nodup) :
    winding c = n * (cycleEdges c).countP (fun e => e.2 < e.1) := by
  sorry

/-- **eq:wp-cycle-count.** Every winding-one partition of the crossing edges has as many cycles as there are
wrapped crossing edges. -/
theorem partition_card (F : LooplessBAP n) (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F)) :
    cycles.length = (crossEdges F).countP (fun e => e.2 < e.1) := by
  sorry

end Conj43
