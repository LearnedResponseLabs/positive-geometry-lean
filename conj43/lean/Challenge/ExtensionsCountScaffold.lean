/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs

noncomputable section
namespace Conj43
variable {n : ℕ}

theorem partition_advance (F : LooplessBAP n) (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F)) :
    n * cycles.length = ((crossEdges F).map fun e => adv e.1 e.2).sum := by
  sorry

theorem crossEdges_advance (F : LooplessBAP n) :
    ((crossEdges F).map fun e => adv e.1 e.2).sum = n * (crossEdges F).countP (fun e => e.2 < e.1) := by
  sorry

end Conj43
