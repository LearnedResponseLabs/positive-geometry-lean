/- SPDX-License-Identifier: Apache-2.0 -/
import TP.DecPermAffine
import Conj43.InterfaceCrossingDefs

namespace TP

variable {n : ℕ}

/-! ### Definitions (to be frozen in `TP/CrossingAdapterDefs.lean`) -/

/-- Galashin's positive crossing `p → q` for a decorated permutation, on residues, read off its 0-based affine
lift `π.affine` (a black fixed point `i` is the loop `f(i) = i`, a white one the coloop `f(i) = i + n`). -/
def DecPerm.CrossEdge (π : DecPerm n) (p q : Fin n) : Prop :=
  ∃ P Q : ℤ, Int.ModEq (n : ℤ) P (p : ℤ) ∧ Int.ModEq (n : ℤ) Q (q : ℤ) ∧
    Conj43.affineCrossing π.affine n P Q

/-- The crossing edges of a decorated permutation, listed as `Conj43.crossEdges` lists them. -/
noncomputable def DecPerm.crossEdges (π : DecPerm n) : List (Fin n × Fin n) := by
  classical
  exact (List.finRange n).flatMap (fun p => (List.finRange n).filterMap
    (fun q => if π.CrossEdge p q then some (p, q) else none))


end TP
