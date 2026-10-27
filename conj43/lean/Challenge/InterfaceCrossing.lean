/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceCrossingDefs
namespace Conj43
 theorem crossEdge_iff_affine {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    CrossEdge F p q ↔ ∃ P Q : ℤ,
      Int.ModEq (n : ℤ) P ((p : ℤ) + 1) ∧
      Int.ModEq (n : ℤ) Q ((q : ℤ) + 1) ∧ affineCrossing (galashinOf F) n P Q := by sorry

 theorem alignment_iff_affine {n : ℕ} (hn : 0 < n) (F : LooplessBAP n)
    (p q : Fin n) (hpq : p ≠ q) :
    (¬ CrossEdge F p q ∧ ¬ CrossEdge F q p ∧ ¬ MisUD F p q ∧ ¬ MisDU F p q) ↔
      affineAlignment (galashinOf F) p q := by sorry
end Conj43
