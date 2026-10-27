/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceChordsDefs
namespace Conj43
 theorem crossEdge_irrefl {n : ℕ} (F : LooplessBAP n) (p : Fin n) :
    ¬ CrossEdge F p p := by sorry

 theorem chord_endpoints_distinct {n : ℕ} (F : LooplessBAP n) (p q : Fin n)
    (hpq : p ≠ q) :
    entryPos F p ≠ exitPos p ∧ entryPos F p ≠ entryPos F q ∧
    entryPos F p ≠ exitPos q ∧ exitPos p ≠ entryPos F q ∧
    exitPos p ≠ exitPos q ∧ entryPos F q ≠ exitPos q := by sorry

 theorem crossEdge_iff_interleave {n : ℕ} (F : LooplessBAP n) (p q : Fin n)
    (hpq : p ≠ q) :
    (CrossEdge F p q ∨ CrossEdge F q p) ↔
      chordsInterleave (5*n) (entryPos F p) (exitPos p)
        (entryPos F q) (exitPos q) := by sorry
end Conj43
