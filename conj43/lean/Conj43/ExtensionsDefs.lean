/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.L5Defs

/-! # CLH extensions: definitions (to be frozen in `Conj43/ExtensionsDefs.lean`)

Four statements of the CLH paper that the formal source does not yet contain: the first form of the cycle count
(`eq:wp-cycle-count`, by total advance), the sharp cotangent cycle inequality (`thm:sharp-cot`) with
`lem:sharp-localization`, the matrix half of the sharp Laplacian sandwich (`cor:sharp-laplacian-sandwich`), and the
combinatorial half of the all-rank shift (`cor:shift`). Labels are zero-based, as everywhere in `Conj43`. -/

noncomputable section

namespace Conj43

variable {n : ℕ}

/-- The sharp constant of `eq:sharp-kappa`: `κ*_m(η) = (cot η − (m − 1) cot((m − 1)η)) / m`. -/
def kappaStar (m : ℕ) (η : ℝ) : ℝ :=
  (Real.cot η - ((m : ℝ) - 1) * Real.cot (((m : ℝ) - 1) * η)) / m

/-- The extremal angles of `eq:sharp-extremizer`: `η` at every index but the last, `π − (m − 1)η` at the last. -/
def sharpAngles (m : ℕ) (η : ℝ) : Fin m → ℝ :=
  fun i => if (i : ℕ) + 1 = m then Real.pi - ((m : ℝ) - 1) * η else η

/-- The extremal velocity of `eq:sharp-extremizer`: `1` at every index but the last, `−(m − 1)` at the last. -/
def sharpVelocity (m : ℕ) : Fin m → ℝ :=
  fun i => if (i : ℕ) + 1 = m then -((m : ℝ) - 1) else 1

/-- The graph Laplacian `L_f^graph = B Bᵀ` of the crossing graph, with `B` the real incidence matrix. -/
def graphLaplacian (F : LooplessBAP n) : Matrix (Fin n) (Fin n) ℝ :=
  realB F * (realB F).transpose

/-- `κ*_{f,Z}(η)`: the minimum of `κ*_{|Z|}(η)` over the cycles `Z` of a winding-one partition, a cycle's length
being its number of vertices (equal to its number of edges). For an empty partition (no crossing edge) the value is
`0`; both sides of the sandwich then vanish. -/
def kappaStarZ (cycles : List (List (Fin n))) (η : ℝ) : ℝ :=
  ((cycles.map fun c => kappaStar c.length η).min?).getD 0

/-- Galashin's shift `f↓(p) = f(p − 1)` of the bounded affine permutation `F.f`. -/
def shiftF (F : LooplessBAP n) (p : ℤ) : ℤ :=
  F.f (p - 1)

/-- The electrical permutation of a matching `τ` (Galashin §7): the loopless bounded affine permutation whose residue
permutation is `p ↦ τ(p + 1)`, labels mod `n`. -/
def elecBAP (τ : Equiv.Perm (Fin n)) : LooplessBAP n :=
  ⟨(finRotate n).trans τ⟩

/-- The Ising permutation of a matching `τ` (Galashin §7): the loopless bounded affine permutation whose residue
permutation is `τ`. -/
def isingBAP (τ : Equiv.Perm (Fin n)) : LooplessBAP n :=
  ⟨τ⟩

end Conj43

