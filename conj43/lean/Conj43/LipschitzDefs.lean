/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs

noncomputable section
namespace Conj43
variable {n : ℕ}

/-- The logarithmic necklace-gradient coordinates `G_f(θ) = B ℓ(θ)`, `ℓ_e = log sin δ_e(θ)` (`prop:grad`); the same
expression as the main challenge's `G` and the body of `gradientMap`. -/
def necklaceGradient (F : LooplessBAP n) (θ : Fin n → ℝ) : Fin n → ℝ :=
  (realB F).mulVec (fun j => Real.log (Real.sin (delta θ (edgeOf F j))))

/-- The Euclidean norm `‖x‖₂ = √(Σ xᵢ²)`, written out because Mathlib's norm on `Fin n → ℝ` is the sup norm. -/
def euclidNorm (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- A component shift: a vector constant on each connected component of the crossing graph `G_f^x`, i.e. in the
span of the `𝟙_C`. -/
def ComponentShift (F : LooplessBAP n) (c : Fin n → ℝ) : Prop :=
  ∀ p q, SameComponent F p q → c p = c q

/-- The norm of the class of `x` in the component-shift quotient: `‖[x]‖_quot = inf_c ‖x − c‖₂` over the component
shifts `c` (attained at the minimum-norm representative). -/
def quotNorm (F : LooplessBAP n) (x : Fin n → ℝ) : ℝ :=
  sInf ((fun c => euclidNorm (x - c)) '' {c | ComponentShift F c})

end Conj43
