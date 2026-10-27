/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.Defs

/-! ### Group `gradient_preimage`: the paper's Corollary 31

Frozen on 2026-10-23, after its proof (`Conj43/VariationalPreimage.lean`, ac5b188e05), unlike the other groups, whose
statements were frozen before their proofs. The definitions inside the statement are those of
`variational_image_minimizer` (S60), verbatim. -/

namespace Conj43

variable {n : ℕ}

/-- **cor:gradient-preimage.** Every `y` in the gradient image of the slice has exactly one preimage in the slice,
and that preimage is the unique minimizer of `Ψ(z) − y·z` there. -/
theorem variational_gradient_preimage (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∀ y ∈ G '' S, (∃! x, x ∈ S ∧ G x = y) ∧
      ∀ x ∈ S, G x = y →
        (∀ z ∈ S, Ψ x - dotProduct y x ≤ Ψ z - dotProduct y z) ∧
        ∀ w ∈ S, (∀ z ∈ S, Ψ w - dotProduct y w ≤ Ψ z - dotProduct y z) → w = x := by
  sorry

end Conj43
