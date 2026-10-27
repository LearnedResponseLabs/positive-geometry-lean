/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.LipschitzDefs

noncomputable section
namespace Conj43
variable {n : ℕ}

/-- **Strong monotonicity** (the proof of `cor:sharp-laplacian-sandwich`): on a convex set where every crossing angle is
at least `η`, `G_f` is strongly monotone modulo component shifts, with constant `κ*_{f,Z}(η) λ_f⁺`, where `λ_f⁺` is the
smallest positive eigenvalue of `L_f^graph`. -/
theorem sharp_strong_monotone (F : LooplessBAP n) (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F))
    (η : ℝ) (hη : 0 < η) (hηZ : ∀ c ∈ cycles, η ≤ Real.pi / c.length)
    (lam : ℝ) (hlam : IsLeast {μ : ℝ | μ ∈ spectrum ℝ (graphLaplacian F) ∧ 0 < μ} lam)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hδ : ∀ θ ∈ C, ∀ p q, CrossEdge F p q → η ≤ delta θ (p, q))
    (θ θ' : Fin n → ℝ) (hθ : θ ∈ C) (hθ' : θ' ∈ C) :
    kappaStarZ cycles η * lam * quotNorm F (θ - θ') ^ 2 ≤
      dotProduct (necklaceGradient F θ - necklaceGradient F θ') (θ - θ') := by
  sorry

/-- **The inverse-Lipschitz bound** `eq:sharp-inverse-lipschitz`: on a convex angular-margin chamber,
`‖[θ] − [θ']‖_quot ≤ ‖G_f(θ) − G_f(θ')‖₂ / (κ*_{f,Z}(η) λ_f⁺)`. -/
theorem sharp_inverse_lipschitz (F : LooplessBAP n) (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F))
    (η : ℝ) (hη : 0 < η) (hηZ : ∀ c ∈ cycles, η ≤ Real.pi / c.length)
    (lam : ℝ) (hlam : IsLeast {μ : ℝ | μ ∈ spectrum ℝ (graphLaplacian F) ∧ 0 < μ} lam)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hδ : ∀ θ ∈ C, ∀ p q, CrossEdge F p q → η ≤ delta θ (p, q))
    (θ θ' : Fin n → ℝ) (hθ : θ ∈ C) (hθ' : θ' ∈ C) :
    quotNorm F (θ - θ') ≤
      euclidNorm (necklaceGradient F θ - necklaceGradient F θ') / (kappaStarZ cycles η * lam) := by
  sorry

end Conj43
