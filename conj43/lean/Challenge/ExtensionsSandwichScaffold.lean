/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs

noncomputable section
namespace Conj43
variable {n : ℕ}

theorem sharp_laplacian_sandwich (F : LooplessBAP n) (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F))
    (θ : Fin n → ℝ) (η : ℝ) (hη : 0 < η)
    (hδ : ∀ p q, CrossEdge F p q → η ≤ delta θ (p, q))
    (hηZ : ∀ c ∈ cycles, η ≤ Real.pi / c.length) (h : Fin n → ℝ) :
    kappaStarZ cycles η * dotProduct h ((graphLaplacian F).mulVec h) ≤
        dotProduct h ((hessianMatrix F θ).mulVec h) ∧
      dotProduct h ((hessianMatrix F θ).mulVec h) ≤
        Real.cot η * dotProduct h ((graphLaplacian F).mulVec h) := by
  sorry

end Conj43
