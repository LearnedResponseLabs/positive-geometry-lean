/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsLipschitzCalculus
import Conj43.ExtensionsLipschitzPositive

noncomputable section
namespace Conj43
variable {n : ℕ}

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
  have hk := extensions_lipschitz_kappa_pos F cycles hc hp η hη hηZ lam hlam
  have hs := mul_le_mul_of_nonneg_left
    (extensions_lipschitz_spectral_gap F lam hlam (θ-θ')) hk.le
  rw [← mul_assoc] at hs
  exact hs.trans (extensions_lipschitz_graph_monotone F cycles hc hp η hη hηZ C hC hδ θ θ' hθ hθ')

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
  have hk := extensions_lipschitz_kappa_pos F cycles hc hp η hη hηZ lam hlam
  have ha : 0 < kappaStarZ cycles η * lam := mul_pos hk hlam.1.2
  have hq := extensions_lipschitz_quot_nonneg F (θ-θ')
  have hg := extensions_lipschitz_euclid_nonneg (necklaceGradient F θ - necklaceGradient F θ')
  have hm := sharp_strong_monotone F cycles hc hp η hη hηZ lam hlam C hC hδ θ θ' hθ hθ'
  have hs := extensions_lipschitz_quot_cs F θ θ' (θ-θ')
  apply (le_div_iff₀ ha).mpr
  by_cases hz : quotNorm F (θ-θ') = 0
  · simpa [hz] using hg
  · have hqp : 0 < quotNorm F (θ-θ') := lt_of_le_of_ne hq (Ne.symm hz)
    have hh := hm.trans hs
    have hh' : (kappaStarZ cycles η * lam * quotNorm F (θ-θ')) * quotNorm F (θ-θ') ≤
        euclidNorm (necklaceGradient F θ - necklaceGradient F θ') * quotNorm F (θ-θ') := by
      nlinarith only [hh]
    have hr := le_of_mul_le_mul_right hh' hqp
    simpa only [mul_comm] using hr

end Conj43
