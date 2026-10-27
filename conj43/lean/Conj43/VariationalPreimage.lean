/-
Conj43/VariationalPreimage.lean — inverting the gradient is minimizing (reading-edition corollary of S59 and S60,
added at the author's request on 2026-10-22).

For a target `y` in the image of the gradient on the slice `θ_p = a_p` at the component anchors, exactly one point of
the slice has gradient `y`, and that point is the unique minimizer of `Ψ(z) − y·z` over the slice (the paper's
Corollary 31 when `a = 0`). Both parts come from `potential_variational_inverse` (S59): every point `x` of the slice
minimizes `Ψ(z) − G(x)·z`, with equality only at `x`. So two preimages of `y` minimize the same function and coincide,
and any minimizer equals the preimage. The statement uses the frozen definitions of `variational_image_minimizer` (S60)
verbatim.
-/
import Conj43.L6Statements

namespace Conj43

variable {n : ℕ}

/-- **Inverting the gradient is minimizing.** Every `y` in the gradient image of the slice has exactly one preimage
in the slice, and that preimage is the unique minimizer of `Ψ(z) − y·z` there. -/
theorem variational_gradient_preimage (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∀ y ∈ G '' S, (∃! x, x ∈ S ∧ G x = y) ∧
      ∀ x ∈ S, G x = y →
        (∀ z ∈ S, Ψ x - dotProduct y x ≤ Ψ z - dotProduct y z) ∧
        ∀ w ∈ S, (∀ z ∈ S, Ψ w - dotProduct y w ≤ Ψ z - dotProduct y z) → w = x := by
  intro δ Ψ G S y hy
  obtain ⟨x₀, hx₀, rfl⟩ := hy
  have hv := potential_variational_inverse F a
  -- S59's equality case: a minimizer of `Ψ(z) − G(x)·z` on the slice is `x` itself.
  have key : ∀ x ∈ S, ∀ w ∈ S, (∀ z ∈ S, Ψ w - dotProduct (G x) w ≤ Ψ z - dotProduct (G x) z) → w = x :=
    fun x hx w hw hmin => ((hv x hx w hw).2).1 (le_antisymm (hmin x hx) (hv x hx w hw).1)
  refine ⟨⟨x₀, ⟨hx₀, rfl⟩, ?_⟩, ?_⟩
  · -- a second preimage `x` minimizes `Ψ(z) − G(x)·z = Ψ(z) − G(x₀)·z`, so it is `x₀`
    rintro x ⟨hx, hGx⟩
    refine key x₀ hx₀ x hx fun z hz => ?_
    rw [← hGx]
    exact (hv x hx z hz).1
  · intro x hx hGx
    refine ⟨fun z hz => ?_, fun w hw hmin => ?_⟩
    · rw [← hGx]
      exact (hv x hx z hz).1
    · rw [← hGx] at hmin
      exact key x hx w hw hmin

end Conj43

#print axioms Conj43.variational_gradient_preimage
