import Conj43.Hessian
import Conj43.Hinge

/-! Exported signatures copied verbatim from the frozen L5 challenge. -/
namespace Conj43
variable {n : ℕ}

theorem cycle_wrap_sum (c : List (Fin n)) (hlen : 3 ≤ c.length)
    (hw : winding c = n) :
    ((cycleEdges c).map fun e => if e.2 < e.1 then (1 : ℝ) else 0).sum = 1 := by
  exact cycle_wrap_sum_core c hlen hw

theorem delta_cycle_sum (θ : Fin n → ℝ) (c : List (Fin n))
    (hlen : 3 ≤ c.length) (_hnodup : c.Nodup) (hw : winding c = n) :
    ((cycleEdges c).map fun e =>
      θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)).sum = Real.pi := by
  exact delta_cycle_sum_core θ c hlen _hnodup hw

theorem hessian_psd (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : ∀ p q, CrossEdge F p q →
      let d := θ q - θ p + Real.pi * (if q < p then 1 else 0)
      0 < d ∧ d < Real.pi) (h : Fin n → ℝ) :
    let Q := ((crossEdges F).map fun e =>
      Real.cot (θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) *
        (h e.2 - h e.1)^2).sum
    0 ≤ Q ∧ (Q = 0 ↔ ∀ p q, CrossEdge F p q → h p = h q) := by
  exact hessian_psd_core F θ hθ h

theorem hessian_kernel_components (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : ∀ p q, CrossEdge F p q →
      let d := θ q - θ p + Real.pi * (if q < p then 1 else 0)
      0 < d ∧ d < Real.pi) (h : Fin n → ℝ) :
    ((crossEdges F).map fun e =>
      Real.cot (θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) *
        (h e.2 - h e.1)^2).sum = 0 ↔
    ∀ p q, Relation.ReflTransGen (fun a b => CrossEdge F a b ∨ CrossEdge F b a) p q →
      h p = h q := by
  exact hessian_kernel_components_core F θ hθ h

theorem hessian_matrix_form (F : LooplessBAP n) (θ h : Fin n → ℝ) :
    let B : Matrix (Fin n) (EdgeIdx F) ℝ := fun r j => (Bmat F r j : ℝ)
    let w := fun j => Real.cot (θ (edgeOf F j).2 - θ (edgeOf F j).1 +
      Real.pi * (if (edgeOf F j).2 < (edgeOf F j).1 then 1 else 0))
    dotProduct h ((B * Matrix.diagonal w * B.transpose).mulVec h) =
      ((crossEdges F).map fun e =>
        Real.cot (θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) *
          (h e.2 - h e.1)^2).sum := by
  exact hessian_matrix_form_core F θ h

theorem hessian_matrix_kernel (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : ∀ p q, CrossEdge F p q →
      let d := θ q - θ p + Real.pi * (if q < p then 1 else 0)
      0 < d ∧ d < Real.pi) (h : Fin n → ℝ) :
    let B : Matrix (Fin n) (EdgeIdx F) ℝ := fun r j => (Bmat F r j : ℝ)
    let w := fun j => Real.cot (θ (edgeOf F j).2 - θ (edgeOf F j).1 +
      Real.pi * (if (edgeOf F j).2 < (edgeOf F j).1 then 1 else 0))
    (B * Matrix.diagonal w * B.transpose).mulVec h = 0 ↔
      ∀ p q, Relation.ReflTransGen (fun a b => CrossEdge F a b ∨ CrossEdge F b a) p q →
        h p = h q := by
  exact hessian_matrix_kernel_core F θ hθ h

theorem hinge_identity (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : ∀ p q, CrossEdge F p q →
      let d := θ q - θ p + Real.pi * (if q < p then 1 else 0)
      0 < d ∧ d < Real.pi) (p q : Fin n) (he : CrossEdge F p q) :
    let t := fun j => Complex.exp (Complex.I * (θ j : ℂ))
    ‖(if q < p then t p / t q - t q / t p else t q / t p - t p / t q)‖ =
      2 * Real.sin (θ q - θ p + Real.pi * (if q < p then 1 else 0)) := by
  exact hinge_identity_core F θ hθ p q he

end Conj43
