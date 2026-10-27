import Conj43.L5Defs

/-! The complex bracket and its norm on the admissible chamber. -/
namespace Conj43
variable {n : ℕ}

theorem angleParameter_ne_zero (θ : Fin n → ℝ) (j : Fin n) :
    angleParameter θ j ≠ 0 := Complex.exp_ne_zero _

theorem bracket_angleParameter (θ : Fin n → ℝ) (p q : Fin n) :
    bracket (angleParameter θ q) (angleParameter θ p) =
      2 * (Real.sin (θ q - θ p) : ℂ) * Complex.I := by
  unfold bracket angleParameter
  rw [← Complex.exp_sub, ← Complex.exp_sub]
  have h₁ : Complex.I * (θ q : ℂ) - Complex.I * (θ p : ℂ) =
      ((θ q - θ p : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have h₂ : Complex.I * (θ p : ℂ) - Complex.I * (θ q : ℂ) =
      ((-(θ q - θ p) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h₁, h₂, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem bracket_angleParameter_norm (θ : Fin n → ℝ) (p q : Fin n) :
    ‖bracket (angleParameter θ q) (angleParameter θ p)‖ =
      2 * |Real.sin (θ q - θ p)| := by
  rw [bracket_angleParameter]
  rw [norm_mul, norm_mul]
  norm_num only [Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- Symmetrizing the labels does not change the bracket norm. -/
theorem bracketPlus_norm (t : Fin n → ℂ) (p q : Fin n) :
    ‖bracketPlus t q p‖ = ‖bracket (t q) (t p)‖ := by
  unfold bracketPlus
  split
  · have h : bracket (t p) (t q) = -bracket (t q) (t p) := by
      unfold bracket; ring
    rw [h, norm_neg]
  · rfl

/-- The hinge identity, including both orientations and the wrapped case. -/
theorem hinge_identity_core (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) (p q : Fin n) (he : CrossEdge F p q) :
    ‖bracketPlus (angleParameter θ) q p‖ = 2 * Real.sin (delta θ (p, q)) := by
  rw [bracketPlus_norm, bracket_angleParameter_norm]
  have hs : 0 ≤ Real.sin (delta θ (p, q)) :=
    (Real.sin_pos_of_pos_of_lt_pi (hθ p q he).1 (hθ p q he).2).le
  have habs : |Real.sin (θ q - θ p)| = |Real.sin (delta θ (p, q))| := by
    by_cases h : q < p
    · simp [delta, h, Real.sin_add_pi]
    · simp [delta, h]
  rw [habs, abs_of_nonneg hs]

end Conj43
