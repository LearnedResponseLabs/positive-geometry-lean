import Conj43.L5Statements

/-! Calculus of the integral potential in the original real coordinates. -/
namespace Conj43
open scoped BigOperators
open ContinuousLinearMap
variable {n : ℕ}

/-- Normalization at the midpoint avoids endpoint integrability issues. -/
noncomputable def logSinPrimitive (u : ℝ) : ℝ :=
  ∫ t in (Real.pi / 2)..u, Real.log (Real.sin t)

/-- The potential, with each directed crossing counted once. -/
noncomputable def potential (F : LooplessBAP n) (θ : Fin n → ℝ) : ℝ :=
  ∑ j : EdgeIdx F, logSinPrimitive (delta θ (edgeOf F j))

/-- The gradient vector in the original coordinates. -/
noncomputable def gradientMap (F : LooplessBAP n) (θ : Fin n → ℝ) : Fin n → ℝ :=
  (realB F).mulVec (fun j => Real.log (Real.sin (delta θ (edgeOf F j))))

/-- Pairing with a vector, in the product norm on the coordinate space. -/
noncomputable def coordinatePairing (v : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ r, v r • proj (R := ℝ) (φ := fun _ : Fin n => ℝ) r

/-- A matrix acts as a continuous linear map in the product norm. -/
noncomputable def matrixCLM (M : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun r => coordinatePairing (M r))

theorem primitive_strict_core (u : ℝ) (hu : 0 < u) (huπ : u < Real.pi) :
    HasStrictDerivAt logSinPrimitive (Real.log (Real.sin u)) u := by
  have hc : ContinuousOn (fun t => Real.log (Real.sin t)) (Set.uIcc (Real.pi / 2) u) := by
    apply Real.continuous_sin.continuousOn.log
    intro t ht
    apply ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · have := (Set.mem_Icc.mp ht).1
      exact lt_of_lt_of_le (lt_min (by positivity) hu) this
    · have := (Set.mem_Icc.mp ht).2
      exact lt_of_le_of_lt this (max_lt (by linarith [Real.pi_pos]) huπ)
  apply intervalIntegral.integral_hasStrictDerivAt_right (hc.intervalIntegrable) ?_ ?_
  · exact (Real.measurable_log.comp Real.continuous_sin.measurable).stronglyMeasurable.stronglyMeasurableAtFilter
  · exact Real.continuous_sin.continuousAt.log (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hu huπ))

private theorem delta_strict (θ : Fin n → ℝ) (e : Fin n × Fin n) :
    HasStrictFDerivAt (fun x => delta x e) (proj (R := ℝ) (φ := fun _ : Fin n => ℝ) e.2 - proj (R := ℝ) (φ := fun _ : Fin n => ℝ) e.1 : (Fin n → ℝ) →L[ℝ] ℝ) θ := by
  exact ((hasStrictFDerivAt_apply e.2 θ).sub (hasStrictFDerivAt_apply e.1 θ)).add_const _

private theorem edge_admissible (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) (j : EdgeIdx F) :
    0 < delta θ (edgeOf F j) ∧ delta θ (edgeOf F j) < Real.pi :=
  hθ _ _ ((l5_mem_crossEdges F _ _).mp (List.get_mem _ j))

private theorem pairing_eq (F : LooplessBAP n) (v : EdgeIdx F → ℝ) :
    coordinatePairing ((realB F).mulVec v) =
      ∑ j, v j • (proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (edgeOf F j).2 - proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (edgeOf F j).1 : (Fin n → ℝ) →L[ℝ] ℝ) := by
  ext h
  simp only [coordinatePairing, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
  change dotProduct ((realB F).mulVec v) h = _
  rw [dotProduct_comm, Matrix.dotProduct_mulVec]
  simp only [dotProduct, realB_vecMul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Strict derivative, hence also the ordinary derivative, of the potential. -/
theorem potential_strict_core (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) :
    HasStrictFDerivAt (potential F) (coordinatePairing (gradientMap F θ)) θ := by
  unfold gradientMap
  rw [pairing_eq]
  apply HasStrictFDerivAt.fun_sum
  intro j _
  exact (primitive_strict_core _ (edge_admissible F θ hθ j).1
    (edge_admissible F θ hθ j).2).comp_hasStrictFDerivAt θ (delta_strict θ _)

private theorem logSin_strict (u : ℝ) (hu : 0 < u) (huπ : u < Real.pi) :
    HasStrictDerivAt (fun t => Real.log (Real.sin t)) (Real.cot u) u := by
  simpa only [Real.cot_eq_cos_div_sin] using
    (Real.hasStrictDerivAt_sin u).log (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hu huπ))

private theorem hessian_clm_eq (F : LooplessBAP n) (θ : Fin n → ℝ) :
    matrixCLM (hessianMatrix F θ) = ContinuousLinearMap.pi (fun r =>
      ∑ j, (realB F r j) • (Real.cot (delta θ (edgeOf F j)) •
        (proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (edgeOf F j).2 - proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (edgeOf F j).1 : (Fin n → ℝ) →L[ℝ] ℝ))) := by
  ext h r
  simp only [matrixCLM, coordinatePairing, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  change (hessianMatrix F θ).mulVec h r = _
  unfold hessianMatrix
  have ht : (realB F).transpose.mulVec h = Matrix.vecMul h (realB F) := by
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ht]
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal, Matrix.of_apply, realB_vecMul,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The strict derivative of the gradient is the layer-5 Hessian matrix. -/
theorem gradient_strict_core (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) :
    HasStrictFDerivAt (gradientMap F) (matrixCLM (hessianMatrix F θ)) θ := by
  rw [hessian_clm_eq]
  apply hasStrictFDerivAt_pi.mpr
  intro r
  unfold gradientMap Matrix.mulVec dotProduct
  apply HasStrictFDerivAt.fun_sum
  intro j _
  exact ((logSin_strict _ (edge_admissible F θ hθ j).1
    (edge_admissible F θ hθ j).2).comp_hasStrictFDerivAt θ
      (delta_strict θ _)).const_mul (realB F r j)

/-- The admissible chamber is open in the full coordinate space. -/
theorem admissible_open_core (F : LooplessBAP n) : IsOpen {θ | Admissible F θ} := by
  classical
  simp only [Admissible, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro p
  apply isOpen_iInter_of_finite
  intro q
  apply isOpen_iInter_of_finite
  intro _
  have hc : Continuous (fun θ : Fin n → ℝ => delta θ (p, q)) := by
    unfold delta; fun_prop
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

end Conj43
