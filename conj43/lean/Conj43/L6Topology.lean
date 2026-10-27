import Conj43.L6Slice

/-! Local inversion in the tangent coordinates of the gauge plane. -/
namespace Conj43
open scoped Topology
variable {n : ℕ}

/-- Delete the anchor coordinates, viewed as a projection onto the gauge tangent space. -/
noncomputable def gaugeProjection (F : LooplessBAP n) : (Fin n → ℝ) →L[ℝ] gaugeTangent F := by
  classical
  exact LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨fun p => if IsGaugeAnchor F p then 0 else v p, by
        intro p hp; simp [hp]⟩
      map_add' := by intros; ext p; by_cases hp : IsGaugeAnchor F p <;> simp [hp]
      map_smul' := by intros; ext p; by_cases hp : IsGaugeAnchor F p <;> simp [hp] }

private theorem projection_pair (F : LooplessBAP n) (h : gaugeTangent F) (v : Fin n → ℝ) :
    dotProduct (h : Fin n → ℝ) (gaugeProjection F v : Fin n → ℝ) = dotProduct (h : Fin n → ℝ) v := by
  classical
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : IsGaugeAnchor F p
  · simp [gaugeProjection, h.property p hp]
  · simp [gaugeProjection, hp]

/-- The slice written as an open subset of its tangent space, based at the prescribed vector. -/
def GaugeDomain (F : LooplessBAP n) (a : Fin n → ℝ) : Set (gaugeTangent F) :=
  {h | Admissible F (a + h)}

/-- Gradient coordinates after deleting the fixed labels. The codomain is the tangent space. -/
noncomputable def reducedGradient (F : LooplessBAP n) (a : Fin n → ℝ)
    (h : gaugeTangent F) : gaugeTangent F :=
  gaugeProjection F (gradientMap F (a + h))

private theorem domain_open (F : LooplessBAP n) (a : Fin n → ℝ) : IsOpen (GaugeDomain F a) :=
  (admissible_open_core F).preimage (continuous_const.add continuous_subtype_val)

private theorem domain_slice (F : LooplessBAP n) (a : Fin n → ℝ) (h : GaugeDomain F a) :
    a + (h.val : Fin n → ℝ) ∈ GaugeSlice F a := by
  refine ⟨h.property, ?_⟩
  intro p hp
  simp [h.val.property p hp]

private theorem reduced_derivative (F : LooplessBAP n) (a : Fin n → ℝ) (h : GaugeDomain F a) :
    HasStrictFDerivAt (reducedGradient F a)
      ((gaugeProjection F).comp ((matrixCLM (hessianMatrix F (a + h.val))).comp
        (gaugeTangent F).subtypeL)) h.val := by
  exact (gaugeProjection F).hasStrictFDerivAt.comp h.val
    ((gradient_strict_core F _ h.property).comp h.val
      ((gaugeTangent F).subtypeL.hasStrictFDerivAt.const_add a))

theorem reduced_derivative_injective (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) : Function.Injective
      ((gaugeProjection F).comp ((matrixCLM (hessianMatrix F θ)).comp (gaugeTangent F).subtypeL)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro h hh
  apply Subtype.ext
  by_contra hne
  have hpos := tangent_positive_core F θ hθ h h.property hne
  have hpair := projection_pair F h ((hessianMatrix F θ).mulVec h)
  have hm : matrixCLM (hessianMatrix F θ) h = (hessianMatrix F θ).mulVec h := by
    ext r
    simp [matrixCLM, coordinatePairing, Matrix.mulVec, dotProduct]
  change gaugeProjection F (matrixCLM (hessianMatrix F θ) h) = 0 at hh
  rw [hm] at hh
  rw [hh] at hpair
  simp only [ZeroMemClass.coe_zero, dotProduct_zero] at hpair
  rw [hessian_matrix_form_core] at hpair
  linarith

/-- Inverse function theorem in equal-dimensional tangent coordinates. -/
theorem reducedGradient_open_core (F : LooplessBAP n) (a : Fin n → ℝ) :
    IsOpenMap (fun h : GaugeDomain F a => reducedGradient F a h.val) := by
  apply isOpenMap_iff_nhds_le.mpr
  intro h
  let D := (gaugeProjection F).comp ((matrixCLM (hessianMatrix F (a + h.val))).comp
    (gaugeTangent F).subtypeL)
  have hi : Function.Injective D := reduced_derivative_injective F _ h.property
  let e : gaugeTangent F ≃L[ℝ] gaugeTangent F :=
    (LinearEquiv.ofBijective D.toLinearMap ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  have hd : HasStrictFDerivAt (reducedGradient F a) (e : gaugeTangent F →L[ℝ] gaugeTangent F) h.val :=
    reduced_derivative F a h
  have hm := hd.map_nhds_eq_of_equiv
  have hs := (domain_open F a).isOpenEmbedding_subtypeVal.map_nhds_eq h
  rw [← hm, ← hs, Filter.map_map]
  rfl

private theorem reducedGradient_injective (F : LooplessBAP n) (a : Fin n → ℝ) :
    Function.Injective (fun h : GaugeDomain F a => reducedGradient F a h.val) := by
  intro h k heq
  by_contra hne
  have hvne : a + (h.val : Fin n → ℝ) ≠ a + (k.val : Fin n → ℝ) := by
    intro he
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact add_left_cancel he
  have hm := gradient_monotone_core F a _ _ (domain_slice F a h) (domain_slice F a k) hvne
  have he : gaugeProjection F (gradientMap F (a + k.val) - gradientMap F (a + h.val)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr heq.symm
  have hdiff : a + (k.val : Fin n → ℝ) - (a + (h.val : Fin n → ℝ)) =
      ((k.val-h.val : gaugeTangent F) : Fin n → ℝ) := by simp
  rw [hdiff, dotProduct_comm, ← projection_pair F (k.val-h.val), he] at hm
  simp at hm

/-- The reduced gradient is an open embedding into the gauge tangent space. -/
theorem reducedGradient_embedding_core (F : LooplessBAP n) (a : Fin n → ℝ) :
    Topology.IsOpenEmbedding (fun h : GaugeDomain F a => reducedGradient F a h.val) := by
  apply Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨?_, reducedGradient_injective F a, reducedGradient_open_core F a⟩
  apply continuous_iff_continuousAt.mpr
  intro h
  exact (reduced_derivative F a h).continuousAt.comp continuous_subtype_val.continuousAt

/-- Translation identifies the slice with an open subset of its tangent space. -/
noncomputable def sliceChart (F : LooplessBAP n) (a : Fin n → ℝ) :
    GaugeSlice F a ≃ₜ GaugeDomain F a where
  toFun θ := ⟨⟨θ.val - a, by intro p hp; simp [θ.property.2 p hp]⟩, by
    change Admissible F (a + (θ.val - a))
    simpa using θ.property.1⟩
  invFun h := ⟨a + (h.val : Fin n → ℝ), domain_slice F a h⟩
  left_inv θ := by apply Subtype.ext; simp
  right_inv h := by apply Subtype.ext; apply Subtype.ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The original gradient is a topological embedding into the ambient coordinate space.
The open-image assertion above is in the explicitly projected tangent coordinates. -/
theorem gradient_embedding_core (F : LooplessBAP n) (a : Fin n → ℝ) :
    Topology.IsEmbedding (fun θ : GaugeSlice F a => gradientMap F θ.val) := by
  have he := (reducedGradient_embedding_core F a).isEmbedding.comp (sliceChart F a).isEmbedding
  have hc : Continuous (fun θ : GaugeSlice F a => gradientMap F θ.val) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (gradient_strict_core F θ.val θ.property.1).continuousAt.comp continuous_subtype_val.continuousAt
  have he' : Topology.IsEmbedding
      (fun θ : GaugeSlice F a => gaugeProjection F (gradientMap F θ.val)) := by
    simpa [Function.comp_def, reducedGradient, sliceChart] using he
  exact Topology.IsEmbedding.of_comp hc (gaugeProjection F).continuous he'

end Conj43
