import Conj43.L6Topology

/-! Identification of the tangent gradient coordinates with the incidence range. -/
namespace Conj43
variable {n : ℕ}

/-- The literal image of the real incidence matrix, with its subspace topology. -/
noncomputable def incidenceRange (F : LooplessBAP n) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.range (Matrix.toLin' (realB F))

private theorem component_symm (F : LooplessBAP n) {p q : Fin n} (h : SameComponent F p q) :
    SameComponent F q p := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head h _ ih => exact ih.trans (.single h.symm)

private noncomputable def representative (F : LooplessBAP n) (p : Fin n) : Fin n :=
  Classical.choose (anchor_exists_core F p)

private theorem representative_spec (F : LooplessBAP n) (p : Fin n) :
    SameComponent F p (representative F p) ∧ IsGaugeAnchor F (representative F p) :=
  Classical.choose_spec (anchor_exists_core F p)

private theorem representative_same (F : LooplessBAP n) {p q : Fin n} (h : SameComponent F p q) :
    representative F p = representative F q :=
  anchor_unique_core F _ _ (representative_spec F p).2 (representative_spec F q).2
    ((component_symm F (representative_spec F p).1).trans (h.trans (representative_spec F q).1))

/-- Deleting anchor coordinates is injective on the incidence image. -/
theorem incidence_projection_injective_core (F : LooplessBAP n) :
    Function.Injective ((gaugeProjection F).comp (incidenceRange F).subtypeL) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Subtype.ext
  apply dotProduct_self_eq_zero.mp
  obtain ⟨w, hw⟩ := v.property
  change (realB F).mulVec w = (v : Fin n → ℝ) at hw
  let s : Fin n → ℝ := fun p => v.val (representative F p)
  have hs : ∀ p q, SameComponent F p q → s p = s q := by
    intro p q hpq
    exact congrArg (fun r => v.val r) (representative_same F hpq)
  have hz : Matrix.vecMul s (realB F) = 0 := by
    funext j
    rw [realB_vecMul]
    exact sub_eq_zero.mpr (hs _ _ (.single (Or.inl
      ((l5_mem_crossEdges F _ _).mp (List.get_mem _ j))))).symm
  have hdot : dotProduct s (v : Fin n → ℝ) = 0 := by
    rw [← hw, Matrix.dotProduct_mulVec, hz, zero_dotProduct]
  have heq : dotProduct s (v : Fin n → ℝ) = dotProduct (v : Fin n → ℝ) (v : Fin n → ℝ) := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : IsGaugeAnchor F p
    · have hr : representative F p = p :=
        (anchor_unique_core F p _ hp (representative_spec F p).2 (representative_spec F p).1).symm
      simp [s, hr]
    · have hzero := congrArg (fun u : gaugeTangent F => (u : Fin n → ℝ) p) hv
      have hzero' : v.val p = 0 := by simpa [gaugeProjection, hp] using hzero
      simp [hzero']
  exact heq.symm.trans hdot

/-- At an admissible point, the projected Hessian realizes surjectivity onto tangent coordinates. -/
theorem incidence_projection_surjective_core (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) :
    Function.Surjective ((gaugeProjection F).comp (incidenceRange F).subtypeL) := by
  let D := (gaugeProjection F).comp ((matrixCLM (hessianMatrix F θ)).comp (gaugeTangent F).subtypeL)
  have hi : Function.Injective D := reduced_derivative_injective F θ hθ
  have hs : Function.Surjective D := LinearMap.injective_iff_surjective.mp hi
  intro y
  obtain ⟨h, hh⟩ := hs y
  have hm : matrixCLM (hessianMatrix F θ) h = (hessianMatrix F θ).mulVec h := by
    ext r
    simp [matrixCLM, coordinatePairing, Matrix.mulVec, dotProduct]
  have hmem : (hessianMatrix F θ).mulVec h ∈ incidenceRange F := by
    refine ⟨(Matrix.diagonal (fun j => Real.cot (delta θ (edgeOf F j))) * (realB F).transpose).mulVec h, ?_⟩
    change (realB F).mulVec _ = _
    rw [Matrix.mulVec_mulVec]
    simp [hessianMatrix, Matrix.mul_assoc]
  refine ⟨⟨(hessianMatrix F θ).mulVec h, hmem⟩, ?_⟩
  change gaugeProjection F ((hessianMatrix F θ).mulVec h) = y
  change gaugeProjection F (matrixCLM (hessianMatrix F θ) h) = y at hh
  rwa [hm] at hh

private theorem gradient_mem_range (F : LooplessBAP n) (θ : Fin n → ℝ) :
    gradientMap F θ ∈ incidenceRange F :=
  ⟨fun j => Real.log (Real.sin (delta θ (edgeOf F j))), rfl⟩

/-- The unprojected gradient is an open embedding into the literal incidence range. -/
theorem gradient_range_openEmbedding_core (F : LooplessBAP n) (a : Fin n → ℝ) :
    ∃ g : GaugeSlice F a → incidenceRange F,
      (∀ θ, (g θ).val = gradientMap F θ.val) ∧ Topology.IsOpenEmbedding g := by
  let g : GaugeSlice F a → incidenceRange F := fun θ => ⟨gradientMap F θ.val, gradient_mem_range F θ.val⟩
  refine ⟨g, (fun _ => rfl), ?_⟩
  by_cases h : Nonempty (GaugeSlice F a)
  · let θ := Classical.choice h
    let P := (gaugeProjection F).comp (incidenceRange F).subtypeL
    let e : incidenceRange F ≃L[ℝ] gaugeTangent F :=
      (LinearEquiv.ofBijective P.toLinearMap ⟨incidence_projection_injective_core F,
        incidence_projection_surjective_core F θ.val θ.property.1⟩).toContinuousLinearEquiv
    have he := (reducedGradient_embedding_core F a).comp (sliceChart F a).isOpenEmbedding
    have he' : Topology.IsOpenEmbedding (e ∘ g) := by
      simpa [e, P, g, Function.comp_def, reducedGradient, sliceChart] using he
    exact e.toHomeomorph.isOpenEmbedding.of_comp g he'
  · letI : IsEmpty (GaugeSlice F a) := not_nonempty_iff.mp h
    exact Topology.IsOpenEmbedding.of_isEmpty g

end Conj43
