/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionConnected
namespace Conj43
namespace Reduction
variable {n : ℕ}

lemma restrict_anchor_iff (F : LooplessBAP n) (p : Fin n) (hp : IsAnchor F p)
    (i : Fin (component F p).card) :
    IsAnchor (restrictBAP F p) i ↔ labelsOf (component F p) i = p := by
  constructor
  · intro hi
    obtain ⟨j,hj⟩ := reduction_labels_surj (component F p) (reduction_self_mem F p)
    apply le_antisymm
    · have h := (labelsOf (component F p)).monotone (hi j (restrict_connected F p i j))
      simpa only [hj] using h
    · exact hp _ ((mem_component_iff F p _).mp (reduction_labels_mem _ i))
  · intro hi j _
    apply (labelsOf (component F p)).le_iff_le.mp
    rw [hi]
    exact hp _ ((mem_component_iff F p _).mp (reduction_labels_mem _ j))

/-- Each label has one component anchor and one increasing-enumeration index. -/
lemma label_index_bijective (F : LooplessBAP n) :
    Function.Bijective (fun z : (p : {p : Fin n // IsAnchor F p}) × Fin (component F p.val).card =>
      labelsOf (component F z.1.val) z.2) := by
  constructor
  · rintro ⟨p,i⟩ ⟨q,j⟩ h
    change labelsOf (component F p.val) i = labelsOf (component F q.val) j at h
    have hpi := (mem_component_iff F p.val _).mp (reduction_labels_mem _ i)
    have hqj := (mem_component_iff F q.val _).mp (reduction_labels_mem _ j)
    have hpi2 : SameComponent F p.val (labelsOf (component F q.val) j) := h ▸ hpi
    have hpq : p = q := Subtype.ext (anchor_unique F p.property q.property
      (hpi2.trans (reduction_same_symm F hqj)))
    subst q
    have hij : i=j := (labelsOf (component F p.val)).injective h
    subst j
    rfl
  · intro q
    obtain ⟨p,hqp,hp⟩ := anchor_exists F q
    obtain ⟨i,hi⟩ := reduction_labels_surj (component F p)
      ((mem_component_iff F p q).mpr (reduction_same_symm F hqp))
    exact ⟨⟨⟨p,hp⟩,i⟩,hi⟩

noncomputable def labelIndex (F : LooplessBAP n) :
    ((p : {p : Fin n // IsAnchor F p}) × Fin (component F p.val).card) ≃ Fin n :=
  Equiv.ofBijective _ (label_index_bijective F)

/-- A permutation of coordinates, curried by the component anchor. -/
noncomputable def ambientHomeomorph (F : LooplessBAP n) :
    (Fin n → ℝ) ≃ₜ ((p : {p : Fin n // IsAnchor F p}) → Fin (component F p.val).card → ℝ) where
  toFun θ p j := θ (labelsOf (component F p.val) j)
  invFun x q := x ((labelIndex F).symm q).1 ((labelIndex F).symm q).2
  left_inv θ := by
    funext q
    exact congrArg θ ((labelIndex F).apply_symm_apply q)
  right_inv x := by
    funext p j
    exact congrArg (fun z => x z.1 z.2) ((labelIndex F).symm_apply_apply ⟨p,j⟩)
  continuous_toFun := continuous_pi (fun _ => continuous_pi (fun _ => continuous_apply _))
  continuous_invFun := continuous_pi (fun _ => (continuous_apply _).comp (continuous_apply _))

lemma slice_membership (F : LooplessBAP n) (a θ : Fin n → ℝ) :
    θ ∈ gaugeSlice F a ↔
      ∀ p : {p : Fin n // IsAnchor F p},
        (ambientHomeomorph F θ) p ∈ gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a) := by
  constructor
  · intro h p
    refine ⟨(admissible_iff_components F θ).mp h.1 p.val p.property, ?_⟩
    intro i hi
    have he := (restrict_anchor_iff F p.val p.property i).mp hi
    change θ (labelsOf (component F p.val) i) = a (labelsOf (component F p.val) i)
    rw [he]
    exact h.2 p.val p.property
  · intro h
    refine ⟨(admissible_iff_components F θ).mpr (fun p hp => (h ⟨p,hp⟩).1), ?_⟩
    intro p hp
    obtain ⟨i,hi⟩ := reduction_labels_surj (component F p) (reduction_self_mem F p)
    have he := (h ⟨p,hp⟩).2 i ((restrict_anchor_iff F p hp i).mpr hi)
    change θ (labelsOf (component F p) i) = a (labelsOf (component F p) i) at he
    simpa only [hi] using he

end Reduction

theorem slice_homeomorph_components (F : LooplessBAP n) (a : Fin n → ℝ) :
    ∃ e : gaugeSlice F a ≃ₜ
        {x : (p : {p : Fin n // IsAnchor F p}) → (Fin (component F p.val).card → ℝ) |
          ∀ p, x p ∈ gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a)},
      ∀ θ p, (e θ).val p = restrictAngles F p.val θ.val := by
  refine ⟨(Reduction.ambientHomeomorph F).subtype (Reduction.slice_membership F a), ?_⟩
  intro θ p
  rfl

end Conj43
