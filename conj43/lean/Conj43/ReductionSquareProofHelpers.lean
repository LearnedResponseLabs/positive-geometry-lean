/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.Reduction
namespace Conj43.Reduction

/-- The subtype of a product cut out by coordinate predicates is the product of subtypes. -/
def subtypePiHomeomorph {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    (P : ∀ i, A i → Prop) :
    {x : ∀ i, A i // ∀ i, P i (x i)} ≃ₜ (∀ i, {x : A i // P i x}) where
  toEquiv := Equiv.subtypePiEquivPi
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))

/-- A product map on nonempty factors is a homeomorphism exactly when all factors are.
No continuity of the factor maps is assumed. It is recovered using coordinate sections. -/
theorem pi_homeomorphism_iff {ι : Type*} {A B : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    (x0 : ∀ i, A i) (f : ∀ i, A i → B i) :
    (∃ e : (∀ i, A i) ≃ₜ (∀ i, B i), ∀ x, e x = fun i => f i (x i)) ↔
      ∀ i, ∃ e : A i ≃ₜ B i, ∀ x, e x = f i x := by
  classical
  constructor
  · rintro ⟨H,hH⟩ i
    have hf : Function.Injective (f i) := by
      intro a b hab
      have hprod : H (Function.update x0 i a) = H (Function.update x0 i b) := by
        rw [hH,hH]
        funext j
        by_cases hji : j=i
        · subst j; simpa only [Function.update_self] using hab
        · simp only [Function.update_of_ne hji]
      have h := congrFun (H.injective hprod) i
      simpa only [Function.update_self] using h
    let g : B i → A i := fun y => H.symm (Function.update (H x0) i y) i
    have hright (y : B i) : f i (g y) = y := by
      have h := congrFun (H.apply_symm_apply (Function.update (H x0) i y)) i
      rw [hH] at h
      simpa only [Function.update_self] using h
    have hcont : Continuous (f i) := by
      have he : f i = fun x => H (Function.update x0 i x) i := by
        funext x
        rw [hH]
        simp only [Function.update_self]
      rw [he]
      exact (continuous_apply i).comp (H.continuous.comp (continuous_const.update i continuous_id))
    refine ⟨{ toFun := f i
              invFun := g
              left_inv := fun x => hf (hright (f i x))
              right_inv := hright
              continuous_toFun := hcont
              continuous_invFun := (continuous_apply i).comp
                (H.symm.continuous.comp (continuous_const.update i continuous_id)) }, fun _ => rfl⟩
  · intro h
    choose e he using h
    exact ⟨Homeomorph.piCongrRight e, fun x => funext (fun i => he i (x i))⟩

end Conj43.Reduction
