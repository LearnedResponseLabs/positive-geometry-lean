/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionSquareProofHelpers
import Conj43.L7Statements
namespace Conj43
variable {n : ℕ}

theorem reduction_homeomorphism_iff (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} [TopologicalSpace X] (Crit : Set X) (Meas : gaugeSlice F a → Crit)
    {Y : {p : Fin n // IsAnchor F p} → Type*} [∀ p, TopologicalSpace (Y p)] (CritC : ∀ p, Set (Y p))
    (MeasC : ∀ p, gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a) → CritC p)
    (Sig : Crit ≃ₜ ((p : {p : Fin n // IsAnchor F p}) → CritC p))
    (hsq : ∀ θ p (h : restrictAngles F p.val θ.val ∈ gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a)),
      Sig (Meas θ) p = MeasC p ⟨restrictAngles F p.val θ.val, h⟩) :
    (∃ e : gaugeSlice F a ≃ₜ Crit, ∀ θ, e θ = Meas θ) ↔
      ∀ p, ∃ e : gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a) ≃ₜ CritC p,
        ∀ θ, e θ = MeasC p θ := by
  classical
  obtain ⟨rho,hrho⟩ := slice_homeomorph_components F a
  let R : gaugeSlice F a ≃ₜ
      ((p : {p : Fin n // IsAnchor F p}) → gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a)) :=
    rho.trans (Reduction.subtypePiHomeomorph (fun (p : {p : Fin n // IsAnchor F p}) (x : Fin (component F p.val).card → ℝ) =>
      x ∈ gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a)))
  have hR (θ : gaugeSlice F a) (p : {p : Fin n // IsAnchor F p}) :
      (R θ p).val = restrictAngles F p.val θ.val := hrho θ p
  have square (θ : gaugeSlice F a) : Sig (Meas θ) = fun p => MeasC p (R θ p) := by
    funext p
    have hp : restrictAngles F p.val θ.val ∈ gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a) := by
      rw [← hR θ p]
      exact (R θ p).property
    rw [hsq θ p hp]
    exact congrArg (MeasC p) (Subtype.ext (hR θ p).symm)
  let x0 : (p : {p : Fin n // IsAnchor F p}) → gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a) :=
    fun p => ⟨(gauge_slice_nonempty (restrictBAP F p.val) (restrictAngles F p.val a)).choose,
      (gauge_slice_nonempty (restrictBAP F p.val) (restrictAngles F p.val a)).choose_spec⟩
  constructor
  · rintro ⟨e,he⟩
    apply (Reduction.pi_homeomorphism_iff x0 MeasC).mp
    refine ⟨R.symm.trans (e.trans Sig), ?_⟩
    intro x
    change Sig (e (R.symm x)) = _
    rw [he, square, R.apply_symm_apply]
  · intro h
    obtain ⟨H,hH⟩ := (Reduction.pi_homeomorphism_iff x0 MeasC).mpr h
    refine ⟨R.trans (H.trans Sig.symm), ?_⟩
    intro θ
    apply Sig.injective
    change Sig (Sig.symm (H (R θ))) = Sig (Meas θ)
    rw [Sig.apply_symm_apply, hH]
    exact (square θ).symm

end Conj43
