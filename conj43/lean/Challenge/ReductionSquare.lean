/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionDefs

/-! ### Group `reduction_square`: the second half of the paper's Lemma 5(2), in conditional form

Frozen on 2026-10-26, before any proof. Lean constructs neither measurement map nor critical cell. The hypotheses
`Sig` and `hsq` stand for Galashin's Proposition 4.10, whose proof gives a homeomorphism of the critical cell onto the
product of the components' critical cells that intertwines the measurement maps (the paper's square (16)). Given them,
the measurement map of `f` is a homeomorphism exactly when every component's is (the paper's sentence after Remark 6).
No continuity of `Meas` or `MeasC` is assumed. -/

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
  sorry

end Conj43
