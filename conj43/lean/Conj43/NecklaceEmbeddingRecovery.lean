-- SPDX-License-Identifier: Apache-2.0
import Conj43.NecklaceEmbeddingDefs
import Conj43.L7Log

/-! Positive rescaling and continuous descent of ordinary necklace recovery.
The constant-annihilation result is reused from the accepted layer 7.
-/
namespace Conj43
variable {n : ℕ}

/-- A positive change of representative adds a constant before recovery. -/
theorem ordinary_log_rescale [NeZero n] (F : LooplessBAP n) (v : Fin n → ℝ)
    (hv : ∀ r, 0 < v r) (c : ℝ) (hc : 0 < c) :
    necklaceRecovery F (fun r => Real.log (c * v r)) =
      necklaceRecovery F (fun r => Real.log (v r)) := by
  have heq : (fun r => Real.log (c * v r)) =
      (fun r => Real.log (v r)) + fun _ => Real.log c := by
    funext r
    simp only [Pi.add_apply, Real.log_mul (ne_of_gt hc) (ne_of_gt (hv r)), add_comm]
  rw [heq, necklaceRecovery_constant_core]

/-- Recovery is a well-defined map on the frozen quotient. -/
noncomputable def projectiveRecovery [NeZero n] (F : LooplessBAP n) :
    PosProj n → (Fin n → ℝ) := by
  refine Quot.lift (fun v : PosVec n => -necklaceRecovery F (fun r => Real.log (v.val r))) ?_
  rintro v w ⟨c, hc, hw⟩
  apply congrArg Neg.neg
  rw [hw]
  exact (ordinary_log_rescale F v.val v.property c hc).symm

@[simp] theorem projectiveRecovery_posClass [NeZero n] (F : LooplessBAP n) (v : PosVec n) :
    projectiveRecovery F (posClass v) = -necklaceRecovery F (fun r => Real.log (v.val r)) := rfl

/-- The quotient topology supplies continuity after descent. -/
theorem projectiveRecovery_continuous [NeZero n] (F : LooplessBAP n) :
    Continuous (projectiveRecovery F) := by
  have hlog : Continuous (fun v : PosVec n => fun r => Real.log (v.val r)) := by
    apply continuous_pi
    intro r
    exact ((continuous_apply r).comp continuous_subtype_val).log
      (fun v => ne_of_gt (v.property r))
  unfold projectiveRecovery necklaceRecovery
  exact continuous_quot_lift _
    ((continuous_const.matrix_mulVec (continuous_const.matrix_mulVec hlog)).neg)

end Conj43
