/- SPDX-License-Identifier: Apache-2.0 -/
import TP.LoopDeleteDefs

/-! # The frozen statements (to be frozen in `Challenge/Loops.lean`) -/

namespace TP

/-- **Deleting a loop leaves a bounded affine permutation** of period `n`. -/
theorem deleteLoop_bdd {n : ℕ} (hn : 0 < n) (g : BddAffPerm (n + 1)) (p : Fin (n + 1))
    (hp : g.f (p : ℕ) = (p : ℕ)) :
    Function.Bijective (deleteLoopFun n p g.f) ∧
      (∀ i, deleteLoopFun n p g.f (i + n) = deleteLoopFun n p g.f i + n) ∧
      (∀ i, i ≤ deleteLoopFun n p g.f i) ∧ (∀ i, deleteLoopFun n p g.f i ≤ i + n) := by
  sorry

/-- **Deleting a loop keeps the rank** `k`. -/
theorem affRank_deleteLoop {n : ℕ} (hn : 0 < n) (g : BddAffPerm (n + 1)) (p : Fin (n + 1))
    (hp : g.f (p : ℕ) = (p : ℕ)) :
    affRank n (deleteLoopFun n p g.f) = affRank (n + 1) g.f := by
  sorry

/-- **Deleting a loop lowers the length by exactly `k`**: `ℓ(f) = ℓ(f') + k`, the bookkeeping identity of the CLH
paper's remark on loops (`rem:loops`), equivalently the face count of a reduced plabic graph left unchanged by deleting
a lollipop. -/
theorem affLength_deleteLoop {n : ℕ} (hn : 0 < n) (g : BddAffPerm (n + 1)) (p : Fin (n + 1))
    (hp : g.f (p : ℕ) = (p : ℕ)) :
    (affLength (n + 1) g.f : ℤ) = affLength n (deleteLoopFun n p g.f) + affRank (n + 1) g.f := by
  sorry

end TP
