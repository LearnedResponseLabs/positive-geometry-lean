/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs

noncomputable section
namespace Conj43
variable {n : ℕ}

theorem rank_sum (F : LooplessBAP n) :
    ∑ i : Fin n, (F.f ((i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = (rank F : ℤ) * n := by
  sorry

theorem shift_bounds (F : LooplessBAP n) (hn : 0 < n) (p : ℤ) :
    p ≤ shiftF F p ∧ shiftF F p ≤ p + n := by
  sorry

theorem shift_periodic (F : LooplessBAP n) (p : ℤ) :
    shiftF F (p + n) = shiftF F p + n := by
  sorry

theorem shift_bijective (F : LooplessBAP n) :
    Function.Bijective (shiftF F) := by
  sorry

theorem shift_rank (F : LooplessBAP n) :
    ∑ i : Fin n, (shiftF F ((i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = ((rank F : ℤ) - 1) * n := by
  sorry

theorem shift_self_le_iff (f : ℤ → ℤ) (hf : ∀ i, i ≤ f i) :
    (∀ p, p ≤ f (p - 1)) ↔ ∀ i, f i ≠ i := by
  sorry

theorem elec_shift_eq_ising (N : ℕ) (hN : 0 < N) (τ : Equiv.Perm (Fin (2 * N)))
    (hinv : ∀ p, τ (τ p) = p) (hfix : ∀ p, τ p ≠ p) (p : ℤ) :
    shiftF (elecBAP τ) p = (isingBAP τ).f p := by
  sorry

end Conj43
