/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs
import Conj43.InterfaceProofs

namespace Conj43
variable {n : ℕ}

theorem rank_sum (F : LooplessBAP n) :
    ∑ i : Fin n, (F.f ((i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = (rank F : ℤ) * n := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  simp_rw [f_window hn]
  have hs : (∑ i : Fin n, (F.σ i : ℤ)) = ∑ i : Fin n, (i : ℤ) :=
    Equiv.sum_comp F.σ (fun i : Fin n => (i : ℤ))
  have hc : (∑ i : Fin n, if F.σ i ≤ i then (n : ℤ) else 0) = (rank F : ℤ) * n := by
    rw [← Finset.sum_filter]
    simp [rank]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hs, hc]
  ring

theorem shift_bounds (F : LooplessBAP n) (hn : 0 < n) (p : ℤ) :
    p ≤ shiftF F p ∧ shiftF F p ≤ p + n := by
  have hb := f_bounds hn F (p - 1)
  unfold shiftF
  omega

theorem shift_periodic (F : LooplessBAP n) (p : ℤ) :
    shiftF F (p + n) = shiftF F p + n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have ht := f_translate hn F (p - 1) 1
  simp only [one_mul] at ht
  unfold shiftF
  rw [show p + (n : ℤ) - 1 = p - 1 + n by ring, ht]

theorem shift_bijective (F : LooplessBAP n) :
    Function.Bijective (shiftF F) := by
  have hb : Function.Bijective (fun p : ℤ => p - 1) := by
    constructor
    · intro p q he
      change p - 1 = q - 1 at he
      omega
    · intro p; exact ⟨p + 1, by ring⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change Function.Bijective (fun p : ℤ => p - 1)
    exact hb
  exact (f_bijective hn F).comp hb

lemma extensions_shift_window (F : LooplessBAP n) :
    (∑ i : Fin n, F.f ((i : ℤ) - 1)) = (∑ i : Fin n, F.f (i : ℤ)) - n := by
  cases n with
  | zero => simp
  | succ k =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    have ht := f_translate (by omega : 0 < k + 1) F (-1) 1
    simp only [one_mul, Nat.cast_add, Nat.cast_one] at ht
    have hk : (-1 : ℤ) + (k + 1) = k := by ring
    rw [hk] at ht
    simp only [Fin.val_zero, Nat.cast_zero, zero_sub, Fin.val_succ,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Fin.val_castSucc, Fin.val_last]
    omega

theorem shift_rank (F : LooplessBAP n) :
    ∑ i : Fin n, (shiftF F ((i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = ((rank F : ℤ) - 1) * n := by
  simp only [shiftF, Finset.sum_sub_distrib]
  rw [extensions_shift_window]
  have hr := rank_sum F
  rw [Finset.sum_sub_distrib] at hr
  nlinarith

theorem shift_self_le_iff (f : ℤ → ℤ) (hf : ∀ i, i ≤ f i) :
    (∀ p, p ≤ f (p - 1)) ↔ ∀ i, f i ≠ i := by
  constructor
  · intro h i
    have hi := h (i + 1)
    simp only [add_sub_cancel_right] at hi
    omega
  · intro h p
    have hi := hf (p - 1)
    have hn := h (p - 1)
    omega

theorem elec_shift_eq_ising (N : ℕ) (hN : 0 < N) (τ : Equiv.Perm (Fin (2 * N)))
    (hinv : ∀ p, τ (τ p) = p) (hfix : ∀ p, τ p ≠ p) (p : ℤ) :
    shiftF (elecBAP τ) p = (isingBAP τ).f p := by
  have hn : 0 < 2 * N := by omega
  have hn2 : 1 < 2 * N := by omega
  have hw (i : Fin (2 * N)) :
      (elecBAP τ).f ((i : ℤ) - 1) = (isingBAP τ).f (i : ℤ) := by
    have hne : (τ i).val ≠ i.val := fun h => hfix i (Fin.ext h)
    rw [f_window hn]
    change _ = (τ i : ℤ) + if τ i ≤ i then ((2 * N : ℕ) : ℤ) else 0
    by_cases hi : i.val = 0
    · let j : Fin (2 * N) := ⟨2 * N - 1, by omega⟩
      have hj : finRotate (2 * N) j = i := by
        rw [finRotate_apply]
        apply Fin.ext
        simp only [Fin.val_add]
        dsimp [j]
        rw [Nat.mod_eq_of_lt hn2]
        have he : 2 * N - 1 + 1 = 2 * N := by omega
        rw [he, Nat.mod_self]
        exact hi.symm
      have ht := f_translate hn (elecBAP τ) ((i : ℤ) - 1) 1
      have he : (i : ℤ) - 1 + 1 * (2 * N : ℕ) = (j : ℤ) := by
        dsimp [j]
        omega
      rw [he, f_window hn] at ht
      change (τ (finRotate (2 * N) j) : ℤ) +
        (if τ (finRotate (2 * N) j) ≤ j then ((2 * N : ℕ) : ℤ) else 0) = _ at ht
      rw [hj] at ht
      have hle : τ i ≤ j := by
        have := (τ i).isLt
        change (τ i).val ≤ 2 * N - 1
        omega
      have hnot : ¬ τ i ≤ i := by
        simp only [Fin.le_def]
        omega
      rw [if_pos hle] at ht
      rw [if_neg hnot]
      omega
    · let j : Fin (2 * N) := ⟨i.val - 1, by omega⟩
      have hj : finRotate (2 * N) j = i := by
        rw [finRotate_apply]
        apply Fin.ext
        simp only [Fin.val_add]
        dsimp [j]
        rw [Nat.mod_eq_of_lt hn2]
        have he : i.val - 1 + 1 = i.val := by omega
        rw [he, Nat.mod_eq_of_lt i.isLt]
      have he : (i : ℤ) - 1 = (j : ℤ) := by
        dsimp [j]
        omega
      rw [he, f_window hn]
      change (τ (finRotate (2 * N) j) : ℤ) +
        (if τ (finRotate (2 * N) j) ≤ j then ((2 * N : ℕ) : ℤ) else 0) = _
      rw [hj]
      have hc : τ i ≤ j ↔ τ i ≤ i := by
        simp only [Fin.le_def]
        dsimp [j]
        omega
      simp only [hc]
  let i := residue hn p
  have he : p = (i : ℤ) + (p / (2 * N : ℕ)) * (2 * N : ℕ) := by
    dsimp [i]
    rw [residue_val]
    exact (Int.emod_add_ediv_mul p (2 * N : ℕ)).symm
  unfold shiftF
  conv_lhs => rw [he]
  rw [show (i : ℤ) + (p / (2 * N : ℕ)) * (2 * N : ℕ) - 1 =
    (i : ℤ) - 1 + (p / (2 * N : ℕ)) * (2 * N : ℕ) by ring,
    f_translate hn, hw]
  conv_rhs => rw [he]
  rw [f_translate hn]

end Conj43
