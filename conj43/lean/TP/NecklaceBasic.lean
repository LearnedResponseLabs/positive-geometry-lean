/- Apache-2.0. Arithmetic of the cyclic order `<_r`, cyclic induction on `Fin n`, a
   rise/fall count on the cycle, and item 1 (all terms of a necklace have the same
   cardinality). -/
import TP.NecklaceDefs

namespace TP

variable {n : ℕ}

/-! ### `finRotate` and `cycPos` in natural-number form -/

theorem val_finRotate (i : Fin n) :
    ((finRotate n i : Fin n) : ℕ) = if (i : ℕ) + 1 = n then 0 else (i : ℕ) + 1 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [coe_finRotate]
    by_cases h : i = Fin.last m
    · subst h; simp
    · have : (i : ℕ) < m := Fin.val_lt_last h
      rw [if_neg h, if_neg (by omega)]

theorem val_finRotate_symm (i : Fin n) :
    (((finRotate n).symm i : Fin n) : ℕ) = if (i : ℕ) = 0 then n - 1 else (i : ℕ) - 1 := by
  have hi := i.isLt
  set j := (finRotate n).symm i with hj
  have hji : finRotate n j = i := by rw [hj, Equiv.apply_symm_apply]
  have hv := val_finRotate j
  rw [hji] at hv
  have := j.isLt
  split_ifs at hv ⊢ <;> omega

theorem cycPos_eq (r i : Fin n) :
    cycPos r i = if (r : ℕ) ≤ i then (i : ℕ) - r else (i : ℕ) + n - r := by
  have hi := i.isLt
  have hr := r.isLt
  unfold cycPos
  split_ifs with h
  · rw [show (i : ℕ) + n - r = ((i : ℕ) - r) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem cycPos_lt (r i : Fin n) : cycPos r i < n := by
  have hi := i.isLt
  rw [cycPos_eq]; split_ifs <;> omega

@[simp] theorem cycPos_self (r : Fin n) : cycPos r r = 0 := by
  rw [cycPos_eq]; simp

theorem cycPos_eq_zero_iff {r i : Fin n} : cycPos r i = 0 ↔ i = r := by
  have hi := i.isLt
  have hr := r.isLt
  rw [cycPos_eq, Fin.ext_iff]
  split_ifs <;> omega

theorem cycPos_injective (r : Fin n) : Function.Injective (cycPos r) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  rw [cycPos_eq, cycPos_eq] at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem cycPos_inj {r i j : Fin n} : cycPos r i = cycPos r j ↔ i = j :=
  ⟨fun h => cycPos_injective r h, fun h => h ▸ rfl⟩

/-- Moving the base point one step: `r` becomes last, everything else moves down. -/
theorem cycPos_finRotate (r i : Fin n) :
    cycPos (finRotate n r) i = if i = r then n - 1 else cycPos r i - 1 := by
  have hi := i.isLt
  have hr := r.isLt
  have hv := val_finRotate r
  rw [cycPos_eq, cycPos_eq]
  by_cases h : i = r
  · subst h; simp only [if_true]; split_ifs at hv ⊢ <;> omega
  · have h' : (i : ℕ) ≠ r := fun e => h (Fin.ext e)
    simp only [if_neg h]
    split_ifs at hv ⊢ <;> omega

theorem cycPos_finRotate_finRotate (r i : Fin n) :
    cycPos (finRotate n r) (finRotate n i) = cycPos r i := by
  have hi := i.isLt
  have hr := r.isLt
  have h1 := val_finRotate r
  have h2 := val_finRotate i
  rw [cycPos_eq, cycPos_eq]
  split_ifs at h1 h2 ⊢ <;> omega

/-- `<_{r+1}` on labels other than `r` is `<_r`. -/
theorem cycPos_finRotate_lt {r x y : Fin n} (hx : x ≠ r) (hy : y ≠ r) :
    cycPos (finRotate n r) x < cycPos (finRotate n r) y ↔ cycPos r x < cycPos r y := by
  rw [cycPos_finRotate, cycPos_finRotate, if_neg hx, if_neg hy]
  have h1 : cycPos r x ≠ 0 := fun h => hx (cycPos_eq_zero_iff.mp h)
  have h2 : cycPos r y ≠ 0 := fun h => hy (cycPos_eq_zero_iff.mp h)
  omega

/-- In `<_{r+1}`, the label `r` is last. -/
theorem cycPos_finRotate_self_max (r y : Fin n) :
    cycPos (finRotate n r) y ≤ cycPos (finRotate n r) r := by
  have := cycPos_lt (finRotate n r) y
  rw [cycPos_finRotate r r, if_pos rfl]
  omega

/-- Every position below `n` is attained. -/
theorem exists_cycPos_eq (r : Fin n) {t : ℕ} (ht : t < n) : ∃ x : Fin n, cycPos r x = t := by
  have hr := r.isLt
  refine ⟨⟨(r + t) % n, Nat.mod_lt _ (by omega)⟩, ?_⟩
  rw [cycPos_eq]
  simp only
  by_cases h : (r : ℕ) + t < n
  · rw [Nat.mod_eq_of_lt h, if_pos (by omega)]; omega
  · rw [show (r : ℕ) + t = ((r : ℕ) + t - n) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), if_neg (by omega)]
    omega

/-! ### Cyclic induction and a rise/fall count -/

theorem iterate_finRotate_val (a : Fin n) (m : ℕ) :
    (((finRotate n)^[m] a : Fin n) : ℕ) = ((a : ℕ) + m) % n := by
  have ha := a.isLt
  induction m with
  | zero => simp [Nat.mod_eq_of_lt ha]
  | succ m ih =>
    rw [Function.iterate_succ_apply', val_finRotate, ih]
    have hn : 0 < n := by omega
    have hlt := Nat.mod_lt ((a : ℕ) + m) hn
    have key : ((a : ℕ) + m + 1) % n = (((a : ℕ) + m) % n + 1) % n :=
      (Nat.mod_add_mod _ _ _).symm
    rw [show (a : ℕ) + (m + 1) = ((a : ℕ) + m) + 1 by omega, key]
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact (Nat.mod_eq_of_lt (by omega)).symm

/-- A property preserved by the cyclic successor and true somewhere holds everywhere. -/
theorem cyc_induction {P : Fin n → Prop} (a : Fin n) (ha : P a)
    (step : ∀ t, P t → P (finRotate n t)) (t : Fin n) : P t := by
  have key : ∀ m, P ((finRotate n)^[m] a) := by
    intro m
    induction m with
    | zero => simpa using ha
    | succ m ih => rw [Function.iterate_succ_apply']; exact step _ ih
  have ht : (finRotate n)^[cycPos a t] a = t := by
    apply Fin.ext
    rw [iterate_finRotate_val, cycPos_eq]
    have hi := t.isLt
    have hr := a.isLt
    split_ifs with h
    · rw [show (a : ℕ) + ((t : ℕ) - a) = t by omega, Nat.mod_eq_of_lt hi]
    · rw [show (a : ℕ) + ((t : ℕ) + n - a) = t + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hi]
  rw [← ht]
  exact key _

/-- Around the cycle, a property is gained exactly as often as it is lost. -/
theorem card_rise_eq_card_fall (m : Fin n → Prop) [DecidablePred m] :
    (Finset.univ.filter fun t => ¬ m t ∧ m (finRotate n t)).card =
      (Finset.univ.filter fun t => m t ∧ ¬ m (finRotate n t)).card := by
  have hsum : (∑ t, if m (finRotate n t) then 1 else 0 : ℕ) = ∑ t, if m t then 1 else 0 :=
    Equiv.sum_comp (finRotate n) (fun t => if m t then 1 else 0)
  have hpt : ∀ t, ((if m (finRotate n t) then 1 else 0) +
      (if m t ∧ ¬ m (finRotate n t) then 1 else 0) : ℕ) =
      (if m t then 1 else 0) + (if ¬ m t ∧ m (finRotate n t) then 1 else 0) := by
    intro t
    by_cases h1 : m t <;> by_cases h2 : m (finRotate n t) <;>
      simp only [h1, h2, not_true, not_false_eq_true, and_true, and_false, if_true,
        if_false]
  have := Finset.sum_congr rfl (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) => hpt t)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum] at this
  rw [Finset.card_filter, Finset.card_filter]
  omega

/-! ### Item 1: equal cardinality -/

theorem IsNecklace.card_succ_le {I : Fin n → Finset (Fin n)} (hI : IsNecklace I) (r : Fin n) :
    (I (finRotate n r)).card ≤ (I r).card := by
  by_cases h : r ∈ I r
  · obtain ⟨j, hj⟩ := (hI r).1 h
    rw [hj]
    calc (insert j ((I r).erase r)).card ≤ ((I r).erase r).card + 1 := Finset.card_insert_le _ _
      _ = (I r).card := Finset.card_erase_add_one h
  · rw [(hI r).2 h]

theorem IsNecklace.card_succ {I : Fin n → Finset (Fin n)} (hI : IsNecklace I) (r : Fin n) :
    (I (finRotate n r)).card = (I r).card := by
  have hsum : (∑ t, (I (finRotate n t)).card) = ∑ t, (I t).card :=
    Equiv.sum_comp (finRotate n) (fun t => (I t).card)
  exact (Finset.sum_eq_sum_iff_of_le (fun t _ => hI.card_succ_le t)).mp hsum r
    (Finset.mem_univ r)

/-- All terms of a necklace have the same cardinality. -/
theorem necklace_card_eq {I : Fin n → Finset (Fin n)} (hI : IsNecklace I) (r s : Fin n) :
    (I r).card = (I s).card := by
  refine cyc_induction (P := fun t => (I t).card = (I s).card) s rfl ?_ r
  intro t ht
  rw [hI.card_succ t, ht]

end TP
