/-
Conj43/WindowAscent.lean — §3: a reducible adjacent active ascent always exists.
The active positions form a σ-invariant set; the minimum maps up and the maximum
maps down, so the lift `w` ascends from min to max active position, forcing an
adjacent active ascent (the argmax of `w` has an active predecessor).
-/
import Conj43.Window

namespace Conj43

variable {n : ℕ}

namespace Window

/-- On an active position the lift is pinned: if `σ i > i` then `w i = σ i`. -/
theorem active_lift_of_gt (W : Window n) {i : Fin n} (h : W.Active i)
    (hgt : (i : ℕ) < (W.σ i : ℕ)) : W.w i = (W.σ i : ℕ) := by
  obtain ⟨hlo, hhi⟩ := W.active_strict h
  have hdm : n * (W.w i / n) + W.w i % n = W.w i := Nat.div_add_mod (W.w i) n
  rw [W.hres i] at hdm
  set d := W.w i / n
  have hnd : n * d < n := by omega
  have hd0 : d = 0 := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exact h0
    · exact absurd (Nat.mul_le_mul (le_refl n) h0) (by omega)
  rw [hd0, Nat.mul_zero, Nat.zero_add] at hdm
  exact hdm.symm

/-- On an active position the lift is pinned: if `σ i < i` then `w i = σ i + n`. -/
theorem active_lift_of_lt (W : Window n) {i : Fin n} (h : W.Active i)
    (hlt : (W.σ i : ℕ) < (i : ℕ)) : W.w i = (W.σ i : ℕ) + n := by
  obtain ⟨hlo, hhi⟩ := W.active_strict h
  have hin : (i : ℕ) < n := i.isLt
  have hwn : n ≤ W.w i := by
    by_contra hlt'
    push_neg at hlt'
    have heq : W.w i = (W.σ i : ℕ) := (Nat.mod_eq_of_lt hlt').symm.trans (W.hres i)
    omega
  have hdm : n * (W.w i / n) + W.w i % n = W.w i := Nat.div_add_mod (W.w i) n
  rw [W.hres i] at hdm
  set d := W.w i / n with hd
  have hge : 1 ≤ d := (Nat.one_le_div_iff (by omega)).mpr hwn
  have hle : d ≤ 1 := by
    have h2 : n * d < n * 2 := by omega
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  have hd1 : d = 1 := le_antisymm hle hge
  rw [hd1, Nat.mul_one] at hdm
  omega

/-- The active set is `σ`-invariant. -/
theorem sigma_active (W : Window n) {i : Fin n} (h : W.Active i) : W.Active (W.σ i) :=
  fun hc => h (W.σ.injective hc)

/-- **§3: a reducible adjacent active ascent exists.** From any active position,
produce `a < b` active, active-adjacent (nothing active strictly between), with
`w a < w b`. -/
theorem ascent_exists (W : Window n) (hact : ∃ i, W.Active i) :
    ∃ a b : Fin n, a < b ∧ W.Active a ∧ W.Active b ∧
      (∀ c : Fin n, a < c → c < b → ¬ W.Active c) ∧ W.w a < W.w b := by
  classical
  set A : Finset (Fin n) := Finset.univ.filter W.Active with hAdef
  have hmemA : ∀ x, x ∈ A ↔ W.Active x := fun x => by
    rw [hAdef, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩
  have hAne : A.Nonempty := by
    obtain ⟨i, hi⟩ := hact; exact ⟨i, (hmemA i).mpr hi⟩
  obtain ⟨b, hbA, hbmax⟩ := Finset.exists_max_image A W.w hAne
  have hbact : W.Active b := (hmemA b).mp hbA
  have hmnA : A.min' hAne ∈ A := A.min'_mem hAne
  have hmnact : W.Active (A.min' hAne) := (hmemA _).mp hmnA
  have hmxA : A.max' hAne ∈ A := A.max'_mem hAne
  have hmxact : W.Active (A.max' hAne) := (hmemA _).mp hmxA
  have hσmnA : W.σ (A.min' hAne) ∈ A := (hmemA _).mpr (W.sigma_active hmnact)
  have hmn_lt : (A.min' hAne : ℕ) < (W.σ (A.min' hAne) : ℕ) := by
    rcases lt_or_eq_of_le (A.min'_le _ hσmnA) with h | h
    · exact h
    · exact absurd h.symm hmnact
  have hwmn := W.active_lift_of_gt hmnact hmn_lt
  have hσmxA : W.σ (A.max' hAne) ∈ A := (hmemA _).mpr (W.sigma_active hmxact)
  have hmx_gt : (W.σ (A.max' hAne) : ℕ) < (A.max' hAne : ℕ) := by
    rcases lt_or_eq_of_le (A.le_max' _ hσmxA) with h | h
    · exact h
    · exact absurd h hmxact
  have hwmx := W.active_lift_of_lt hmxact hmx_gt
  have hend : W.w (A.min' hAne) < W.w (A.max' hAne) := by
    rw [hwmn, hwmx]; have := (W.σ (A.min' hAne)).isLt; omega
  have hbmn : b ≠ A.min' hAne := by
    intro hc
    have h1 : W.w (A.max' hAne) ≤ W.w b := hbmax _ hmxA
    rw [hc] at h1; omega
  have hmnb : A.min' hAne < b := lt_of_le_of_ne (A.min'_le b hbA) (Ne.symm hbmn)
  set A' : Finset (Fin n) := A.filter (· < b) with hA'def
  have hA'ne : A'.Nonempty := ⟨A.min' hAne, Finset.mem_filter.mpr ⟨hmnA, hmnb⟩⟩
  have haA' : A'.max' hA'ne ∈ A' := A'.max'_mem hA'ne
  have haA : A'.max' hA'ne ∈ A := (Finset.mem_filter.mp haA').1
  have hab : A'.max' hA'ne < b := (Finset.mem_filter.mp haA').2
  refine ⟨A'.max' hA'ne, b, hab, (hmemA _).mp haA, hbact, ?_, ?_⟩
  · intro c hac hcb hcact
    have hcA' : c ∈ A' := Finset.mem_filter.mpr ⟨(hmemA c).mpr hcact, hcb⟩
    exact absurd hac (not_lt.mpr (A'.le_max' c hcA'))
  · rcases lt_or_eq_of_le (hbmax _ haA) with h | h
    · exact h
    · exact absurd (W.w_inj h) (ne_of_lt hab)

/-- **§3 bounds (1).** For an adjacent active ascent, `b ≤ w a < w b ≤ a + n`. -/
theorem ascent_bounds (W : Window n) {a b : Fin n} (hab : a < b) (haact : W.Active a)
    (hbact : W.Active b) (hadj : ∀ c : Fin n, a < c → c < b → ¬ W.Active c) :
    (b : ℕ) ≤ W.w a ∧ W.w b ≤ (a : ℕ) + n := by
  have habn : (a : ℕ) < (b : ℕ) := hab
  have hane : (W.σ a : ℕ) ≠ (a : ℕ) := fun hc => haact (Fin.ext hc)
  have hbne : (W.σ b : ℕ) ≠ (b : ℕ) := fun hc => hbact (Fin.ext hc)
  have hbn := b.isLt
  refine ⟨?_, ?_⟩
  · have hα : (W.σ a : ℕ) < (a : ℕ) ∨ (b : ℕ) ≤ (W.σ a : ℕ) := by
      rcases lt_or_ge (W.σ a : ℕ) (a : ℕ) with h | h
      · exact Or.inl h
      · rcases lt_or_ge (W.σ a : ℕ) (b : ℕ) with h2 | h2
        · exact absurd (W.sigma_active haact)
            (hadj (W.σ a) (by exact_mod_cast lt_of_le_of_ne h (Ne.symm hane))
              (by exact_mod_cast h2))
        · exact Or.inr h2
    rcases hα with h | h
    · rw [W.active_lift_of_lt haact h]; omega
    · rw [W.active_lift_of_gt haact (lt_of_lt_of_le habn h)]; exact h
  · have hβ : (W.σ b : ℕ) ≤ (a : ℕ) ∨ (b : ℕ) < (W.σ b : ℕ) := by
      rcases lt_or_ge (b : ℕ) (W.σ b : ℕ) with h | h
      · exact Or.inr h
      · rcases lt_or_ge (a : ℕ) (W.σ b : ℕ) with h2 | h2
        · exact absurd (W.sigma_active hbact)
            (hadj (W.σ b) (by exact_mod_cast h2)
              (by exact_mod_cast lt_of_le_of_ne h hbne))
        · exact Or.inl h2
    rcases hβ with h | h
    · rw [W.active_lift_of_lt hbact (lt_of_le_of_lt h habn)]; omega
    · rw [W.active_lift_of_gt hbact h]; have := (W.σ b).isLt; omega

/-- The `(a,b)`-swapped window `g`: `σ_g = σ ∘ swap a b`, values at `a,b`
exchanged. Well-defined by the ascent bounds. -/
def swapWindow (W : Window n) (a b : Fin n) (hab : a < b)
    (h1 : (b : ℕ) ≤ W.w a) (h2 : W.w b ≤ (a : ℕ) + n)
    (h3 : (a : ℕ) ≤ W.w b) (h4 : W.w a ≤ (b : ℕ) + n) : Window n where
  σ := W.σ * Equiv.swap a b
  w := fun i => if i = a then W.w b else if i = b then W.w a else W.w i
  hres := by
    intro i
    split_ifs with hia hib
    · subst hia; rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact W.hres b
    · subst hib; rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; exact W.hres a
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hia hib]; exact W.hres i
  hlb := by
    intro i
    split_ifs with hia hib
    · subst hia; exact h3
    · subst hib; exact h1
    · exact W.hlb i
  hub := by
    intro i
    split_ifs with hia hib
    · subst hia; exact h2
    · subst hib; exact h4
    · exact W.hub i

@[simp] theorem swapWindow_σ (W : Window n) (a b : Fin n) (hab h1 h2 h3 h4) :
    (swapWindow W a b hab h1 h2 h3 h4).σ = W.σ * Equiv.swap a b := rfl

theorem swapWindow_w_apply (W : Window n) (a b : Fin n) (hab h1 h2 h3 h4) (i : Fin n) :
    (swapWindow W a b hab h1 h2 h3 h4).w i =
      if i = a then W.w b else if i = b then W.w a else W.w i := rfl

/-! ### §4: the strictly decreasing measure `∑ i·w_i` -/

/-- Position-weighted lift sum. The `(a,b)`-swap with `a<b`, `w a < w b` strictly
decreases it, giving a clean termination measure (no inversion counting needed). -/
def measure (W : Window n) : ℕ := ∑ i : Fin n, (i : ℕ) * W.w i

theorem measure_split (a b : Fin n) (hab' : a ≠ b) (f : Fin n → ℕ) :
    (∑ i : Fin n, (i : ℕ) * f i)
      = (∑ i ∈ (Finset.univ.erase a).erase b, (i : ℕ) * f i)
        + ((a : ℕ) * f a + (b : ℕ) * f b) := by
  have hbmem : b ∈ Finset.univ.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab', Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add Finset.univ (fun i : Fin n => (i : ℕ) * f i) (Finset.mem_univ a),
      ← Finset.sum_erase_add (Finset.univ.erase a) (fun i : Fin n => (i : ℕ) * f i) hbmem]
  ring

theorem swap_measure_lt (W : Window n) (a b : Fin n) (hab : a < b)
    (h1 h2 h3 h4) (hasc : W.w a < W.w b) :
    (swapWindow W a b hab h1 h2 h3 h4).measure < W.measure := by
  have hab' : a ≠ b := ne_of_lt hab
  set g := swapWindow W a b hab h1 h2 h3 h4 with hgdef
  have hga : g.w a = W.w b := by rw [hgdef, swapWindow_w_apply, if_pos rfl]
  have hgb : g.w b = W.w a := by
    rw [hgdef, swapWindow_w_apply, if_neg (Ne.symm hab'), if_pos rfl]
  have hsame : (∑ i ∈ (Finset.univ.erase a).erase b, (i : ℕ) * g.w i)
      = ∑ i ∈ (Finset.univ.erase a).erase b, (i : ℕ) * W.w i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    obtain ⟨hib, hi'⟩ := Finset.mem_erase.mp hi
    obtain ⟨hia, _⟩ := Finset.mem_erase.mp hi'
    rw [hgdef, swapWindow_w_apply, if_neg hia, if_neg hib]
  have hlt : (a : ℕ) * W.w b + (b : ℕ) * W.w a < (a : ℕ) * W.w a + (b : ℕ) * W.w b := by
    have hab2 : (a : ℕ) < (b : ℕ) := hab
    nlinarith [hab2, hasc]
  show g.measure < W.measure
  unfold Window.measure
  rw [measure_split a b hab' g.w, measure_split a b hab' W.w, hsame, hga, hgb]
  omega

end Window

end Conj43
