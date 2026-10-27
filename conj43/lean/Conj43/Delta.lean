import Conj43.L5Defs
import Conj43.Winding

/-! Telescoping and the winding-one lifted angle identity. -/
namespace Conj43
variable {n : ℕ}

theorem cycle_difference_sum (c : List (Fin n)) (h : Fin n → ℝ) :
    ((cycleEdges c).map fun e => h e.2 - h e.1).sum = 0 := by
  have hf : (cycleEdges c).map Prod.fst = c := by
    simp [cycleEdges, List.map_fst_zip]
  have hs : (cycleEdges c).map Prod.snd = c.rotate 1 := by
    simp [cycleEdges, List.map_snd_zip]
  have he : ((cycleEdges c).map fun e => h e.2).sum =
      ((cycleEdges c).map fun e => h e.1).sum := by
    have hm (f : Fin n × Fin n → Fin n) :
        ((cycleEdges c).map fun e => h (f e)) = ((cycleEdges c).map f).map h :=
      List.map_map.symm
    rw [hm Prod.snd, hm Prod.fst]
    rw [hf, hs]
    exact ((List.rotate_perm c 1).map h).sum_eq
  have sub_sum : ∀ l : List (Fin n × Fin n),
      (l.map fun e => h e.2 - h e.1).sum =
        (l.map fun e => h e.2).sum - (l.map fun e => h e.1).sum := by
    intro l; induction l with
    | nil => simp
    | cons e l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [sub_sum, he, sub_self]

theorem adv_real (p q : Fin n) :
    (adv p q : ℝ) = (q.val : ℝ) - (p.val : ℝ) +
      (n : ℝ) * (if q < p then 1 else 0) := by
  rcases lt_trichotomy p q with h | h | h
  · have ha := advD_of_lt h
    have hb : (adv p q : ℤ) = (q.val : ℤ) - (p.val : ℤ) := ha
    have hc : (adv p q : ℝ) = (q.val : ℝ) - (p.val : ℝ) := by exact_mod_cast hb
    simpa [not_lt_of_ge h.le] using hc
  · subst q
    simp [adv]
  · have ha := advD_of_gt h
    have hb : (adv p q : ℤ) = (q.val : ℤ) - (p.val : ℤ) + (n : ℤ) := ha
    have hc : (adv p q : ℝ) = (q.val : ℝ) - (p.val : ℝ) + (n : ℝ) := by
      exact_mod_cast hb
    simpa [h] using hc

/-- Winding one forces exactly one wrapped edge, expressed as a real sum. -/
theorem cycle_wrap_sum_core (c : List (Fin n)) (hlen : 3 ≤ c.length)
    (hw : winding c = n) :
    ((cycleEdges c).map fun e => if e.2 < e.1 then (1 : ℝ) else 0).sum = 1 := by
  have hn : 0 < n := by
    cases c with
    | nil => simp at hlen
    | cons p t => exact Nat.zero_lt_of_lt p.isLt
  have hw' : ((cycleEdges c).map fun e => (adv e.1 e.2 : ℝ)).sum = (n : ℝ) := by
    have hh := congrArg (fun k : ℕ => (k : ℝ)) hw
    simpa only [winding, Nat.cast_list_sum, List.map_map, Function.comp_def] using hh
  simp_rw [adv_real] at hw'
  rw [List.sum_map_add, cycle_difference_sum c (fun p => (p.val : ℝ)),
    List.sum_map_mul_left, zero_add] at hw'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_left_cancel₀ hn') (hw'.trans (mul_one _).symm)

/-- The lifted angles telescope to pi on each cycle supplied by the partition. -/
theorem delta_cycle_sum_core (θ : Fin n → ℝ) (c : List (Fin n))
    (hlen : 3 ≤ c.length) (_hnodup : c.Nodup) (hw : winding c = n) :
    ((cycleEdges c).map (delta θ)).sum = Real.pi := by
  change ((cycleEdges c).map fun e => θ e.2 - θ e.1 +
    Real.pi * (if e.2 < e.1 then 1 else 0)).sum = Real.pi
  rw [List.sum_map_add, List.sum_map_mul_left]
  rw [cycle_difference_sum, cycle_wrap_sum_core c hlen hw]
  ring

end Conj43
