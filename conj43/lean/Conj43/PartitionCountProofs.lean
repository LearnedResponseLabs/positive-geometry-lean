/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceRefinedDefs
import Conj43.CyclicArc
namespace Conj43
variable {n : ℕ}


private theorem adv_balance (p q : Fin n) :
    adv p q + (p : ℕ) = (q : ℕ) + n * (if q < p then 1 else 0) := by
  have hp := p.isLt
  have hq := q.isLt
  have hn : 0 < n := by omega
  change step n p q + (p : ℕ) = _
  rcases step_spec hn hp hq with ⟨h,e⟩ | ⟨h,e⟩ <;>
    split_ifs <;> simp only [Fin.lt_def] at * <;> simp only [mul_one, mul_zero] <;> omega

private theorem edges_balance (es : List (Fin n × Fin n)) :
    (es.map fun e => adv e.1 e.2).sum + (es.map fun e => (e.1 : ℕ)).sum =
      (es.map fun e => (e.2 : ℕ)).sum + n * es.countP (fun e => e.2 < e.1) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := adv_balance e.1 e.2
    by_cases h : e.2 < e.1 <;> simp [h, Nat.mul_add] at he ⊢ <;> omega


/-! ### Group `count`: the cycle count of CLH-5 -/

/-- A duplicate-free cycle winds `n` times its number of wrapped edges (edges `p → q` with `q < p`). -/
theorem winding_eq_wrapped (c : List (Fin n)) (hc : c.Nodup) :
    winding c = n * (cycleEdges c).countP (fun e => e.2 < e.1) := by
  have hfst := congrArg (fun l : List (Fin n) => (l.map Fin.val).sum)
    (List.map_fst_zip (l₁ := c) (l₂ := c.rotate 1) (by simp))
  have hsnd := congrArg (fun l : List (Fin n) => (l.map Fin.val).sum)
    (List.map_snd_zip (l₁ := c) (l₂ := c.rotate 1) (by simp))
  have hrot : ((c.rotate 1).map Fin.val).sum = (c.map Fin.val).sum :=
    ((List.rotate_perm c 1).map Fin.val).sum_eq
  have h := edges_balance (cycleEdges c)
  simp only [List.map_map, Function.comp_def] at hfst hsnd
  dsimp only [cycleEdges] at h
  rw [hfst, hsnd, hrot] at h
  unfold winding cycleEdges
  omega

/-- **eq:wp-cycle-count.** Every winding-one partition of the crossing edges has as many cycles as there are
wrapped crossing edges. -/
theorem partition_card (F : LooplessBAP n) (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F)) :
    cycles.length = (crossEdges F).countP (fun e => e.2 < e.1) := by
  have hncase : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
  rcases hncase with hn | hn
  · subst n
    have hz : cycles = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro c hc'
      have he : c = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        exact Fin.elim0 x
      have hl := (hc c hc').1
      simp [he] at hl
    simp [hz, crossEdges]
  · have hone : ∀ c ∈ cycles, (cycleEdges c).countP (fun e => e.2 < e.1) = 1 := by
      intro c hmem
      have hh := hc c hmem
      have hw := winding_eq_wrapped c hh.2.1
      rw [hh.2.2] at hw
      nlinarith
    have hsum : (cycles.flatMap cycleEdges).countP (fun e => e.2 < e.1) = cycles.length := by
      clear hc hp
      induction cycles with
      | nil => simp
      | cons c cs ih =>
        simp only [List.flatMap_cons, List.countP_append, List.length_cons]
        rw [hone c (by simp), ih (fun c h => hone c (List.mem_cons_of_mem _ h))]
        omega
    exact hsum.symm.trans (hp.countP_eq _)

end Conj43
