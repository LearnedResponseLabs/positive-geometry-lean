/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.WindowLemmasDefs
import Conj43.CyclicArc
import Conj43.Winding

/-!
Closed-walk helpers for Lemma 14. The balance and telescoping proof is ported
from `Conj43/PartitionCountProofs.lean` (Apache-2.0); its proof never uses the
duplicate-free premise, so the helper here records the general identity.
Rotation to a least label then turns a one-descent walk into a strict chain.
-/
namespace Conj43.WindowLemmas
variable {n : ℕ}

theorem advance_balance (p q : Fin n) :
    adv p q + (p : ℕ) = (q : ℕ) + n * (if q < p then 1 else 0) := by
  have hp := p.isLt
  have hq := q.isLt
  have hn : 0 < n := by omega
  change step n p q + (p : ℕ) = _
  rcases step_spec hn hp hq with ⟨h,e⟩ | ⟨h,e⟩ <;>
    split_ifs <;> simp only [Fin.lt_def] at * <;> simp only [mul_one, mul_zero] <;> omega

theorem walk_edges_balance (es : List (Fin n × Fin n)) :
    (es.map fun e => adv e.1 e.2).sum + (es.map fun e => (e.1 : ℕ)).sum =
      (es.map fun e => (e.2 : ℕ)).sum + n * es.countP (fun e => e.2 < e.1) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := advance_balance e.1 e.2
    by_cases h : e.2 < e.1 <;> simp [h, Nat.mul_add] at he ⊢ <;> omega

theorem winding_count_descents (c : List (Fin n)) :
    winding c = n * (cycleEdges c).countP (fun e => e.2 < e.1) := by
  have hfst := congrArg (fun l : List (Fin n) => (l.map Fin.val).sum)
    (List.map_fst_zip (l₁ := c) (l₂ := c.rotate 1) (by simp))
  have hsnd := congrArg (fun l : List (Fin n) => (l.map Fin.val).sum)
    (List.map_snd_zip (l₁ := c) (l₂ := c.rotate 1) (by simp))
  have hrot : ((c.rotate 1).map Fin.val).sum = (c.map Fin.val).sum :=
    ((List.rotate_perm c 1).map Fin.val).sum_eq
  have h := walk_edges_balance (cycleEdges c)
  simp only [List.map_map, Function.comp_def] at hfst hsnd
  dsimp only [cycleEdges] at h
  rw [hfst, hsnd, hrot] at h
  unfold winding cycleEdges
  omega

theorem advance_pos {p q : Fin n} (h : p ≠ q) : 0 < adv p q := by
  have hn : 0 < n := by have := p.isLt; omega
  have hpq : (p : ℕ) ≠ (q : ℕ) := fun hc => h (Fin.ext hc)
  change 0 < step n p q
  rcases step_spec hn p.isLt q.isLt with ⟨h1,e1⟩ | ⟨h1,e1⟩ <;> omega

theorem cycleEdges_rotate (c : List (Fin n)) (k : ℕ) :
    cycleEdges (c.rotate k) = (cycleEdges c).rotate k := by
  unfold cycleEdges
  change List.zipWith Prod.mk (c.rotate k) ((c.rotate k).rotate 1) =
    (List.zipWith Prod.mk c (c.rotate 1)).rotate k
  rw [List.zipWith_rotate_distrib _ _ _ _ (by simp)]
  simp only [List.rotate_rotate, Nat.add_comm]

theorem strictChain_of_forward (c : List (Fin n))
    (h : ∀ e ∈ c.zip c.tail, e.1 < e.2) : List.IsChain (· < ·) c := by
  induction c with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      apply List.isChain_cons_cons.mpr
      refine ⟨h (a,b) (by simp), ih ?_⟩
      intro e he
      exact h e (by simpa only [List.tail_cons, List.zip_cons_cons, List.mem_cons] using Or.inr he)

theorem nodup_of_one_descent (c : List (Fin n)) (hm : 2 ≤ c.length)
    (hc : ∀ e ∈ cycleEdges c, e.1 ≠ e.2)
    (hd : (cycleEdges c).countP (fun e => e.2 < e.1) = 1) : c.Nodup := by
  have hlen : 0 < c.length := by omega
  let a := c.minimum_of_length_pos hlen
  have ha : a ∈ c := List.minimum_of_length_pos_mem hlen
  have hmin : ∀ x ∈ c, a ≤ x := fun x hx => List.minimum_of_length_pos_le_of_mem hx hlen
  obtain ⟨s,t,hst⟩ := List.mem_iff_append.mp ha
  have hr : c.rotate s.length = a :: (t ++ s) := by
    rw [hst, List.rotate_append_length_eq]
    rfl
  have hcr : ∀ e ∈ cycleEdges (a :: (t ++ s)), e.1 ≠ e.2 := by
    intro e he
    rw [← hr, cycleEdges_rotate, List.mem_rotate] at he
    exact hc e he
  have hdr : (cycleEdges (a :: (t ++ s))).countP (fun e => e.2 < e.1) = 1 := by
    rw [← hr, cycleEdges_rotate, (List.rotate_perm (cycleEdges c) s.length).countP_eq]
    exact hd
  have hce : cycleEdges (a :: (t ++ s)) =
      (a :: (t ++ s)).zip (t ++ s) ++ [((a :: (t ++ s)).getLast (by simp), a)] := by
    unfold cycleEdges
    rw [rotate_one_cons]
    exact zip_tail_append a (a :: (t ++ s)) (by simp)
  have hlastmem : (a :: (t ++ s)).getLast (by simp) ∈ c := by
    rw [← List.mem_rotate (n := s.length), hr]
    exact List.getLast_mem (by simp)
  have hlastne := hcr ((a :: (t ++ s)).getLast (by simp), a) (by rw [hce]; simp)
  have hlast : a < (a :: (t ++ s)).getLast (by simp) :=
    lt_of_le_of_ne (hmin _ hlastmem) (Ne.symm hlastne)
  have hzero : ((a :: (t ++ s)).zip (t ++ s)).countP (fun e => e.2 < e.1) = 0 := by
    rw [hce] at hdr
    simpa [hlast] using hdr
  have hchain : List.IsChain (· < ·) (a :: (t ++ s)) := by
    apply strictChain_of_forward
    intro e he
    have hne := hcr e (by rw [hce]; exact List.mem_append_left _ he)
    have hnot := List.countP_eq_zero.mp hzero e he
    simp only [decide_eq_true_eq] at hnot
    exact lt_of_le_of_ne (le_of_not_gt hnot) hne
  have hnd : (a :: (t ++ s)).Nodup :=
    (List.isChain_iff_pairwise.mp hchain).nodup
  rw [← hr] at hnd
  exact List.nodup_rotate.mp hnd

end Conj43.WindowLemmas
