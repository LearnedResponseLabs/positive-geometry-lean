/-
Conj43/Winding.lean — winding-one ⟺ sorted-subset, and the cover→conclusion assembly.

To avoid an import cycle with the pinned `Conj43/Statements.lean` (which defines
`adv`/`cycleEdges`/`winding` and states the goal), we work with local *definitionally
identical* copies `advD`/`cycleEdgesD`/`windingD` (same bodies). The final glue in
Statements bridges them by `rfl`/defeq. Nothing pinned is touched.

Key fact (verified n≤6 by a script not included): a Nodup cycle of length ≥ 2 has winding = n iff
it is a rotation of its sorted-increasing order — the strictly increasing lift
`C_{i+1}=C_i+adv` spans a window of length exactly n. The topological content of
prop:wp's seed is `Conj43/Seed.lean` (`crossEdges_subset_cover`, PROVED via window induction).
-/
import Conj43.Defs

namespace Conj43

variable {n : ℕ}

/-! ### Definitionally identical copies of the pinned cycle vocabulary -/

/-- Copy of the pinned `adv` (exit-advance of an edge p→q). -/
def advD {n : ℕ} (p q : Fin n) : ℕ := ((q : ℕ) + n - (p : ℕ)) % n

/-- Copy of the pinned `winding`. -/
def windingD {n : ℕ} (c : List (Fin n)) : ℕ :=
  ((cycleEdgesD c).map fun e => advD e.1 e.2).sum

/-! ### `advD` as an integer, split by wrap -/

/-- On a forward (non-wrapping) step `a < b`, the advance is just the difference. -/
theorem advD_of_lt {a b : Fin n} (h : (a : ℕ) < (b : ℕ)) :
    (advD a b : ℤ) = (b : ℤ) - (a : ℤ) := by
  have hb : (b : ℕ) < n := b.isLt
  unfold advD
  have hrw : (b : ℕ) + n - (a : ℕ) = n + ((b : ℕ) - (a : ℕ)) := by omega
  rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  push_cast [Nat.cast_sub h.le]
  ring

/-- On the single wrapping step `b < a`, the advance carries one extra `n`. -/
theorem advD_of_gt {a b : Fin n} (h : (b : ℕ) < (a : ℕ)) :
    (advD a b : ℤ) = (b : ℤ) - (a : ℤ) + (n : ℤ) := by
  have ha : (a : ℕ) < n := a.isLt
  unfold advD
  rw [Nat.mod_eq_of_lt (by omega)]
  push_cast
  omega

/-! ### Telescoping over the forward (non-wrap) edges -/

/-- The forward edges of `a :: t` are `(a :: t).zip t`; on a strictly increasing list
their advances telescope to `last − a`. -/
theorem forward_adv_sum (a : Fin n) (t : List (Fin n))
    (hchain : List.IsChain (· < ·) (a :: t)) :
    (((a :: t).zip t).map (fun e => (advD e.1 e.2 : ℤ))).sum
      = ((a :: t).getLast (by simp) : ℤ) - (a : ℤ) := by
  induction t generalizing a with
  | nil => simp
  | cons b t' ih =>
    obtain ⟨hab, hchain'⟩ := List.isChain_cons_cons.mp hchain
    have hstep : (List.zip (a :: b :: t') (b :: t'))
        = (a, b) :: (b :: t').zip t' := rfl
    rw [hstep, List.map_cons, List.sum_cons, advD_of_lt hab, ih b hchain']
    have hlast : ((a :: b :: t').getLast (by simp) : ℤ)
        = ((b :: t').getLast (by simp) : ℤ) := by
      rw [List.getLast_cons_cons]
    rw [hlast]; ring

/-! ### The cyclic (wrap) edge -/

/-- `rotate 1` on a nonempty list moves the head to the back. -/
theorem rotate_one_cons (a : Fin n) (t : List (Fin n)) :
    (a :: t).rotate 1 = t ++ [a] := by
  rw [List.rotate_cons_succ, List.rotate_zero]

/-- Zipping against `tail ++ [c]` = zipping against the tail, plus the closing pair. -/
theorem zip_tail_append (c : Fin n) :
    ∀ (l : List (Fin n)) (hne : l ≠ []),
      l.zip (l.tail ++ [c]) = l.zip l.tail ++ [(l.getLast hne, c)] := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x rest ih =>
    intro _
    cases rest with
    | nil => simp
    | cons y t' =>
      have hih := ih (by simp)
      simp only [List.tail_cons] at hih ⊢
      rw [List.cons_append, List.zip_cons_cons, List.zip_cons_cons, hih,
        List.getLast_cons_cons, List.cons_append]

/-! ### windingD = n on a strictly increasing list -/

/-- Strictly increasing ⇒ head < last (length ≥ 2). -/
theorem head_lt_getLast {a : Fin n} {t : List (Fin n)} (htne : t ≠ [])
    (hchain : List.IsChain (· < ·) (a :: t)) :
    (a : ℕ) < ((a :: t).getLast (by simp) : ℕ) := by
  have hp : List.Pairwise (· < ·) (a :: t) := List.isChain_iff_pairwise.mp hchain
  rw [List.pairwise_cons] at hp
  have hmem : (a :: t).getLast (by simp) ∈ t := by
    rw [List.getLast_cons htne]; exact List.getLast_mem htne
  exact hp.1 _ hmem

/-- **Winding-one from sorted.** A strictly increasing list of length ≥ 2 has
`windingD = n`. -/
theorem winding_strictMono (a : Fin n) (t : List (Fin n)) (htne : t ≠ [])
    (hchain : List.IsChain (· < ·) (a :: t)) :
    windingD (a :: t) = n := by
  have hne : (a :: t) ≠ [] := by simp
  have hce : cycleEdgesD (a :: t) = (a :: t).zip t ++ [((a :: t).getLast hne, a)] := by
    unfold cycleEdgesD
    rw [rotate_one_cons]
    have h := zip_tail_append a (a :: t) hne
    simpa using h
  have hgt := head_lt_getLast htne hchain
  have hcast : (windingD (a :: t) : ℤ)
      = ((cycleEdgesD (a :: t)).map (fun e => (advD e.1 e.2 : ℤ))).sum := by
    unfold windingD
    rw [Nat.cast_list_sum, List.map_map]
    rfl
  have hz : (windingD (a :: t) : ℤ) = (n : ℤ) := by
    rw [hcast, hce, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, forward_adv_sum a t hchain, advD_of_gt hgt]
    ring
  exact_mod_cast hz

/-! ### From subsets to winding-one cycles -/

/-- A subset of size ≥ 3 gives a length-≥3, `Nodup`, winding-one cycle. -/
theorem winding_consecutive {S : Finset (Fin n)} (h3 : 3 ≤ S.card) :
    3 ≤ (S.sort (· ≤ ·)).length ∧ (S.sort (· ≤ ·)).Nodup
      ∧ windingD (S.sort (· ≤ ·)) = n := by
  have hlen : 3 ≤ (S.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact h3
  have hnodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have hchain : List.IsChain (· < ·) (S.sort (· ≤ ·)) := (Finset.sortedLT_sort S).isChain
  refine ⟨hlen, hnodup, ?_⟩
  obtain ⟨a, t, hat⟩ : ∃ a t, S.sort (· ≤ ·) = a :: t := by
    cases h : S.sort (· ≤ ·) with
    | nil => rw [h] at hlen; simp at hlen
    | cons a t => exact ⟨a, t, rfl⟩
  have htne : t ≠ [] := by rintro rfl; rw [hat] at hlen; simp at hlen
  have hchain' : List.IsChain (· < ·) (a :: t) := hat ▸ hchain
  rw [hat]; exact winding_strictMono a t htne hchain'

/-- **cover → conclusion (movement 3 output).** Any cover of the crossing edges by
consecutive-edge lists of size-≥3 subsets yields the winding-one partition. -/
theorem partition_of_cover (F : LooplessBAP n) (Ss : List (Finset (Fin n)))
    (hcard : ∀ S ∈ Ss, 3 ≤ S.card)
    (hperm : (Ss.flatMap consecutiveEdges).Perm (crossEdges F)) :
    ∃ cycles : List (List (Fin n)),
      (∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ windingD c = n) ∧
      (cycles.flatMap cycleEdgesD).Perm (crossEdges F) := by
  refine ⟨Ss.map (fun S => S.sort (· ≤ ·)), ?_, ?_⟩
  · intro c hc
    rw [List.mem_map] at hc
    obtain ⟨S, hS, rfl⟩ := hc
    exact winding_consecutive (hcard S hS)
  · have hflat : (Ss.map (fun S => S.sort (· ≤ ·))).flatMap cycleEdgesD
        = Ss.flatMap consecutiveEdges := by
      rw [List.flatMap_map]; rfl
    rw [hflat]; exact hperm

end Conj43
