/-
Conj43/SeedCover.lean — combinatorics of `consecutiveEdges` (the sorted cyclic
edge list of a Finset), part 1: the `advD` toolkit and the argmin characterization
of cyclic edges. `(u,v)` is a consecutive edge of `S` iff `v` minimises the forward
advance `advD u ·` over `S \ {u}` — the cyclic successor. Handles the wrap edge
uniformly. Verified computationally (script not included; |S|≥2, n≤7).
-/
import Conj43.Window

namespace Conj43

variable {n : ℕ}

/-! ### `advD` toolkit (advance = `step n` on the row circle) -/

theorem advD_eq_step (p q : Fin n) : advD p q = step n (p : ℕ) (q : ℕ) := rfl

theorem advD_lt (p q : Fin n) : advD p q < n := by
  have hn : 0 < n := by have := p.isLt; omega
  rw [advD_eq_step]; exact Nat.mod_lt _ hn

theorem advD_self (p : Fin n) : advD p p = 0 := by
  rw [advD_eq_step]; exact step_self n (p : ℕ)

theorem advD_pos {p q : Fin n} (h : p ≠ q) : 0 < advD p q := by
  have hn : 0 < n := by have := p.isLt; omega
  have hpq : (p : ℕ) ≠ (q : ℕ) := fun hc => h (Fin.ext hc)
  rw [advD_eq_step]
  rcases step_spec hn p.isLt q.isLt with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> omega

/-- `advD u ·` is injective on `Fin n`. -/
theorem advD_inj (u : Fin n) : Function.Injective (fun v : Fin n => advD u v) := by
  intro v w h
  simp only at h
  have hn : 0 < n := by have := u.isLt; omega
  rw [advD_eq_step, advD_eq_step] at h
  have hv := v.isLt; have hw := w.isLt
  apply Fin.ext
  rcases step_spec hn u.isLt hv with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases step_spec hn u.isLt hw with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> omega

/-! ### Index membership of `consecutiveEdges` -/

/-- `consecutiveEdges S` in index form: `(u,v)` is a consecutive edge iff for some
position `i` in the sorted list `l = S.sort`, `u = l[i]` and `v = l[(i+1) mod k]`.
The extra existential `hs` carries the validity of the cyclic-successor index. -/
theorem edge_index_mem (S : Finset (Fin n)) (u v : Fin n) :
    (u, v) ∈ consecutiveEdges S ↔
      ∃ (i : ℕ) (hi : i < (S.sort (· ≤ ·)).length)
        (hs : (i + 1) % (S.sort (· ≤ ·)).length < (S.sort (· ≤ ·)).length),
        (S.sort (· ≤ ·))[i]'hi = u ∧
        (S.sort (· ≤ ·))[(i + 1) % (S.sort (· ≤ ·)).length]'hs = v := by
  set l := S.sort (· ≤ ·) with hl
  unfold consecutiveEdges cycleEdgesD
  rw [List.mem_iff_getElem]
  have hlen : (l.zip (l.rotate 1)).length = l.length := by
    rw [List.length_zip, List.length_rotate]; simp
  constructor
  · rintro ⟨i, hi, heq⟩
    rw [hlen] at hi
    have hs : (i + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
    have hz : (l.zip (l.rotate 1))[i]'(by rw [hlen]; exact hi)
        = (l[i]'hi, l[(i + 1) % l.length]'hs) := by
      rw [List.getElem_zip, List.getElem_rotate]
    rw [hz] at heq
    exact ⟨i, hi, hs, (Prod.mk.injEq _ _ _ _).mp heq⟩
  · rintro ⟨i, hi, hs, hu, hv⟩
    refine ⟨i, by rw [hlen]; exact hi, ?_⟩
    have hz : (l.zip (l.rotate 1))[i]'(by rw [hlen]; exact hi)
        = (l[i]'hi, l[(i + 1) % l.length]'hs) := by
      rw [List.getElem_zip, List.getElem_rotate]
    rw [hz, hu, hv]

/-! ### The argmin core: the cyclic successor minimises forward advance -/

/-- **Core** (abstract sorted list). The cyclic successor `l[(i+1) mod k]` of
`l[i]` has the least forward advance from `l[i]` over all other elements. -/
theorem list_core (l : List (Fin n)) (hstrict : List.Pairwise (· < ·) l) (i : ℕ)
    (hi : i < l.length) (hs : (i + 1) % l.length < l.length)
    (j : ℕ) (hj : j < l.length) (hji : j ≠ i) :
    advD (l[i]'hi) (l[(i + 1) % l.length]'hs) ≤ advD (l[i]'hi) (l[j]'hj) := by
  have amono : ∀ p q (hp : p < l.length) (hq : q < l.length),
      p < q → (l[p]'hp : ℕ) < (l[q]'hq : ℕ) :=
    fun p q hp hq hpq => List.pairwise_iff_getElem.mp hstrict p q hp hq hpq
  have amono_le : ∀ p q (hp : p < l.length) (hq : q < l.length),
      p ≤ q → (l[p]'hp : ℕ) ≤ (l[q]'hq : ℕ) := by
    intro p q hp hq hpq
    rcases Nat.eq_or_lt_of_le hpq with h | h
    · subst h; exact le_refl _
    · exact le_of_lt (amono p q hp hq h)
  have hn : 0 < n := by have := (l[i]'hi).isLt; omega
  have hai : (l[i]'hi : ℕ) < n := (l[i]'hi).isLt
  have has : (l[(i + 1) % l.length]'hs : ℕ) < n := (l[(i + 1) % l.length]'hs).isLt
  have haj : (l[j]'hj : ℕ) < n := (l[j]'hj).isLt
  rw [advD_eq_step, advD_eq_step]
  have hspecS := step_spec hn hai has
  have hspecJ := step_spec hn hai haj
  rcases Nat.lt_or_ge (i + 1) l.length with hik | hik
  · -- successor is i+1
    have hse : (i + 1) % l.length = i + 1 := Nat.mod_eq_of_lt hik
    have h_i_s : (l[i]'hi : ℕ) < (l[(i + 1) % l.length]'hs : ℕ) :=
      amono i ((i + 1) % l.length) hi hs (by rw [hse]; omega)
    rcases Nat.lt_or_ge j i with hlt | hge
    · have h_j_i : (l[j]'hj : ℕ) < (l[i]'hi : ℕ) := amono j i hj hi hlt
      omega
    · have hij : i < j := by omega
      have h_s_j : (l[(i + 1) % l.length]'hs : ℕ) ≤ (l[j]'hj : ℕ) :=
        amono_le ((i + 1) % l.length) j hs hj (by rw [hse]; omega)
      omega
  · -- i = k-1, successor is 0
    have hik' : i + 1 = l.length := by omega
    have hse : (i + 1) % l.length = 0 := by rw [hik', Nat.mod_self]
    have hji' : j < i := by omega
    have h_j_i : (l[j]'hj : ℕ) < (l[i]'hi : ℕ) := amono j i hj hi hji'
    have h_s_i : (l[(i + 1) % l.length]'hs : ℕ) < (l[i]'hi : ℕ) :=
      amono ((i + 1) % l.length) i hs hi (by rw [hse]; omega)
    have h_s_j : (l[(i + 1) % l.length]'hs : ℕ) ≤ (l[j]'hj : ℕ) :=
      amono_le ((i + 1) % l.length) j hs hj (by rw [hse]; omega)
    omega

/-- The cyclic successor index differs from the source index (length ≥ 2). -/
theorem idx_succ_ne {l : List (Fin n)} (hk : 2 ≤ l.length) {i : ℕ}
    (hi : i < l.length) : i ≠ (i + 1) % l.length := by
  rcases Nat.lt_or_ge (i + 1) l.length with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have he : i + 1 = l.length := by omega
    rw [he, Nat.mod_self]; omega

/-! ### The argmin characterisation of `consecutiveEdges` -/

/-- **Characterisation.** For `|S| ≥ 2`, `(u,v)` is a consecutive edge of `S` iff
`u,v ∈ S`, `u ≠ v`, and `v` minimises the forward advance `advD u ·` over
`S \ {u}` (the cyclic successor). -/
theorem mem_consecutiveEdges_iff (S : Finset (Fin n)) (h2 : 2 ≤ S.card) (u v : Fin n) :
    (u, v) ∈ consecutiveEdges S ↔
      u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ ∀ w ∈ S, w ≠ u → advD u v ≤ advD u w := by
  have hstrict : List.Pairwise (· < ·) (S.sort (· ≤ ·)) :=
    List.isChain_iff_pairwise.mp (List.SortedLT.isChain (Finset.sortedLT_sort S))
  have hnodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort _
  have hk2 : 2 ≤ (S.sort (· ≤ ·)).length := by rw [hlen]; exact h2
  have hkpos : 0 < (S.sort (· ≤ ·)).length := by omega
  rw [edge_index_mem]
  constructor
  · rintro ⟨i, hi, hs, hui, hvi⟩
    have hidxne : i ≠ (i + 1) % (S.sort (· ≤ ·)).length := idx_succ_ne hk2 hi
    have huS : u ∈ S := by rw [← hui, ← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem hi
    have hvS : v ∈ S := by rw [← hvi, ← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem hs
    have huv : u ≠ v := by
      rw [← hui, ← hvi]; intro hc
      exact hidxne ((List.Nodup.getElem_inj_iff hnodup).mp hc)
    refine ⟨huS, hvS, huv, ?_⟩
    intro w hwS hwu
    obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr hwS)
    have hji : j ≠ i := by
      intro hc; apply hwu; rw [← hjw, ← hui]; subst hc; rfl
    have hcore := list_core _ hstrict i hi hs j hj hji
    rw [hui, hvi, hjw] at hcore
    exact hcore
  · rintro ⟨huS, hvS, huv, hmin⟩
    obtain ⟨i, hi, hui⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr huS)
    have hs : (i + 1) % (S.sort (· ≤ ·)).length < (S.sort (· ≤ ·)).length :=
      Nat.mod_lt _ hkpos
    have hidxne : i ≠ (i + 1) % (S.sort (· ≤ ·)).length := idx_succ_ne hk2 hi
    have hv'S : (S.sort (· ≤ ·))[(i + 1) % (S.sort (· ≤ ·)).length]'hs ∈ S := by
      rw [← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem hs
    have hv'u : (S.sort (· ≤ ·))[(i + 1) % (S.sort (· ≤ ·)).length]'hs ≠ u := by
      rw [← hui]; intro hc
      exact hidxne (((List.Nodup.getElem_inj_iff hnodup).mp hc).symm)
    obtain ⟨jv, hjv, hjvv⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr hvS)
    have hjvi : jv ≠ i := by
      intro hc; apply huv; rw [← hui, ← hjvv]; subst hc; rfl
    have hle1 : advD u ((S.sort (· ≤ ·))[(i + 1) % (S.sort (· ≤ ·)).length]'hs)
        ≤ advD u v := by
      have hcore := list_core _ hstrict i hi hs jv hjv hjvi
      rw [hui, hjvv] at hcore; exact hcore
    have hle2 : advD u v ≤ advD u ((S.sort (· ≤ ·))[(i + 1) % (S.sort (· ≤ ·)).length]'hs) :=
      hmin _ hv'S hv'u
    have hvv' : v = (S.sort (· ≤ ·))[(i + 1) % (S.sort (· ≤ ·)).length]'hs :=
      advD_inj u (le_antisymm hle2 hle1)
    exact ⟨i, hi, hs, hui, hvv'.symm⟩

end Conj43
