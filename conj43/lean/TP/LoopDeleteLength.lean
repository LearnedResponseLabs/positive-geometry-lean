/- SPDX-License-Identifier: Apache-2.0 -/
import TP.LoopDeleteRank

/-! # Deleting a loop lowers the length by the rank

Write the inversions of a period-`m` function as pairs `(i, j)` with `0 ≤ i < m`, `i < j < i + m`, `g j < g i`. For a
loop at `p` of a period-`n + 1` bounded affine permutation `f`, the inversions whose second entry lies outside the
class of `p` correspond bijectively (through `dropPos`) to the inversions of the deleted function, and those whose
second entry lies in the class are counted by a pointwise identity: there are exactly `k` of them. -/

open Finset

namespace TP
namespace LoopDelete

/-- The inversions of a period-`m` function, as pairs `(i, j)`. -/
noncomputable def QJ (m : ℕ) (g : ℤ → ℤ) : Finset (ℤ × ℤ) :=
  ((Ico (0 : ℤ) m) ×ˢ (Ico (0 : ℤ) (2 * m))).filter fun x => x.1 < x.2 ∧ x.2 < x.1 + m ∧ g x.2 < g x.1

lemma mem_QJ {m : ℕ} {g : ℤ → ℤ} {x : ℤ × ℤ} :
    x ∈ QJ m g ↔ 0 ≤ x.1 ∧ x.1 < m ∧ x.1 < x.2 ∧ x.2 < x.1 + m ∧ g x.2 < g x.1 := by
  unfold QJ
  simp only [mem_filter, mem_product, mem_Ico]
  constructor <;> intro h <;> omega

lemma affLength_eq (m : ℕ) (g : ℤ → ℤ) : affLength m g = (QJ m g).card := by
  unfold affLength
  apply Finset.card_bij (fun x _ => ((x.1 : ℤ), (x.1 : ℤ) + x.2))
  · intro x hx
    simp only [mem_filter, mem_product, mem_range] at hx
    rw [mem_QJ]; simp only; omega
  · intro a _ b _ h
    simp only [Prod.ext_iff] at h
    ext <;> omega
  · intro y hy
    rw [mem_QJ] at hy
    refine ⟨(y.1.toNat, (y.2 - y.1).toNat), ?_, ?_⟩
    · simp only [mem_filter, mem_product, mem_range]
      refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
      have e1 : ((y.1.toNat : ℕ) : ℤ) = y.1 := by omega
      have e2 : (((y.2 - y.1).toNat : ℕ) : ℤ) = y.2 - y.1 := by omega
      rw [e1, e2]; simpa using hy.2.2.2.2
    · simp only [Prod.ext_iff]; omega

/-- Integers `j` strictly between `i` and `i + N` in the class of `p`: `j = p` (with `i < p`) or `j = p + N`. -/
lemma j_cases {N p i j : ℤ} (hN : 0 < N) (hp0 : 0 ≤ p) (hpN : p < N) (hi0 : 0 ≤ i) (hiN : i < N)
    (hij : i < j) (hji : j < i + N) (hjp : j % N = p) :
    (j = p ∧ i < p) ∨ (j = p + N ∧ p < i) := by
  have hq := Int.mul_ediv_add_emod j N
  rw [hjp] at hq
  have q0 : 0 ≤ j / N := by
    by_contra h
    have h := not_le.1 h
    have := mul_le_mul_of_nonneg_left (show j / N ≤ -1 by omega) hN.le
    linarith
  have q1 : j / N ≤ 1 := by
    by_contra h
    have h := not_le.1 h
    have := mul_le_mul_of_nonneg_left (show 2 ≤ j / N by omega) hN.le
    linarith
  rcases (show j / N = 0 ∨ j / N = 1 by omega) with h | h
  · rw [h] at hq; left; constructor <;> linarith
  · rw [h] at hq; right; constructor <;> linarith

/-- The pointwise identity behind the count of inversions through the loop. -/
lemma ind_id {N p i v w : ℤ} (hp0 : 0 ≤ p) (hpN : p < N) (_hi0 : 0 ≤ i) (hiN : i < N) (h1 : i ≤ v)
    (h2 : v ≤ i + N) (hw1 : v < N → w = v) (hw2 : N ≤ v → w = v - N) (hfix : i = p → v = p)
    (hback : w = p → i = p) :
    ((if (if i < p then p else p + N) < v then (1 : ℤ) else 0) - (if N ≤ v then 1 else 0)) =
      (if i < p then 1 else 0) - (if w < p then 1 else 0) := by
  split_ifs <;> omega

/-- The unique `j` in the class of `p` with `i < j < i + N` (when it exists). -/
def jpf (N p i : ℤ) : ℤ := if i < p then p else p + N

lemma jpf_cases (N p i : ℤ) : (i < p ∧ jpf N p i = p) ∨ (p ≤ i ∧ jpf N p i = p + N) := by
  unfold jpf; split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨not_lt.1 h, rfl⟩

lemma emod_win {N v : ℤ} (hN : 0 < N) (h0 : 0 ≤ v) (h1 : v < 2 * N) :
    (v < N → v % N = v) ∧ (N ≤ v → v % N = v - N) := by
  constructor
  · intro h; exact Int.emod_eq_of_lt h0 h
  · intro h
    exact (divmod_of hN (x := v) (q := 1) (t := v - N) (by ring) (by omega) (by omega)).2

end LoopDelete

open LoopDelete

/-- **Deleting a loop lowers the length by exactly `k`**: `ℓ(f) = ℓ(f') + k`, the bookkeeping identity of the CLH
paper's remark on loops (`rem:loops`), equivalently the face count of a reduced plabic graph left unchanged by deleting
a lollipop. -/
theorem affLength_deleteLoop {n : ℕ} (hn : 0 < n) (g : BddAffPerm (n + 1)) (p : Fin (n + 1))
    (hp : g.f (p : ℕ) = (p : ℕ)) :
    (affLength (n + 1) g.f : ℤ) = affLength n (deleteLoopFun n p g.f) + affRank (n + 1) g.f := by
  have hpn : (p : ℕ) < n + 1 := p.isLt
  have hN : (0 : ℤ) < (n : ℤ) + 1 := by omega
  have hpn' : (p : ℤ) < (n : ℤ) + 1 := by exact_mod_cast hpn
  have hiff := loop_mod_iff g hpn hp
  obtain ⟨hbij, hper, h0, h1⟩ := deleteLoop_bdd hn g p hp
  set f' := deleteLoopFun n p g.f with hf'
  have key : ∀ y, f' y = dropPos n p (g.f (liftPos n p y)) := fun y => rfl
  have onback : ∀ x, x % ((n : ℤ) + 1) ≠ p → f' (dropPos n p x) = dropPos n p (g.f x) := by
    intro x hx
    rw [key, liftPos_dropPos hn hpn hx]
  have nonpf : ∀ x : ℤ, x % ((n : ℤ) + 1) ≠ p → g.f x % ((n : ℤ) + 1) ≠ p :=
    fun x hx h => hx ((hiff x).1 h)
  have mem1 : ∀ x : ℤ × ℤ, x ∈ QJ (n + 1) g.f ↔ 0 ≤ x.1 ∧ x.1 < (n : ℤ) + 1 ∧ x.1 < x.2 ∧
      x.2 < x.1 + ((n : ℤ) + 1) ∧ g.f x.2 < g.f x.1 := by
    intro x; rw [mem_QJ]; push_cast; rfl
  rw [affLength_eq, affLength_eq, affRank_eq_card (m := n + 1) (Nat.succ_pos n) g.periodic g.bijective.1 g.self_le g.le_add]
  have hsplit := Finset.card_filter_add_card_filter_not (s := QJ (n + 1) g.f)
    (fun x : ℤ × ℤ => x.2 % ((n : ℤ) + 1) = p)
  -- the inversions whose second entry is outside the class correspond to the inversions of f'
  have hQ1 : ((QJ (n + 1) g.f).filter fun x : ℤ × ℤ => ¬ x.2 % ((n : ℤ) + 1) = p).card = (QJ n f').card := by
    apply Finset.card_bij (fun x _ => (dropPos n p x.1, dropPos n p x.2))
    · intro x hx
      simp only [mem_filter, mem1] at hx
      obtain ⟨⟨a0, a1, a2, a3, a4⟩, a5⟩ := hx
      have hi : x.1 % ((n : ℤ) + 1) ≠ p := by
        intro h
        have := loop_class g hp x.1 h
        have := g.self_le x.2
        omega
      have hi2 : (x.1 + ((n : ℤ) + 1)) % ((n : ℤ) + 1) ≠ p := by rw [Int.add_emod_right]; exact hi
      rw [mem_QJ]
      obtain ⟨r0, r1⟩ := dropPos_range hpn hi a0 a1
      refine ⟨r0, by exact_mod_cast r1, (dropPos_lt_iff hn hpn hi a5).2 a2, ?_, ?_⟩
      · have := (dropPos_lt_iff hn hpn a5 hi2).2 a3
        rwa [dropPos_add hn] at this
      · simp only
        rw [onback _ a5, onback _ hi]
        exact (dropPos_lt_iff hn hpn (nonpf _ a5) (nonpf _ hi)).2 a4
    · intro x hx y hy hxy
      simp only [mem_filter, mem1] at hx hy
      obtain ⟨⟨a0, a1, a2, a3, a4⟩, a5⟩ := hx
      obtain ⟨⟨b0, b1, b2, b3, b4⟩, b5⟩ := hy
      have hi : ∀ z : ℤ × ℤ, 0 ≤ z.1 → z.1 < (n : ℤ) + 1 → z.1 < z.2 → g.f z.2 < g.f z.1 →
          z.1 % ((n : ℤ) + 1) ≠ p := by
        intro z z0 z1 z2 z4 h
        have := loop_class g hp z.1 h
        have := g.self_le z.2
        omega
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext (dropPos_injOn hn hpn (hi x a0 a1 a2 a4) (hi y b0 b1 b2 b4) hxy.1)
        (dropPos_injOn hn hpn a5 b5 hxy.2)
    · intro y hy
      rw [mem_QJ] at hy
      obtain ⟨a0, a1, a2, a3, a4⟩ := hy
      obtain ⟨l0, l1⟩ := liftPos_range (p := (p : ℕ)) hn a0 (by exact_mod_cast a1)
      have hb2 : liftPos n p y.2 < liftPos n p y.1 + ((n : ℤ) + 1) := by
        have := liftPos_strictMono (p := (p : ℕ)) hn (show y.2 < y.1 + n from a3)
        rwa [liftPos_add hn] at this
      refine ⟨(liftPos n p y.1, liftPos n p y.2), ?_, ?_⟩
      · simp only [mem_filter, mem1]
        refine ⟨⟨l0, l1, liftPos_strictMono hn a2, hb2, ?_⟩, liftPos_mod_ne hn _⟩
        have e1 := key y.1
        have e2 := key y.2
        have := a4
        rw [e1, e2] at this
        exact (dropPos_lt_iff hn hpn (nonpf _ (liftPos_mod_ne hn _)) (nonpf _ (liftPos_mod_ne hn _))).1 this
      · simp only [dropPos_liftPos hn]
  -- the inversions whose second entry is in the class: one per wrapping position
  have hQ2 : (((QJ (n + 1) g.f).filter fun x : ℤ × ℤ => x.2 % ((n : ℤ) + 1) = p).card : ℤ) =
      (((Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ)).filter fun i => ((n + 1 : ℕ) : ℤ) ≤ g.f i).card : ℤ) := by
    have hjp : ∀ i : ℤ, 0 ≤ i → i < (n : ℤ) + 1 → jpf ((n : ℤ) + 1) p i % ((n : ℤ) + 1) = p := by
      intro i _ _
      rcases jpf_cases ((n : ℤ) + 1) p i with ⟨_, h⟩ | ⟨_, h⟩
      · rw [h]; exact Int.emod_eq_of_lt (by omega) hpn'
      · rw [h, Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) hpn'
    have hB : ((QJ (n + 1) g.f).filter fun x : ℤ × ℤ => x.2 % ((n : ℤ) + 1) = p).card =
        ((Ico (0 : ℤ) ((n : ℤ) + 1)).filter fun i => jpf ((n : ℤ) + 1) p i < g.f i).card := by
      apply Finset.card_bij (fun x _ => x.1)
      · intro x hx
        simp only [mem_filter, mem1] at hx
        obtain ⟨⟨a0, a1, a2, a3, a4⟩, a5⟩ := hx
        simp only [mem_filter, mem_Ico]
        refine ⟨⟨a0, a1⟩, ?_⟩
        have hj := loop_class g hp x.2 a5
        rcases j_cases hN (by omega) hpn' a0 a1 a2 a3 a5 with ⟨c1, c2⟩ | ⟨c1, c2⟩
        · rcases jpf_cases ((n : ℤ) + 1) p x.1 with ⟨_, h⟩ | ⟨h, _⟩
          · omega
          · omega
        · rcases jpf_cases ((n : ℤ) + 1) p x.1 with ⟨h, _⟩ | ⟨_, h⟩
          · omega
          · omega
      · intro x hx y hy hxy
        simp only [mem_filter, mem1] at hx hy
        obtain ⟨⟨a0, a1, a2, a3, a4⟩, a5⟩ := hx
        obtain ⟨⟨b0, b1, b2, b3, b4⟩, b5⟩ := hy
        have hxy' : x.1 = y.1 := hxy
        have hxj : x.2 = jpf ((n : ℤ) + 1) p x.1 := by
          rcases j_cases hN (by omega) hpn' a0 a1 a2 a3 a5 with ⟨c1, c2⟩ | ⟨c1, c2⟩
          · rcases jpf_cases ((n : ℤ) + 1) p x.1 with ⟨_, h⟩ | ⟨h, _⟩
            · omega
            · omega
          · rcases jpf_cases ((n : ℤ) + 1) p x.1 with ⟨h, _⟩ | ⟨_, h⟩
            · omega
            · omega
        have hyj : y.2 = jpf ((n : ℤ) + 1) p y.1 := by
          rcases j_cases hN (by omega) hpn' b0 b1 b2 b3 b5 with ⟨c1, c2⟩ | ⟨c1, c2⟩
          · rcases jpf_cases ((n : ℤ) + 1) p y.1 with ⟨_, h⟩ | ⟨h, _⟩
            · omega
            · omega
          · rcases jpf_cases ((n : ℤ) + 1) p y.1 with ⟨h, _⟩ | ⟨_, h⟩
            · omega
            · omega
        exact Prod.ext hxy' (by rw [hxj, hyj, hxy'])
      · intro i hi
        simp only [mem_filter, mem_Ico] at hi
        obtain ⟨⟨i0, i1⟩, i2⟩ := hi
        have hle := g.le_add i
        have hle' : g.f i ≤ i + ((n : ℤ) + 1) := by push_cast at hle; exact hle
        have hfj := loop_class g hp (jpf ((n : ℤ) + 1) p i) (hjp i i0 i1)
        refine ⟨(i, jpf ((n : ℤ) + 1) p i), ?_, rfl⟩
        simp only [mem_filter, mem1]
        refine ⟨⟨i0, i1, ?_, ?_, ?_⟩, hjp i i0 i1⟩
        · rcases jpf_cases ((n : ℤ) + 1) p i with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
        · rcases jpf_cases ((n : ℤ) + 1) p i with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
        · rcases jpf_cases ((n : ℤ) + 1) p i with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    rw [hB]
    -- the count of positions i whose partner `jp i` lies below `f i` equals the number of wrapping positions
    have hsum : (((Ico (0 : ℤ) ((n : ℤ) + 1)).filter fun i => jpf ((n : ℤ) + 1) p i < g.f i).card : ℤ) -
        (((Ico (0 : ℤ) ((n : ℤ) + 1)).filter fun i => ((n : ℤ) + 1) ≤ g.f i).card : ℤ) = 0 := by
      rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib]
      have hpt : ∀ i ∈ Ico (0 : ℤ) ((n : ℤ) + 1),
          ((if jpf ((n : ℤ) + 1) p i < g.f i then (1 : ℤ) else 0) - (if ((n : ℤ) + 1) ≤ g.f i then 1 else 0)) =
            (if i < (p : ℤ) then 1 else 0) - (if g.f i % ((n : ℤ) + 1) < (p : ℤ) then 1 else 0) := by
        intro i hi
        simp only [mem_Ico] at hi
        have hle := g.le_add i
        have hle' : g.f i ≤ i + ((n : ℤ) + 1) := by push_cast at hle; exact hle
        have hge := g.self_le i
        obtain ⟨w1, w2⟩ := emod_win hN (by omega) (show g.f i < 2 * ((n : ℤ) + 1) by omega)
        refine ind_id (by omega) hpn' hi.1 hi.2 hge hle' w1 w2 ?_ ?_
        · intro h
          have : i % ((n : ℤ) + 1) = p := by rw [Int.emod_eq_of_lt hi.1 hi.2]; exact h
          rw [loop_class g hp i this]; exact h
        · intro h
          have := (hiff i).1 h
          rwa [Int.emod_eq_of_lt hi.1 hi.2] at this
      rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
      have hsc : ∑ i ∈ Ico (0 : ℤ) ((n : ℤ) + 1), (if g.f i % ((n : ℤ) + 1) < (p : ℤ) then (1 : ℤ) else 0) =
          ∑ i ∈ Ico (0 : ℤ) ((n : ℤ) + 1), (if i < (p : ℤ) then (1 : ℤ) else 0) :=
        sum_comp_mod hN (g := g.f) (BddAffPerm.perSucc g) g.bijective.1 (fun t => if t < (p : ℤ) then (1 : ℤ) else 0)
      rw [hsc]; ring
    push_cast at hsum ⊢
    linarith
  omega

end TP
