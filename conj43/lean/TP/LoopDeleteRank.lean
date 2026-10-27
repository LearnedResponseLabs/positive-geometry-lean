/- SPDX-License-Identifier: Apache-2.0 -/
import TP.LoopDeleteBdd

/-! # Deleting a loop keeps the rank

The rank of a bounded affine permutation of period `m` is the number of window positions `i ∈ [0, m)` with
`m ≤ f i` (the wrapping positions); deleting a loop (which never wraps) removes no wrapping position. -/

open Finset

namespace TP
namespace LoopDelete

lemma sum_range_cast (F : ℤ → ℤ) (m : ℕ) : ∑ i ∈ range m, F (i : ℤ) = ∑ i ∈ Ico (0 : ℤ) m, F i := by
  apply Finset.sum_bij (fun (i : ℕ) _ => (i : ℤ))
  · intro a ha; simp only [mem_range] at ha; simp only [mem_Ico]; omega
  · intro a _ b _ h; exact_mod_cast h
  · intro b hb; simp only [mem_Ico] at hb
    exact ⟨b.toNat, by simp only [mem_range]; omega, by omega⟩
  · intros; rfl

/-- Residues of the values of a periodic injective function on a window are a permutation of the window. -/
lemma sum_comp_mod {m : ℤ} (hm : 0 < m) {g : ℤ → ℤ} (hper : ∀ i, g (i + m) = g i + m)
    (hinj : Function.Injective g) (h : ℤ → ℤ) :
    ∑ i ∈ Ico (0 : ℤ) m, h (g i % m) = ∑ i ∈ Ico (0 : ℤ) m, h i := by
  have hinjOn : Set.InjOn (fun i => g i % m) (Ico (0 : ℤ) m) := by
    intro i hi j hj hij
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    simp only at hij
    have h1 := Int.mul_ediv_add_emod (g i) m
    have h2 := Int.mul_ediv_add_emod (g j) m
    have h3 := per_int hper j (g i / m - g j / m)
    have h4 : g i = g (j + m * (g i / m - g j / m)) := by rw [h3]; nlinarith
    have h5 := hinj h4
    have h6 : i % m = j % m := by
      rw [h5, Int.add_mul_emod_self_left]
    rwa [Int.emod_eq_of_lt hi.1 hi.2, Int.emod_eq_of_lt hj.1 hj.2] at h6
  have hsub : (Ico (0 : ℤ) m).image (fun i => g i % m) ⊆ Ico (0 : ℤ) m := by
    intro x hx
    simp only [mem_image, mem_Ico] at hx ⊢
    obtain ⟨i, _, rfl⟩ := hx
    exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
  have hcard := Finset.card_image_of_injOn hinjOn
  have heq : (Ico (0 : ℤ) m).image (fun i => g i % m) = Ico (0 : ℤ) m :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
  calc ∑ i ∈ Ico (0 : ℤ) m, h (g i % m) = ∑ x ∈ (Ico (0 : ℤ) m).image (fun i => g i % m), h x :=
        (Finset.sum_image hinjOn).symm
    _ = ∑ i ∈ Ico (0 : ℤ) m, h i := by rw [heq]

/-- The rank is the number of wrapping window positions. -/
lemma affRank_eq_card {m : ℕ} (hm : 0 < m) {g : ℤ → ℤ} (hper : ∀ i, g (i + m) = g i + m)
    (hinj : Function.Injective g) (h0 : ∀ i, i ≤ g i) (h1 : ∀ i, g i ≤ i + m) :
    affRank m g = (((Ico (0 : ℤ) m).filter fun i => (m : ℤ) ≤ g i).card : ℤ) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  unfold affRank
  have hs : ∑ i ∈ range m, (g (i : ℤ) - (i : ℤ)) = ∑ i ∈ Ico (0 : ℤ) m, (g i - i) :=
    sum_range_cast (fun i => g i - i) m
  rw [hs]
  have hdiv : ∀ i ∈ Ico (0 : ℤ) m, g i / m = if (m : ℤ) ≤ g i then 1 else 0 := by
    intro i hi
    simp only [mem_Ico] at hi
    have a := h0 i
    have b := h1 i
    split_ifs with h
    · exact (divmod_of hm' (x := g i) (q := 1) (t := g i - m) (by ring) (by omega) (by omega)).1
    · exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have hsum : ∑ i ∈ Ico (0 : ℤ) m, (g i - i) = m * ∑ i ∈ Ico (0 : ℤ) m, g i / m := by
    have e : ∀ i, g i - i = g i % m - i + m * (g i / m) := fun i => by
      have := Int.mul_ediv_add_emod (g i) m; linarith
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_comp_mod hm' hper hinj (fun x => x), ← Finset.mul_sum]
    simp
  rw [hsum, Finset.sum_congr rfl hdiv, Finset.sum_boole]
  exact Int.mul_ediv_cancel_left _ hm'.ne'

end LoopDelete

open LoopDelete

/-- **Deleting a loop keeps the rank** `k`. -/
theorem affRank_deleteLoop {n : ℕ} (hn : 0 < n) (g : BddAffPerm (n + 1)) (p : Fin (n + 1))
    (hp : g.f (p : ℕ) = (p : ℕ)) :
    affRank n (deleteLoopFun n p g.f) = affRank (n + 1) g.f := by
  have hpn : (p : ℕ) < n + 1 := p.isLt
  have hiff := loop_mod_iff g hpn hp
  obtain ⟨hbij, hper, h0, h1⟩ := deleteLoop_bdd hn g p hp
  rw [affRank_eq_card hn (by simpa using hper) hbij.1 h0 (by simpa using h1),
    affRank_eq_card (Nat.succ_pos n) g.periodic g.bijective.1 g.self_le g.le_add]
  congr 1
  push_cast
  symm
  apply Finset.card_bij (fun i _ => dropPos n p i)
  · intro a ha
    simp only [mem_filter, mem_Ico] at ha ⊢
    obtain ⟨⟨ha0, ha1⟩, ha2⟩ := ha
    have hap : a % ((n : ℤ) + 1) ≠ p := by
      intro h
      have := loop_class g hp a h
      omega
    have hfa : g.f a % ((n : ℤ) + 1) ≠ p := fun h => hap ((hiff a).1 h)
    obtain ⟨r0, r1⟩ := dropPos_range hpn hap ha0 ha1
    refine ⟨⟨r0, r1⟩, ?_⟩
    have e : deleteLoopFun n p g.f (dropPos n p a) = dropPos n p (g.f a) := by
      show dropPos n p (g.f (liftPos n p (dropPos n p a))) = _
      rw [liftPos_dropPos hn hpn hap]
    rw [e]
    obtain ⟨s, s0, s1, hs⟩ := dropPos_shape hpn hfa
    rw [hs]
    have : 1 ≤ g.f a / ((n : ℤ) + 1) := (Int.le_ediv_iff_mul_le (by omega)).2 (by linarith)
    nlinarith
  · intro a ha b hb hab
    simp only [mem_filter, mem_Ico] at ha hb
    have nonp : ∀ x : ℤ, 0 ≤ x → x < (n : ℤ) + 1 → (n : ℤ) + 1 ≤ g.f x → x % ((n : ℤ) + 1) ≠ p := by
      intro x hx0 hx1 hx2 h
      have := loop_class g hp x h
      omega
    exact dropPos_injOn hn hpn (nonp a ha.1.1 ha.1.2 ha.2) (nonp b hb.1.1 hb.1.2 hb.2) hab
  · intro y hy
    simp only [mem_filter, mem_Ico] at hy
    obtain ⟨⟨hy0, hy1⟩, hy2⟩ := hy
    obtain ⟨l0, l1⟩ := liftPos_range (p := (p : ℕ)) hn hy0 hy1
    refine ⟨liftPos n p y, ?_, dropPos_liftPos hn y⟩
    simp only [mem_filter, mem_Ico]
    refine ⟨⟨l0, l1⟩, ?_⟩
    have hfa : g.f (liftPos n p y) % ((n : ℤ) + 1) ≠ p := fun h => liftPos_mod_ne hn y ((hiff _).1 h)
    obtain ⟨s, s0, s1, hs⟩ := dropPos_shape hpn hfa
    have e : deleteLoopFun n p g.f y = dropPos n p (g.f (liftPos n p y)) := rfl
    rw [e, hs] at hy2
    by_contra hlt
    have : g.f (liftPos n p y) / ((n : ℤ) + 1) ≤ 0 := by
      have := (Int.ediv_lt_iff_lt_mul (by omega : (0 : ℤ) < (n : ℤ) + 1)).2 (show g.f (liftPos n p y) < 1 * ((n : ℤ) + 1) by omega)
      omega
    nlinarith

end TP
