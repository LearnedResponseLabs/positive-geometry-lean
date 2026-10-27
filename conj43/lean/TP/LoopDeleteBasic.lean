/- SPDX-License-Identifier: Apache-2.0 -/
import TP.LoopDeleteDefs

/-! # Deleting a loop: arithmetic of `dropPos` and `liftPos`

With `N = n + 1` and the residue class `p` modulo `N` removed, `dropPos n p` is the order-preserving bijection from
the integers outside the class onto `ℤ`, and `liftPos n p` is its inverse; both commute with the shift by one period. -/

namespace TP
namespace LoopDelete

lemma divmod_of {N q t x : ℤ} (hN : 0 < N) (h : x = N * q + t) (h0 : 0 ≤ t) (h1 : t < N) :
    x / N = q ∧ x % N = t :=
  (Int.ediv_emod_unique hN).2 ⟨by linarith, h0, h1⟩

variable {n p : ℕ}

lemma liftPos_eq (n p : ℕ) (y : ℤ) :
    liftPos n p y = ((n : ℤ) + 1) * (y / n) + (if y % n < p then y % n else y % n + 1) := by
  unfold liftPos; ring

lemma dropPos_eq (n p : ℕ) (x : ℤ) :
    dropPos n p x = (n : ℤ) * (x / ((n : ℤ) + 1)) + (if x % ((n : ℤ) + 1) < p then x % ((n : ℤ) + 1)
      else x % ((n : ℤ) + 1) - 1) := by
  unfold dropPos; ring

lemma liftPos_divmod (hn : 0 < n) (y : ℤ) :
    liftPos n p y / ((n : ℤ) + 1) = y / n ∧
      liftPos n p y % ((n : ℤ) + 1) = (if y % n < p then y % n else y % n + 1) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ y % (n : ℤ) := Int.emod_nonneg _ hn'.ne'
  have h1 : y % (n : ℤ) < n := Int.emod_lt_of_pos _ hn'
  apply divmod_of (by omega) (liftPos_eq n p y)
  · split_ifs <;> omega
  · split_ifs <;> omega

lemma liftPos_mod_ne (hn : 0 < n) (y : ℤ) : liftPos n p y % ((n : ℤ) + 1) ≠ p := by
  rw [(liftPos_divmod (p := p) hn y).2]; split_ifs <;> omega

lemma dropPos_liftPos (hn : 0 < n) (y : ℤ) : dropPos n p (liftPos n p y) = y := by
  obtain ⟨h1, h2⟩ := liftPos_divmod (p := p) hn y
  rw [dropPos_eq, h1, h2]
  have := Int.mul_ediv_add_emod y n
  split_ifs <;> omega

/-- `dropPos` of an integer outside the class: its quotient and an in-range remainder. -/
lemma dropPos_shape (hp : p < n + 1) {x : ℤ} (hx : x % ((n : ℤ) + 1) ≠ p) :
    ∃ s : ℤ, 0 ≤ s ∧ s < n ∧ dropPos n p x = (n : ℤ) * (x / ((n : ℤ) + 1)) + s := by
  have h0 : 0 ≤ x % ((n : ℤ) + 1) := Int.emod_nonneg _ (by omega)
  have h1 : x % ((n : ℤ) + 1) < (n : ℤ) + 1 := Int.emod_lt_of_pos _ (by omega)
  rw [dropPos_eq]
  have hp' : (p : ℤ) < n + 1 := by exact_mod_cast hp
  by_cases h : x % ((n : ℤ) + 1) < p
  · exact ⟨x % ((n : ℤ) + 1), h0, by omega, by rw [if_pos h]⟩
  · exact ⟨x % ((n : ℤ) + 1) - 1, by omega, by omega, by rw [if_neg h]⟩

lemma liftPos_dropPos (hn : 0 < n) (hp : p < n + 1) {x : ℤ} (hx : x % ((n : ℤ) + 1) ≠ p) :
    liftPos n p (dropPos n p x) = x := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hp' : (p : ℤ) < n + 1 := by exact_mod_cast hp
  have h0 : 0 ≤ x % ((n : ℤ) + 1) := Int.emod_nonneg _ (by omega)
  have h1 : x % ((n : ℤ) + 1) < (n : ℤ) + 1 := Int.emod_lt_of_pos _ (by omega)
  have hx' := Int.mul_ediv_add_emod x ((n : ℤ) + 1)
  by_cases h : x % ((n : ℤ) + 1) < p
  · have hd : dropPos n p x = (n : ℤ) * (x / ((n : ℤ) + 1)) + x % ((n : ℤ) + 1) := by
      rw [dropPos_eq, if_pos h]
    obtain ⟨e1, e2⟩ := divmod_of (N := (n : ℤ)) (q := x / ((n : ℤ) + 1)) (t := x % ((n : ℤ) + 1)) hn'
      (x := dropPos n p x) (by rw [hd]) h0 (by omega)
    rw [liftPos_eq, e1, e2, if_pos h]; linarith
  · have hd : dropPos n p x = (n : ℤ) * (x / ((n : ℤ) + 1)) + (x % ((n : ℤ) + 1) - 1) := by
      rw [dropPos_eq, if_neg h]
    obtain ⟨e1, e2⟩ := divmod_of (N := (n : ℤ)) (q := x / ((n : ℤ) + 1)) (t := x % ((n : ℤ) + 1) - 1) hn'
      (x := dropPos n p x) (by rw [hd]) (by omega) (by omega)
    rw [liftPos_eq, e1, e2, if_neg (by omega)]; linarith

lemma liftPos_add (hn : 0 < n) (y : ℤ) : liftPos n p (y + n) = liftPos n p y + ((n : ℤ) + 1) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have e1 : (y + n) / (n : ℤ) = y / n + 1 := by
    rw [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self hn'.ne']
  have e2 : (y + n) % (n : ℤ) = y % n := Int.add_emod_right y n
  rw [liftPos_eq, liftPos_eq, e1, e2]; ring

lemma dropPos_add (hn : 0 < n) (x : ℤ) :
    dropPos n p (x + ((n : ℤ) + 1)) = dropPos n p x + n := by
  have hN : (0 : ℤ) < (n : ℤ) + 1 := by omega
  have e1 : (x + ((n : ℤ) + 1)) / ((n : ℤ) + 1) = x / ((n : ℤ) + 1) + 1 := by
    rw [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self hN.ne']
  have e2 : (x + ((n : ℤ) + 1)) % ((n : ℤ) + 1) = x % ((n : ℤ) + 1) := Int.add_emod_right x _
  rw [dropPos_eq, dropPos_eq, e1, e2]; ring

lemma liftPos_strictMono (hn : 0 < n) {y y' : ℤ} (h : y < y') : liftPos n p y < liftPos n p y' := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have a0 : 0 ≤ y % (n : ℤ) := Int.emod_nonneg _ hn'.ne'
  have a1 : y % (n : ℤ) < n := Int.emod_lt_of_pos _ hn'
  have b0 : 0 ≤ y' % (n : ℤ) := Int.emod_nonneg _ hn'.ne'
  have b1 : y' % (n : ℤ) < n := Int.emod_lt_of_pos _ hn'
  have hy := Int.mul_ediv_add_emod y n
  have hy' := Int.mul_ediv_add_emod y' n
  rw [liftPos_eq, liftPos_eq]
  have hq : y / (n : ℤ) ≤ y' / n := Int.ediv_le_ediv hn' h.le
  rcases hq.lt_or_eq with hq | hq
  · have : ((n : ℤ) + 1) * (y / n + 1) ≤ ((n : ℤ) + 1) * (y' / n) :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    split_ifs <;> nlinarith
  · rw [← hq] at hy' ⊢
    have : y % (n : ℤ) < y' % n := by nlinarith
    split_ifs <;> omega

lemma liftPos_range (hn : 0 < n) {y : ℤ} (h0 : 0 ≤ y) (h1 : y < n) :
    0 ≤ liftPos n p y ∧ liftPos n p y < (n : ℤ) + 1 := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have e1 : y / (n : ℤ) = 0 := Int.ediv_eq_zero_of_lt h0 h1
  have e2 : y % (n : ℤ) = y := Int.emod_eq_of_lt h0 h1
  rw [liftPos_eq, e1, e2]; split_ifs <;> omega

lemma dropPos_range (hp : p < n + 1) {x : ℤ} (hx : x % ((n : ℤ) + 1) ≠ p) (h0 : 0 ≤ x) (h1 : x < (n : ℤ) + 1) :
    0 ≤ dropPos n p x ∧ dropPos n p x < n := by
  have e1 : x / ((n : ℤ) + 1) = 0 := Int.ediv_eq_zero_of_lt h0 h1
  obtain ⟨s, hs0, hs1, hs⟩ := dropPos_shape hp hx
  rw [hs, e1]; constructor <;> omega

/-- Outside the class, `dropPos` preserves and reflects `≤`. -/
lemma dropPos_le_iff (hn : 0 < n) (hp : p < n + 1) {x z : ℤ} (hx : x % ((n : ℤ) + 1) ≠ p)
    (hz : z % ((n : ℤ) + 1) ≠ p) : dropPos n p x ≤ dropPos n p z ↔ x ≤ z := by
  have ex := liftPos_dropPos (p := p) hn hp hx
  have ez := liftPos_dropPos (p := p) hn hp hz
  constructor
  · intro h
    rcases h.lt_or_eq with h | h
    · have := liftPos_strictMono (p := p) hn h
      omega
    · rw [← ex, ← ez, h]
  · intro h
    by_contra hc
    have := liftPos_strictMono (p := p) hn (not_le.1 hc)
    omega

lemma dropPos_lt_iff (hn : 0 < n) (hp : p < n + 1) {x z : ℤ} (hx : x % ((n : ℤ) + 1) ≠ p)
    (hz : z % ((n : ℤ) + 1) ≠ p) : dropPos n p x < dropPos n p z ↔ x < z := by
  rw [← not_le, ← not_le, dropPos_le_iff hn hp hz hx]

lemma dropPos_injOn (hn : 0 < n) (hp : p < n + 1) {x z : ℤ} (hx : x % ((n : ℤ) + 1) ≠ p)
    (hz : z % ((n : ℤ) + 1) ≠ p) (h : dropPos n p x = dropPos n p z) : x = z :=
  le_antisymm ((dropPos_le_iff hn hp hx hz).1 h.le) ((dropPos_le_iff hn hp hz hx).1 h.ge)

end LoopDelete
end TP
