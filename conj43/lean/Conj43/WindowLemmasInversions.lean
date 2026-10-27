/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.WindowLemmasBridges

/-!
The paper's inversion measure. Split the ordered-pair sum at the two swapped
positions. Exterior positions see the same two values; each interior fixed
position has a lift below both values or above both. Only the pair (a,b)
changes. The generic sum split adapts `Window.measure_split` (Apache-2.0).
-/
namespace Conj43.WindowLemmas
variable {n : ℕ}
open scoped BigOperators

def invTerm (w : Fin n → ℕ) (i j : Fin n) : ℕ :=
  if i < j ∧ w j < w i then 1 else 0

theorem invLift_eq_sum (w : Fin n → ℕ) :
    invLift w = ∑ i : Fin n, ∑ j : Fin n, invTerm w i j := by
  unfold invLift invTerm
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]

theorem sum_split_two (a b : Fin n) (hab : a ≠ b) (f : Fin n → ℕ) :
    (∑ i : Fin n, f i) = (∑ i ∈ (Finset.univ.erase a).erase b, f i) + (f a + f b) := by
  have hb : b ∈ Finset.univ.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ a),
    ← Finset.sum_erase_add (Finset.univ.erase a) f hb]
  omega

theorem invLift_split (w : Fin n → ℕ) (a b : Fin n) (hab : a < b) :
    invLift w =
      (∑ i ∈ (Finset.univ.erase a).erase b,
        ∑ j ∈ (Finset.univ.erase a).erase b, invTerm w i j) +
      (∑ r ∈ (Finset.univ.erase a).erase b,
        (invTerm w a r + invTerm w b r + invTerm w r a + invTerm w r b)) +
      (if w b < w a then 1 else 0) := by
  rw [invLift_eq_sum]
  simp_rw [sum_split_two a b (ne_of_lt hab)]
  simp only [Finset.sum_add_distrib]
  have haa : invTerm w a a = 0 := by simp [invTerm]
  have hbb : invTerm w b b = 0 := by simp [invTerm]
  have hba : invTerm w b a = 0 := by simp [invTerm, not_lt_of_ge hab.le]
  have hab' : invTerm w a b = if w b < w a then 1 else 0 := by simp [invTerm, hab]
  rw [haa, hbb, hba, hab']
  omega

theorem swap_incident_sum (w : Fin n → ℕ) {a b r : Fin n}
    (hab : a < b) (hra : r ≠ a) (hrb : r ≠ b) (hasc : w a < w b)
    (hgap : a < r → r < b → w r < w a ∨ w b < w r) :
    invTerm (swapLift w a b) a r + invTerm (swapLift w a b) b r +
        invTerm (swapLift w a b) r a + invTerm (swapLift w a b) r b =
      invTerm w a r + invTerm w b r + invTerm w r a + invTerm w r b := by
  have habne := ne_of_lt hab
  have hg_a : swapLift w a b a = w b := by simp [swapLift]
  have hg_b : swapLift w a b b = w a := by simp [swapLift, Ne.symm habne]
  have hg_r : swapLift w a b r = w r := by simp [swapLift, hra, hrb]
  unfold invTerm
  rw [hg_a, hg_b, hg_r]
  rcases lt_trichotomy r a with hleft | heq | hright
  · have hrb' : r < b := lt_trans hleft hab
    simp only [not_lt_of_ge hleft.le, not_lt_of_ge hrb'.le, hleft, hrb',
      false_and, true_and, if_false, zero_add]
    omega
  · exact (hra heq).elim
  · rcases lt_trichotomy r b with hmiddle | heq | hright'
    · rcases hgap hright hmiddle with hlow | hhigh
      · have hlow' : w r < w b := lt_trans hlow hasc
        simp [hright, hmiddle, not_lt_of_ge hright.le, not_lt_of_ge hmiddle.le,
          hlow, hlow', not_lt_of_ge hlow.le, not_lt_of_ge hlow'.le]
      · have hhigh' : w a < w r := lt_trans hasc hhigh
        simp [hright, hmiddle, not_lt_of_ge hright.le, not_lt_of_ge hmiddle.le,
          hhigh, hhigh', not_lt_of_ge hhigh.le, not_lt_of_ge hhigh'.le]
    · exact (hrb heq).elim
    · simp only [hright, hright', not_lt_of_ge hright.le, not_lt_of_ge hright'.le,
        false_and, true_and, if_false, add_zero]
      omega

theorem invLift_swap_add_one (W : DWindow n) {a b : Fin n}
    (h : IsAdjacentAscent W a b) :
    invLift (swapLift W.w a b) = invLift W.w + 1 := by
  let R : Finset (Fin n) := (Finset.univ.erase a).erase b
  have hs : ∀ r ∈ R, swapLift W.w a b r = W.w r := by
    intro r hr
    obtain ⟨hrb,hra⟩ := Finset.mem_erase.mp hr
    have hra' := (Finset.mem_erase.mp hra).1
    simp [swapLift, hrb, hra']
  have hinterior : (∑ i ∈ R, ∑ j ∈ R, invTerm (swapLift W.w a b) i j) =
      ∑ i ∈ R, ∑ j ∈ R, invTerm W.w i j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [invTerm, hs i hi, hs j hj]
  have hincident : (∑ r ∈ R, (invTerm (swapLift W.w a b) a r +
      invTerm (swapLift W.w a b) b r + invTerm (swapLift W.w a b) r a +
      invTerm (swapLift W.w a b) r b)) =
      ∑ r ∈ R, (invTerm W.w a r + invTerm W.w b r + invTerm W.w r a + invTerm W.w r b) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrb := (Finset.mem_erase.mp hr).1
    have hra := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    exact swap_incident_sum W.w h.1 hra hrb h.2.2.2.2 (middle_lift_outside W h)
  rw [invLift_split _ a b h.1, invLift_split _ a b h.1]
  change _ + _ + _ = _ + _ + _ + 1
  rw [hinterior, hincident]
  have hga : swapLift W.w a b a = W.w b := by simp [swapLift]
  have hgb : swapLift W.w a b b = W.w a := by simp [swapLift, Ne.symm (ne_of_lt h.1)]
  rw [hga, hgb, if_pos h.2.2.2.2, if_neg (not_lt_of_ge h.2.2.2.2.le)]

theorem invLift_le_choose (w : Fin n → ℕ) : invLift w ≤ n.choose 2 := by
  classical
  let I := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1
  have hle : I.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard 2).card := by
    apply Finset.card_le_card_of_injOn (fun p : Fin n × Fin n => ({p.1,p.2} : Finset (Fin n)))
    · intro p hp
      have hlt := (Finset.mem_filter.mp hp).2.1
      simp [Finset.mem_powersetCard, ne_of_lt hlt]
    · intro p hp q hq heq
      change ({p.1,p.2} : Finset (Fin n)) = {q.1,q.2} at heq
      have hplt := (Finset.mem_filter.mp hp).2.1
      have hqlt := (Finset.mem_filter.mp hq).2.1
      have h1 : p.1 = q.1 ∨ p.1 = q.2 := by
        have hm : p.1 ∈ ({q.1,q.2} : Finset (Fin n)) := by rw [← heq]; simp
        simpa using hm
      have h2 : p.2 = q.1 ∨ p.2 = q.2 := by
        have hm : p.2 ∈ ({q.1,q.2} : Finset (Fin n)) := by rw [← heq]; simp
        simpa using hm
      apply Prod.ext <;> apply Fin.ext <;>
        simp only [Fin.lt_def, Fin.ext_iff] at hplt hqlt h1 h2 ⊢ <;> omega
  simpa [I, invLift, Finset.card_powersetCard] using hle

end Conj43.WindowLemmas
