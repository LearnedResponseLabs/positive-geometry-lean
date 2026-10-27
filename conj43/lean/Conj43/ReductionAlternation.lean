/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionCircle
namespace Conj43
namespace Reduction
variable {n : ℕ}

lemma entry_arc_exit_target (F : LooplessBAP n) {u v : Fin n} (huv : u ≠ v) :
    insideArc (5*n) (entryPos F u) (entryPos F v) (exitPos (F.σ.symm v)) := by
  rw [inside_cases (entry_lt F u) (entry_lt F v) (exit_lt _), entry_eq, entry_eq]
  have hn : (F.σ.symm u).val ≠ (F.σ.symm v).val :=
    fun h => huv (F.σ.symm.injective (Fin.ext h))
  unfold exitPos
  omega

lemma entry_arc_to_exit (F : LooplessBAP n) {u v r : Fin n}
    (h : insideArc (5*n) (entryPos F u) (entryPos F v) (entryPos F r)) :
    insideArc (5*n) (entryPos F u) (entryPos F v) (exitPos (F.σ.symm r)) ∧
      F.σ.symm r ≠ F.σ.symm v := by
  rw [inside_cases (entry_lt F u) (entry_lt F v) (entry_lt F r), entry_eq, entry_eq, entry_eq] at h
  constructor
  · rw [inside_cases (entry_lt F u) (entry_lt F v) (exit_lt _), entry_eq, entry_eq]
    unfold exitPos
    omega
  · intro he
    have he' := congrArg Fin.val he
    omega

/-- Each arc between distinct surviving entries contains a surviving exit.
Otherwise inverse permutation injects its exits into the same finite set minus one point. -/
lemma surviving_exit_between (F : LooplessBAP n) (p : Fin n) {u v : Fin n}
    (hu : u ∈ component F p) (hv : v ∈ component F p) (huv : u ≠ v) :
    ∃ r ∈ component F p, insideArc (5*n) (entryPos F u) (entryPos F v) (exitPos r) := by
  classical
  by_contra! hn
  let S := Finset.univ.filter (fun r : Fin n =>
    insideArc (5*n) (entryPos F u) (entryPos F v) (exitPos r))
  have ht : F.σ.symm v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, entry_arc_exit_target F huv⟩
  have hmap : S.image F.σ.symm ⊆ S.erase (F.σ.symm v) := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    have harc := (Finset.mem_filter.mp hr).2
    have hrout : r ∉ component F p := fun h => hn r h harc
    have he := (outside_entry_arc F p hrout hu hv).mpr harc
    obtain ⟨hinside, hne⟩ := entry_arc_to_exit F he
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinside⟩⟩
  have hc := Finset.card_le_card hmap
  rw [Finset.card_image_of_injective S F.σ.symm.injective, Finset.card_erase_of_mem ht] at hc
  have hp := Finset.card_pos.mpr ⟨_, ht⟩
  omega

def entryCount (F : LooplessBAP n) (C : Finset (Fin n)) (u : Fin n) : ℕ :=
  (C.filter (· ≤ F.σ.symm u)).card

lemma entryCount_le (F : LooplessBAP n) (C : Finset (Fin n)) (u : Fin n) :
    entryCount F C u ≤ C.card := Finset.card_filter_le _ _

lemma entryCount_mono (F : LooplessBAP n) (C : Finset (Fin n)) {u v : Fin n}
    (h : F.σ.symm u ≤ F.σ.symm v) : entryCount F C u ≤ entryCount F C v := by
  apply Finset.card_le_card
  intro r hr
  obtain ⟨hrC, hr⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hrC, hr.trans h⟩

lemma entryCount_lt (F : LooplessBAP n) (p : Fin n) {u v : Fin n}
    (hu : u ∈ component F p) (hv : v ∈ component F p) (hlt : F.σ.symm u < F.σ.symm v) :
    entryCount F (component F p) u < entryCount F (component F p) v := by
  have huv : u ≠ v := fun h => (ne_of_lt hlt) (congrArg F.σ.symm h)
  obtain ⟨r, hrC, hr⟩ := surviving_exit_between F p hu hv huv
  rw [inside_cases (entry_lt F u) (entry_lt F v) (exit_lt r), entry_eq, entry_eq] at hr
  have hrr : F.σ.symm u < r ∧ r ≤ F.σ.symm v := by
    simp only [exitPos] at hr
    change (F.σ.symm u).val < (F.σ.symm v).val at hlt
    constructor
    · change (F.σ.symm u).val < r.val; omega
    · change r.val ≤ (F.σ.symm v).val; omega
  apply Finset.card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxC, hx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxC, hx.trans hlt.le⟩
  · intro he
    have hx : r ∈ (component F p).filter (· ≤ F.σ.symm v) := Finset.mem_filter.mpr ⟨hrC,hrr.2⟩
    rw [← he] at hx
    exact (not_le_of_gt hrr.1) (Finset.mem_filter.mp hx).2

lemma entryCount_not_zero_full (F : LooplessBAP n) (p : Fin n) {u v : Fin n}
    (hu : u ∈ component F p) (hv : v ∈ component F p) (hlt : F.σ.symm u < F.σ.symm v) :
    ¬ (entryCount F (component F p) u = 0 ∧
      entryCount F (component F p) v = (component F p).card) := by
  rintro ⟨hzero,hfull⟩
  have huv : v ≠ u := fun h => (ne_of_lt hlt) (congrArg F.σ.symm h.symm)
  obtain ⟨r, hrC, hr⟩ := surviving_exit_between F p hv hu huv
  have he : (component F p).filter (· ≤ F.σ.symm v) = component F p :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (le_of_eq hfull.symm)
  have hrmem : r ∈ (component F p).filter (· ≤ F.σ.symm v) := by rw [he]; exact hrC
  have hrle : r ≤ F.σ.symm v := (Finset.mem_filter.mp hrmem).2
  have hrnot : ¬ r ≤ F.σ.symm u := by
    intro h
    have hmem : r ∈ (component F p).filter (· ≤ F.σ.symm u) := Finset.mem_filter.mpr ⟨hrC,h⟩
    have hc : 0 < entryCount F (component F p) u := Finset.card_pos.mpr ⟨r,hmem⟩
    omega
  rw [inside_cases (entry_lt F v) (entry_lt F u) (exit_lt r), entry_eq, entry_eq] at hr
  simp only [exitPos] at hr
  simp only [Fin.le_def, Fin.lt_def] at hlt hrle hrnot
  omega

lemma entry_index_formula {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) :
    (k+m-1)%m = if k=0 then m-1 else k-1 := by
  by_cases h : k=0
  · simp only [h, zero_add, ite_true]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg h]
    have he : k+m-1 = (k-1)+m := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma entryMapOn_ne_of_inv_lt (F : LooplessBAP n) (p : Fin n)
    (i j : Fin (component F p).card)
    (hlt : F.σ.symm (labelsOf (component F p) i) < F.σ.symm (labelsOf (component F p) j)) :
    entryMapOn F (component F p) i ≠ entryMapOn F (component F p) j := by
  intro h
  have hi := reduction_labels_mem (component F p) i
  have hj := reduction_labels_mem (component F p) j
  have hstrict := entryCount_lt F p hi hj hlt
  have hn := entryCount_not_zero_full F p hi hj hlt
  have hle1 := entryCount_le F (component F p) (labelsOf (component F p) i)
  have hle2 := entryCount_le F (component F p) (labelsOf (component F p) j)
  have he := congrArg Fin.val h
  change (entryCount F (component F p) (labelsOf (component F p) i) + (component F p).card - 1) %
      (component F p).card =
    (entryCount F (component F p) (labelsOf (component F p) j) + (component F p).card - 1) %
      (component F p).card at he
  rw [entry_index_formula i.pos hle1, entry_index_formula i.pos hle2] at he
  split_ifs at he <;> omega

end Reduction

/-- Surviving entries alternate with the ordered surviving exits. -/
theorem restrictEntry_bijective (F : LooplessBAP n) (p : Fin n) :
    Function.Bijective (restrictEntry F p) := by
  apply (Finite.injective_iff_bijective).mp
  intro i j hij
  by_contra hne
  have hn : F.σ.symm (labelsOf (component F p) i) ≠ F.σ.symm (labelsOf (component F p) j) :=
    fun h => hne ((labelsOf (component F p)).injective (F.σ.symm.injective h))
  rcases lt_or_gt_of_ne hn with hlt | hlt
  · exact Reduction.entryMapOn_ne_of_inv_lt F p i j hlt hij
  · exact Reduction.entryMapOn_ne_of_inv_lt F p j i hlt hij.symm

theorem restrictBAP_inv (F : LooplessBAP n) (p : Fin n) (j : Fin (component F p).card) :
    (restrictBAP F p).σ⁻¹ j = restrictEntry F p j := by
  unfold restrictBAP
  rw [dif_pos (restrictEntry_bijective F p)]
  rfl

end Conj43
