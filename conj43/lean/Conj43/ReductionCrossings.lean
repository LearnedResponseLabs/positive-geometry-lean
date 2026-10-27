/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionAlternation
namespace Conj43
namespace Reduction
variable {n : ℕ}

lemma count_threshold (C : Finset (Fin n)) (t : Fin n) (i : Fin C.card) :
    labelsOf C i ≤ t ↔ i.val < (C.filter (· ≤ t)).card := by
  classical
  let S := Finset.univ.filter (fun j : Fin C.card => labelsOf C j ≤ t)
  have him : S.image (labelsOf C) = C.filter (· ≤ t) := by
    ext q
    constructor
    · intro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨reduction_labels_mem C j, (Finset.mem_filter.mp hj).2⟩
    · intro h
      obtain ⟨hq, hqt⟩ := Finset.mem_filter.mp h
      obtain ⟨j,rfl⟩ := reduction_labels_surj C hq
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqt⟩,rfl⟩
  have hcard : S.card = (C.filter (· ≤ t)).card := by
    rw [← him, Finset.card_image_of_injective S (labelsOf C).injective]
  constructor
  · intro h
    have hsub : Finset.Iic i ⊆ S := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((labelsOf C).monotone (Finset.mem_Iic.mp hj)).trans h⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic, hcard] at hc
    omega
  · intro h
    by_contra hn
    have hsub : S ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      exact (labelsOf C).lt_iff_lt.mp (lt_of_le_of_lt (Finset.mem_filter.mp hj).2 (lt_of_not_ge hn))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio, hcard] at hc
    omega

lemma entryCount_lt_iff (F : LooplessBAP n) (p : Fin n) {u v : Fin n}
    (hu : u ∈ component F p) (hv : v ∈ component F p) :
    F.σ.symm u < F.σ.symm v ↔ entryCount F (component F p) u < entryCount F (component F p) v := by
  refine ⟨entryCount_lt F p hu hv, ?_⟩
  intro h
  by_contra hn
  have hle := entryCount_mono F (component F p) (le_of_not_gt hn)
  omega

lemma entryCount_no_zero_full (F : LooplessBAP n) (p : Fin n) {u v : Fin n}
    (hu : u ∈ component F p) (hv : v ∈ component F p) :
    ¬ (entryCount F (component F p) u = 0 ∧ entryCount F (component F p) v = (component F p).card) := by
  intro h
  have hp : 0 < (component F p).card := Finset.card_pos.mpr ⟨u,hu⟩
  have hlt := (entryCount_lt_iff F p hu hv).mpr (by omega)
  exact entryCount_not_zero_full F p hu hv hlt h

/-- Four linear cuts of the strict clockwise order, in boundary-vertex coordinates. -/
def crossPattern (s t p q : ℕ) : Prop :=
  (s < t ∧ t < p ∧ p < q) ∨ (t < p ∧ p < q ∧ q ≤ s) ∨
  (p < q ∧ q ≤ s ∧ s < t) ∨ (q ≤ s ∧ s < t ∧ t < p)

lemma cross_iff_pattern (F : LooplessBAP n) (p q : Fin n) :
    CrossEdge F p q ↔ crossPattern (F.σ.symm p).val (F.σ.symm q).val p.val q.val := by
  unfold CrossEdge
  rw [clockwise_cases (entry_lt F p) (entry_lt F q) (exit_lt p) (exit_lt q), entry_eq, entry_eq]
  unfold crossPattern exitPos
  omega

lemma pattern_relabel {m a b i j : ℕ} (hm : 0 < m) (ha : a ≤ m) (hb : b ≤ m)
    (hi : i < m) (hj : j < m) (hab : ¬ (a=0 ∧ b=m)) (hba : ¬ (b=0 ∧ a=m)) :
    crossPattern (if a=0 then m-1 else a-1) (if b=0 then m-1 else b-1) i j ↔
      ((a < b ∧ b ≤ i ∧ i < j) ∨ (b ≤ i ∧ i < j ∧ j < a) ∨
       (i < j ∧ j < a ∧ a < b) ∨ (j < a ∧ a < b ∧ b ≤ i)) := by
  unfold crossPattern
  split_ifs <;> omega

end Reduction

theorem restrict_crossEdge (F : LooplessBAP n) (p : Fin n) (i j : Fin (component F p).card) :
    CrossEdge (restrictBAP F p) i j ↔
      CrossEdge F (labelsOf (component F p) i) (labelsOf (component F p) j) := by
  rw [Reduction.cross_iff_pattern, Reduction.cross_iff_pattern]
  have he (k : Fin (component F p).card) :
      ((restrictBAP F p).σ.symm k).val =
        if Reduction.entryCount F (component F p) (labelsOf (component F p) k) = 0
        then (component F p).card-1
        else Reduction.entryCount F (component F p) (labelsOf (component F p) k)-1 := by
    rw [show (restrictBAP F p).σ.symm k = restrictEntry F p k from restrictBAP_inv F p k]
    exact Reduction.entry_index_formula k.pos (Reduction.entryCount_le F _ _)
  rw [he i, he j, Reduction.pattern_relabel i.pos (Reduction.entryCount_le F _ _) (Reduction.entryCount_le F _ _) i.isLt j.isLt
    (Reduction.entryCount_no_zero_full F p (reduction_labels_mem _ i) (reduction_labels_mem _ j))
    (Reduction.entryCount_no_zero_full F p (reduction_labels_mem _ j) (reduction_labels_mem _ i))]
  have hab := Reduction.entryCount_lt_iff F p (reduction_labels_mem _ i) (reduction_labels_mem _ j)
  have hbi := Reduction.count_threshold (component F p) (F.σ.symm (labelsOf (component F p) j)) i
  have hja := Reduction.count_threshold (component F p) (F.σ.symm (labelsOf (component F p) i)) j
  have hij := (labelsOf (component F p)).lt_iff_lt (a := i) (b := j)
  unfold Reduction.crossPattern
  simp only [Fin.lt_def, Fin.le_def, Reduction.entryCount] at hab hbi hja hij ⊢
  omega

end Conj43
