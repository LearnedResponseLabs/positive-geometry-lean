/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionCrossings
namespace Conj43
variable {n : ℕ}

theorem restrict_connected (F : LooplessBAP n) (p : Fin n) (i j : Fin (component F p).card) :
    SameComponent (restrictBAP F p) i j := by
  have hi := (mem_component_iff F p _).mp (reduction_labels_mem (component F p) i)
  have hj := (mem_component_iff F p _).mp (reduction_labels_mem (component F p) j)
  have hij := (reduction_same_symm F hi).trans hj
  have lift : ∀ q, SameComponent F (labelsOf (component F p) i) q →
      ∀ k : Fin (component F p).card, labelsOf (component F p) k = q →
        SameComponent (restrictBAP F p) i k := by
    intro q hq
    induction hq with
    | refl =>
      intro k hk
      have hki := (labelsOf (component F p)).injective hk
      subst k
      exact .refl
    | @tail b c hab hbc ih =>
      intro k hk
      have hb : b ∈ component F p := (mem_component_iff F p b).mpr (hi.trans hab)
      obtain ⟨l,hl⟩ := reduction_labels_surj (component F p) hb
      apply (ih l hl).tail
      rcases hbc with he | he
      · exact Or.inl ((restrict_crossEdge F p l k).mpr (by simpa [hl,hk] using he))
      · exact Or.inr ((restrict_crossEdge F p k l).mpr (by simpa [hl,hk] using he))
  exact lift _ hij j rfl

theorem restrict_fixedPointFree (F : LooplessBAP n) (p : Fin n) (h : 2 ≤ (component F p).card)
    (i : Fin (component F p).card) :
    (restrictBAP F p).σ i ≠ i := by
  intro hf
  have hi : (restrictBAP F p).σ.symm i = i := by
    simpa only [Equiv.symm_apply_apply] using (congrArg (restrictBAP F p).σ.symm hf).symm
  have isolated : ∀ q, ¬ crossAdj (restrictBAP F p) i q := by
    intro q hq
    rcases hq with he | he
    · rw [Reduction.cross_iff_pattern, hi] at he
      unfold Reduction.crossPattern at he
      omega
    · rw [Reduction.cross_iff_pattern, hi] at he
      unfold Reduction.crossPattern at he
      omega
  have hc := (component_card_eq_one_iff (restrictBAP F p) i).mpr isolated
  have he : component (restrictBAP F p) i = Finset.univ := by
    ext j
    simp only [mem_component_iff, Finset.mem_univ, iff_true]
    exact restrict_connected F p i j
  rw [he, Finset.card_univ, Fintype.card_fin] at hc
  omega

namespace Reduction
/-- Least-label representatives; the construction parallels L6Slice's anchor_exists_core. -/
lemma anchor_exists (F : LooplessBAP n) (p : Fin n) :
    ∃ q, SameComponent F p q ∧ IsAnchor F q := by
  let C := component F p
  have hn : C.Nonempty := ⟨p,reduction_self_mem F p⟩
  refine ⟨C.min' hn, (mem_component_iff F p _).mp (Finset.min'_mem C hn), ?_⟩
  intro r hr
  apply Finset.min'_le
  exact (mem_component_iff F p r).mpr
    (((mem_component_iff F p _).mp (Finset.min'_mem C hn)).trans hr)

lemma anchor_unique (F : LooplessBAP n) {p q : Fin n} (hp : IsAnchor F p)
    (hq : IsAnchor F q) (hpq : SameComponent F p q) : p = q :=
  le_antisymm (hp q hpq) (hq p (reduction_same_symm F hpq))

lemma delta_restrict (F : LooplessBAP n) (p : Fin n) (θ : Fin n → ℝ)
    (i j : Fin (component F p).card) :
    delta (restrictAngles F p θ) (i,j) =
      delta θ (labelsOf (component F p) i, labelsOf (component F p) j) := by
  simp only [delta, restrictAngles, OrderEmbedding.lt_iff_lt]
end Reduction

theorem admissible_iff_components (F : LooplessBAP n) (θ : Fin n → ℝ) :
    Admissible F θ ↔ ∀ p, IsAnchor F p → Admissible (restrictBAP F p) (restrictAngles F p θ) := by
  constructor
  · intro h p _ i j hij
    rw [Reduction.delta_restrict]
    exact h _ _ ((restrict_crossEdge F p i j).mp hij)
  · intro h u v huv
    obtain ⟨p,hup,hp⟩ := Reduction.anchor_exists F u
    have hpu := reduction_same_symm F hup
    have hu : u ∈ component F p := (mem_component_iff F p u).mpr hpu
    have hv : v ∈ component F p := reduction_component_closed F p hu (Or.inl huv)
    obtain ⟨i,hi⟩ := reduction_labels_surj (component F p) hu
    obtain ⟨j,hj⟩ := reduction_labels_surj (component F p) hv
    have hc := h p hp i j ((restrict_crossEdge F p i j).mpr (by simpa [hi,hj] using huv))
    simpa only [Reduction.delta_restrict,hi,hj] using hc

end Conj43
