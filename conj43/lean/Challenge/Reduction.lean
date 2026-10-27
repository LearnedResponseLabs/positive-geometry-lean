/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionDefs

/-! ### Group `reduction`: the paper's Lemma 5, parts (1), (3), (4) and the first half of (2)

Frozen on 2026-10-26, before any proof. Proof placeholders belong only to this challenge. -/

namespace Conj43

variable {n : ℕ}

/-- The computed component is the reflexive-transitive closure of crossing adjacency. -/
theorem mem_component_iff (F : LooplessBAP n) (p q : Fin n) :
    q ∈ component F p ↔ SameComponent F p q := by
  sorry

/-- Part (1), alternation: once the strands outside a component are erased, every new boundary vertex receives exactly
one surviving entry. -/
theorem restrictEntry_bijective (F : LooplessBAP n) (p : Fin n) :
    Function.Bijective (restrictEntry F p) := by
  sorry

/-- The restriction's `σ⁻¹` is the relabeled entry map. -/
theorem restrictBAP_inv (F : LooplessBAP n) (p : Fin n) (j : Fin (component F p).card) :
    (restrictBAP F p).σ⁻¹ j = restrictEntry F p j := by
  sorry

/-- Part (1): the crossing edges of the restriction are the crossing edges inside the component, relabeled. -/
theorem restrict_crossEdge (F : LooplessBAP n) (p : Fin n) (i j : Fin (component F p).card) :
    CrossEdge (restrictBAP F p) i j ↔
      CrossEdge F (labelsOf (component F p) i) (labelsOf (component F p) j) := by
  sorry

/-- Part (1): the crossing graph of the restriction is connected. -/
theorem restrict_connected (F : LooplessBAP n) (p : Fin n) (i j : Fin (component F p).card) :
    SameComponent (restrictBAP F p) i j := by
  sorry

/-- Part (3): a component is a single label exactly when that label crosses nothing. -/
theorem component_card_eq_one_iff (F : LooplessBAP n) (p : Fin n) :
    (component F p).card = 1 ↔ ∀ q, ¬ crossAdj F p q := by
  sorry

/-- Part (4): a component of at least two labels restricts to a fixed-point-free permutation. -/
theorem restrict_fixedPointFree (F : LooplessBAP n) (p : Fin n) (h : 2 ≤ (component F p).card)
    (i : Fin (component F p).card) :
    (restrictBAP F p).σ i ≠ i := by
  sorry

/-- Admissibility splits over the components: each crossing edge lies in one component, with the same angle. -/
theorem admissible_iff_components (F : LooplessBAP n) (θ : Fin n → ℝ) :
    Admissible F θ ↔ ∀ p, IsAnchor F p → Admissible (restrictBAP F p) (restrictAngles F p θ) := by
  sorry

/-- Part (2), first half: restriction to the components is a homeomorphism from the gauge slice onto the product of the
components' gauge slices. -/
theorem slice_homeomorph_components (F : LooplessBAP n) (a : Fin n → ℝ) :
    ∃ e : gaugeSlice F a ≃ₜ
        {x : (p : {p : Fin n // IsAnchor F p}) → (Fin (component F p.val).card → ℝ) |
          ∀ p, x p ∈ gaugeSlice (restrictBAP F p.val) (restrictAngles F p.val a)},
      ∀ θ p, (e θ).val p = restrictAngles F p.val θ.val := by
  sorry

/-- Part (3): the gauge slice of a single-label component is a point. -/
theorem singleton_slice (F : LooplessBAP n) (p : Fin n) (h : (component F p).card = 1) (a : Fin n → ℝ) :
    gaugeSlice (restrictBAP F p) (restrictAngles F p a) = {restrictAngles F p a} := by
  sorry

/-! Controls and the fixture. -/

/-- Control (Remark 6): a component need not be `σ`-stable, so the restriction is an erasure, not a restriction of `σ`. -/
theorem component_not_sigma_stable :
    component FSwap 0 = {0} ∧ FSwap.σ 0 ∉ component FSwap 0 := by
  sorry

/-- Control: on a set of strands that is not a union of components, the relabeled entry map can fail to be a bijection. -/
theorem entryMapOn_not_bijective :
    ¬ Function.Bijective (entryMapOn FTop3 {0, 1}) := by
  sorry

/-- Control: without `2 ≤ card`, part (4) fails; the coloop is a one-label component with a fixed point. -/
theorem restrict_coloop_fixed :
    (component FColoop 0).card = 1 ∧ ∃ i, (restrictBAP FColoop 0).σ i = i := by
  sorry

/-- The paper's Figure 5(a): two components of three labels, each restricting to `σ = (2, 0, 1)`. -/
theorem fixture_two_components :
    component FTwo 0 = {0, 1, 2} ∧ component FTwo 3 = {3, 4, 5} ∧
      (∀ j, (restrictEntry FTwo 0 j : ℕ) = ((j : ℕ) + 1) % 3) ∧
      (∀ j, (restrictEntry FTwo 3 j : ℕ) = ((j : ℕ) + 1) % 3) := by
  sorry

end Conj43
