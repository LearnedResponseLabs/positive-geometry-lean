/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ReductionDefs
import Conj43.InterfaceChordsProofs

namespace Conj43
variable {n : ℕ}

lemma reduction_crossAdj_symm (F : LooplessBAP n) {p q : Fin n}
    (h : crossAdj F p q) : crossAdj F q p := h.symm

lemma reduction_same_symm (F : LooplessBAP n) {p q : Fin n}
    (h : SameComponent F p q) : SameComponent F q p := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head h _ ih => exact ih.trans (.single h.symm)

lemma reduction_reach_subset (F : LooplessBAP n) (p : Fin n) (k : ℕ) :
    reachAux F p k ⊆ reachAux F p (k+1) := Finset.subset_union_left

lemma reduction_reach_mono (F : LooplessBAP n) (p : Fin n) : Monotone (reachAux F p) :=
  monotone_nat_of_le_succ (reduction_reach_subset F p)

lemma reduction_reach_stable_or_card (F : LooplessBAP n) (p : Fin n) (k : ℕ) :
    reachAux F p k = reachAux F p (k+1) ∨ k+1 ≤ (reachAux F p k).card := by
  induction k with
  | zero => right; simp [reachAux]
  | succ k ih =>
    by_cases h : reachAux F p k = reachAux F p (k+1)
    · left
      exact congrArg (fun S => S ∪ Finset.univ.filter (fun q => ∃ r ∈ S, crossAdj F r q)) h
    · right
      have hc := Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨reduction_reach_subset F p k, h⟩)
      have hk := ih.resolve_left h
      omega

lemma reduction_reach_stable (F : LooplessBAP n) (p : Fin n) :
    reachAux F p n = reachAux F p (n+1) := by
  rcases reduction_reach_stable_or_card F p n with h | h
  · exact h
  · have hc : (reachAux F p n).card ≤ n := by
      simpa using Finset.card_le_univ (s := reachAux F p n)
    omega

lemma reduction_self_mem (F : LooplessBAP n) (p : Fin n) : p ∈ component F p :=
  reduction_reach_mono F p (Nat.zero_le n) (by simp [reachAux])

lemma reduction_component_closed (F : LooplessBAP n) (p : Fin n) {q r : Fin n}
    (hq : q ∈ component F p) (hqr : crossAdj F q r) : r ∈ component F p := by
  unfold component at *
  rw [reduction_reach_stable F p]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hq, hqr⟩)

/-- The finite breadth-first closure stabilizes by the size of the ambient type. -/
theorem mem_component_iff (F : LooplessBAP n) (p q : Fin n) :
    q ∈ component F p ↔ SameComponent F p q := by
  constructor
  · have step : ∀ k, ∀ q ∈ reachAux F p k, SameComponent F p q := by
      intro k
      induction k with
      | zero => intro q h; have : q = p := by simpa [reachAux] using h
                subst q; exact .refl
      | succ k ih =>
        intro q h
        rcases Finset.mem_union.mp h with h | h
        · exact ih q h
        · obtain ⟨_, r, hr, he⟩ := Finset.mem_filter.mp h
          exact (ih r hr).tail he
    exact step n q
  · intro h
    induction h with
    | refl => exact reduction_self_mem F p
    | tail _ h ih => exact reduction_component_closed F p ih h

lemma reduction_component_eq (F : LooplessBAP n) {p q : Fin n}
    (h : SameComponent F p q) : component F p = component F q := by
  ext r
  rw [mem_component_iff, mem_component_iff]
  exact ⟨fun hr => (reduction_same_symm F h).trans hr, fun hr => h.trans hr⟩

lemma reduction_labels_mem (C : Finset (Fin n)) (j : Fin C.card) : labelsOf C j ∈ C :=
  Finset.orderEmbOfFin_mem C rfl j

lemma reduction_labels_surj (C : Finset (Fin n)) {q : Fin n} (hq : q ∈ C) :
    ∃ j, labelsOf C j = q := by
  have h := Finset.range_orderEmbOfFin C rfl
  exact (Set.ext_iff.mp h q).mpr hq

/-- A singleton component is exactly an isolated vertex. -/
theorem component_card_eq_one_iff (F : LooplessBAP n) (p : Fin n) :
    (component F p).card = 1 ↔ ∀ q, ¬ crossAdj F p q := by
  constructor
  · intro h q he
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
    have hp : p = r := by simpa [hr] using reduction_self_mem F p
    have hq : q = r := by
      simpa [hr] using reduction_component_closed F p (reduction_self_mem F p) he
    have hqp : q = p := hq.trans hp.symm
    rw [hqp] at he
    exact he.elim (crossEdge_irrefl F p) (crossEdge_irrefl F p)
  · intro h
    have hs : component F p = {p} := by
      ext q
      rw [mem_component_iff, Finset.mem_singleton]
      constructor
      · intro hq
        induction hq with
        | refl => rfl
        | @tail b c _ he ih =>
          subst b
          exact False.elim (h c he)
      · rintro rfl; exact .refl
    simp [hs]

/-- The one-coordinate slice has no inequalities and its coordinate is fixed. -/
theorem singleton_slice (F : LooplessBAP n) (p : Fin n) (h : (component F p).card = 1)
    (a : Fin n → ℝ) :
    gaugeSlice (restrictBAP F p) (restrictAngles F p a) = {restrictAngles F p a} := by
  have heq (i j : Fin (component F p).card) : i = j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  have anchor (i : Fin (component F p).card) : IsAnchor (restrictBAP F p) i := by
    intro j _; exact le_of_eq (heq i j)
  have adm (θ : Fin (component F p).card → ℝ) : Admissible (restrictBAP F p) θ := by
    intro i j hij
    exact False.elim (crossEdge_irrefl _ i (heq j i ▸ hij))
  ext θ
  constructor
  · intro hθ
    apply Set.mem_singleton_iff.mpr
    funext i
    exact hθ.2 i (anchor i)
  · rintro rfl
    exact ⟨adm _, fun _ _ => rfl⟩

end Conj43
