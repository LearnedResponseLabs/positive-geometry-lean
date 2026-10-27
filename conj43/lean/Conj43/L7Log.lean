import Conj43.L6Conditional
import Conj43.FullColumns

/-! The full necklace log formula and its internal gradient assembly. -/
namespace Conj43
variable {n : ℕ}

/-- Every unordered pair, including Mis pairs and pairs meeting coloops. -/
abbrev NecklacePair (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

/-- Totalized logarithm on all pairs. Zero-exponent non-crossing factors may
have zero bracket; their assigned logarithm is immaterial. -/
noncomputable def pairLog (θ : Fin n → ℝ) (e : Fin n × Fin n) : ℝ :=
  Real.log ‖bracketPlus (angleParameter θ) e.2 e.1‖

/-- The log form of the entire necklace monomial in Proposition 5.12, (5.8). -/
noncomputable def necklaceLogModel (F : LooplessBAP n) (θ : Fin n → ℝ) : Fin n → ℝ :=
  fun r => ∑ e : NecklacePair n, (pairExponent F r e.val : ℝ) * pairLog θ e.val

/-- The real cast of P D, acting on logarithmic necklace coordinates. -/
noncomputable def necklaceRecovery [NeZero n] (F : LooplessBAP n)
    (z : Fin n → ℝ) : Fin n → ℝ :=
  (Matrix.of (fun x r => (Pmat F x r : ℝ))).mulVec
    ((Matrix.of (fun r s => (Dmat n r s : ℝ))).mulVec z)

private theorem pairLog_swap (θ : Fin n → ℝ) (p q : Fin n) :
    pairLog θ (p,q) = pairLog θ (q,p) := by
  unfold pairLog bracketPlus
  by_cases hp : p < q <;> by_cases hq : q < p
  · exact False.elim (lt_asymm hp hq)
  · simp [hp, hq]
  · simp [hp, hq]
  · have h : p = q := le_antisymm (le_of_not_gt hq) (le_of_not_gt hp)
    subst h; rfl

private def sortedEdge (F : LooplessBAP n) (j : EdgeIdx F) : NecklacePair n :=
  ⟨(min (edgeOf F j).1 (edgeOf F j).2, max (edgeOf F j).1 (edgeOf F j).2), by
    have h : (edgeOf F j).1 ≠ (edgeOf F j).2 := crossEdge_ne F (crossEdge_of_mem F (List.get_mem _ j))
    rcases lt_or_gt_of_ne h with h | h <;> simp [min_def, max_def, le_of_lt h, not_le_of_gt h, h]⟩

private theorem sortedEdge_cases (F : LooplessBAP n) (j : EdgeIdx F) :
    (sortedEdge F j).val = edgeOf F j ∨
      (sortedEdge F j).val = ((edgeOf F j).2, (edgeOf F j).1) := by
  rcases le_total (edgeOf F j).1 (edgeOf F j).2 with h | h
  · left; simp [sortedEdge, min_eq_left h, max_eq_right h]
  · right; simp [sortedEdge, min_eq_right h, max_eq_left h]

private theorem sortedEdge_injective (F : LooplessBAP n) :
    Function.Injective (sortedEdge F) := by
  intro i j h
  have hv := congrArg Subtype.val h
  have hi : CrossEdge F (edgeOf F i).1 (edgeOf F i).2 := crossEdge_of_mem F (List.get_mem _ i)
  have hj : CrossEdge F (edgeOf F j).1 (edgeOf F j).2 := crossEdge_of_mem F (List.get_mem _ j)
  apply (crossEdges_nodup F).injective_get
  change edgeOf F i = edgeOf F j
  rcases sortedEdge_cases F i with ei | ei <;>
    rcases sortedEdge_cases F j with ej | ej <;> rw [ei, ej] at hv
  · exact hv
  · have h1 := congrArg Prod.fst hv
    have h2 := congrArg Prod.snd hv
    exact False.elim ((crossEdge_excl F hi).2.2.2.2 (by simpa [h1, h2] using hj))
  · have h1 := congrArg Prod.fst hv
    have h2 := congrArg Prod.snd hv
    exact False.elim ((crossEdge_excl F hj).2.2.2.2 (by simpa [← h1, ← h2] using hi))
  · exact Prod.ext (congrArg Prod.snd hv) (congrArg Prod.fst hv)

private theorem sortedEdge_term (F : LooplessBAP n) (θ : Fin n → ℝ)
    (r : Fin n) (j : EdgeIdx F) :
    (pairExponent F r (sortedEdge F j).val : ℝ) * pairLog θ (sortedEdge F j).val =
      (Mmat F r j : ℝ) * pairLog θ (edgeOf F j) := by
  rcases sortedEdge_cases F j with h | h
  · rw [h]; rfl
  · rw [h, pairExponent_swap, pairLog_swap]; rfl

/-- Formal removal of all non-crossing columns, using the existing Mis support
lemmas through pairExponent_nonCross. Each unordered crossing is counted once. -/
theorem necklaceLogModel_crossing_core (F : LooplessBAP n) (θ : Fin n → ℝ) :
    necklaceLogModel F θ = (Matrix.of (fun r j => (Mmat F r j : ℝ))).mulVec
      (fun j => pairLog θ (edgeOf F j)) := by
  classical
  funext r
  symm
  change (∑ j : EdgeIdx F, (Mmat F r j : ℝ) * pairLog θ (edgeOf F j)) = _
  apply Finset.sum_bij_ne_zero (fun j _ _ => sortedEdge F j)
  · intros; exact Finset.mem_univ _
  · intro i _ _ j _ _ h; exact sortedEdge_injective F h
  · intro e _ he
    have hc : CrossEdge F e.val.1 e.val.2 ∨ CrossEdge F e.val.2 e.val.1 := by
      by_contra h
      push Not at h
      have hz := pairExponent_nonCross F e.val.1 e.val.2 r h.1 h.2
      exact he (by simp [hz])
    have preimage : ∃ j, sortedEdge F j = e := by
      rcases hc with hc | hc
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp (crossEdge_mem_full F _ _ hc)
        refine ⟨j, ?_⟩
        apply Subtype.ext
        simp only [sortedEdge, edgeOf, hj, Prod.fst, Prod.snd, min_eq_left e.property.le, max_eq_right e.property.le]
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp (crossEdge_mem_full F _ _ hc)
        refine ⟨j, ?_⟩
        apply Subtype.ext
        simp only [sortedEdge, edgeOf, hj, Prod.fst, Prod.snd, min_eq_right e.property.le, max_eq_left e.property.le]
    obtain ⟨j, hj⟩ := preimage
    refine ⟨j, Finset.mem_univ _, ?_, hj⟩
    rw [← sortedEdge_term F θ r j, hj]
    exact he
  · intro j _ _; exact (sortedEdge_term F θ r j).symm

/-- D annihilates the common logarithmic projective scalar, including n = 1. -/
theorem necklaceRecovery_constant_core [NeZero n] (F : LooplessBAP n)
    (z : Fin n → ℝ) (c : ℝ) :
    necklaceRecovery F (z + fun _ => c) = necklaceRecovery F z := by
  have hz : (Matrix.of (fun r s => (Dmat n r s : ℝ))).mulVec (fun _ => c) = 0 := by
    ext r
    simp [Matrix.mulVec, dotProduct, Dmat, sub_mul, Finset.sum_sub_distrib]
  unfold necklaceRecovery
  rw [Matrix.mulVec_add, hz, add_zero]

/-- The hinge after taking logs; admissibility supplies the nonzero factor. -/
theorem pairLog_hinge_core (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) (j : EdgeIdx F) :
    pairLog θ (edgeOf F j) = Real.log (Real.sin (delta θ (edgeOf F j))) + Real.log 2 := by
  have he : CrossEdge F (edgeOf F j).1 (edgeOf F j).2 := crossEdge_of_mem F (List.get_mem _ j)
  have hs := Real.sin_pos_of_pos_of_lt_pi (hθ _ _ he).1 (hθ _ _ he).2
  have hh := hinge_identity_core F θ hθ _ _ he
  change Real.log ‖bracketPlus (angleParameter θ) (edgeOf F j).2 (edgeOf F j).1‖ = _
  rw [hh, Real.log_mul (by norm_num) (ne_of_gt hs), add_comm]

/-- P D M = B transported to real matrices, followed by the log hinge and
formal incidence balance. No assembled gradient identity is assumed. -/
theorem necklaceLogModel_gradient_core [NeZero n] (F : LooplessBAP n)
    (θ : Fin n → ℝ) (hθ : Admissible F θ) :
    necklaceRecovery F (necklaceLogModel F θ) = gradientMap F θ := by
  have hm : (Matrix.of (fun x r => (Pmat F x r : ℝ))) *
      (Matrix.of (fun r s => (Dmat n r s : ℝ))) * (Matrix.of (fun r j => (Mmat F r j : ℝ))) = realB F := by
    ext x j
    have h := congrFun (congrFun (rowdiff n F) x) j
    simp only [Matrix.mul_apply, Matrix.of_apply, realB] at h ⊢
    exact_mod_cast h
  rw [necklaceLogModel_crossing_core]
  unfold necklaceRecovery
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm]
  simp_rw [pairLog_hinge_core F θ hθ]
  exact gradient_constant_core F θ (Real.log 2)

end Conj43
