/- Full unordered-pair columns, with the existing exponent definition unchanged. -/
import Conj43.RowDiff

namespace Conj43

variable {n : ℕ}

/-- The resolved up-down order excludes a full-turn strand at either label. -/
theorem misUD_ne_inv (F : LooplessBAP n) {p q : Fin n} (hc : MisUD F p q) :
    (F.σ⁻¹ p : ℕ) ≠ (p : ℕ) ∧ (F.σ⁻¹ q : ℕ) ≠ (q : ℕ) := by
  have hn : 0 < n := p.pos
  have b1 := (F.σ⁻¹ p).isLt
  have b2 := (F.σ⁻¹ q).isLt
  have b3 := p.isLt
  have b4 := q.isLt
  unfold MisUD at hc
  simp only [entryPos_eq, exitPos] at hc
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at hc
  constructor <;> intro hbad <;> omega

/-- Up-down misalignment has empty simultaneous necklace support. -/
theorem misUD_support_empty (F : LooplessBAP n) (p q r : Fin n) :
    ¬ (MisUD F p q ∧ p ∈ necklace F r ∧ q ∈ necklace F r) := by
  rintro ⟨hc, hp, hq⟩
  obtain ⟨hsp, hsq⟩ := misUD_ne_inv F hc
  rw [mem_necklace_iff, inArcC_of_ne hsp] at hp
  rw [mem_necklace_iff, inArcC_of_ne hsq] at hq
  have hcw := hc
  unfold MisUD at hcw
  simp only [entryPos_eq, exitPos] at hcw
  exact arc_L1 (F.σ⁻¹ p).isLt p.isLt (F.σ⁻¹ q).isLt q.isLt
    hsp hsq hcw r r.isLt ⟨hp, hq⟩

/-- Down-up misalignment has empty simultaneous absence support, also at coloops. -/
theorem misDU_support_empty (F : LooplessBAP n) (p q r : Fin n) :
    ¬ (MisDU F p q ∧ p ∉ necklace F r ∧ q ∉ necklace F r) := by
  rintro ⟨hc, hp, hq⟩
  have hsp : (F.σ⁻¹ p : ℕ) ≠ (p : ℕ) := by
    intro heq
    exact hp ((mem_necklace_iff F r p).mpr (inArcC_of_coloop heq))
  have hsq : (F.σ⁻¹ q : ℕ) ≠ (q : ℕ) := by
    intro heq
    exact hq ((mem_necklace_iff F r q).mpr (inArcC_of_coloop heq))
  have hcw := hc
  unfold MisDU at hcw
  simp only [entryPos_eq, exitPos] at hcw
  rcases arc_L2 (F.σ⁻¹ p).isLt p.isLt (F.σ⁻¹ q).isLt q.isLt
    hsp hsq hcw r r.isLt with ha | ha
  · exact hp ((mem_necklace_iff F r p).mpr (Or.inr ha))
  · exact hq ((mem_necklace_iff F r q).mpr (Or.inr ha))

/-- Zero exponent before taking differences; no distinctness or rank restriction. -/
theorem pairExponent_nonCross (F : LooplessBAP n) (p q r : Fin n)
    (hpq : ¬ CrossEdge F p q) (hqp : ¬ CrossEdge F q p) :
    pairExponent F r (p, q) = 0 := by
  rcases le_total p q with hle | hle
  · simp only [pairExponent, min_eq_left hle, max_eq_right hle]
    rw [if_neg (misUD_support_empty F p q r), if_neg (misDU_support_empty F p q r),
      if_neg (fun h => hpq h.1), if_neg (fun h => hqp h.1)]
    norm_num
  · simp only [pairExponent, min_eq_right hle, max_eq_left hle]
    rw [if_neg (misUD_support_empty F q p r), if_neg (misDU_support_empty F q p r),
      if_neg (fun h => hqp h.1), if_neg (fun h => hpq h.1)]
    norm_num

/-- The exponent depends only on the unordered pair. -/
theorem pairExponent_swap (F : LooplessBAP n) (p q r : Fin n) :
    pairExponent F r (p,q) = pairExponent F r (q,p) := by
  simp only [pairExponent, min_comm p q, max_comm p q]

/-- Relabeled row difference for an arbitrary column type. -/
theorem full_PDM_apply [NeZero n] (F : LooplessBAP n) {ι : Type*}
    (M : Matrix (Fin n) ι ℤ) (x : Fin n) (j : ι) :
    (Pmat F * Dmat n * M) x j = M (F.σ⁻¹ x + 1) j - M (F.σ⁻¹ x) j := by
  rw [Matrix.mul_apply]
  simp only [PD_apply, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  simp

/-- Every crossing pair has an index in the existing crossing-edge matrix. -/
theorem crossEdge_mem_full (F : LooplessBAP n) (p q : Fin n)
    (hc : CrossEdge F p q) : (p,q) ∈ crossEdges F := by
  simp only [crossEdges, List.mem_flatMap, List.mem_filterMap]
  refine ⟨p, ?_, q, ?_, ?_⟩
  · simp
  · simp
  · simp [hc]

/-- Transfer the existing crossing identity to a specified directed pair. -/
theorem crossing_pair_difference [NeZero n] (F : LooplessBAP n) (p q x : Fin n)
    (hc : CrossEdge F p q) :
    pairExponent F (F.σ⁻¹ x + 1) (p,q) - pairExponent F (F.σ⁻¹ x) (p,q) =
      (if x = q then 1 else 0) - (if x = p then 1 else 0) := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (crossEdge_mem_full F p q hc)
  have h := congrFun (congrFun (rowdiff_proof n F) x) j
  rw [PDM_apply] at h
  simpa only [Mmat, Bmat, Matrix.of_apply, edgeOf, hj] using h

theorem full_pair_columns_zero (n : ℕ) [NeZero n] (F : LooplessBAP n)
    (e : {e : Fin n × Fin n // e.1 < e.2})
    (hpq : ¬ CrossEdge F e.val.1 e.val.2)
    (hqp : ¬ CrossEdge F e.val.2 e.val.1) :
    let M : Matrix (Fin n) {e : Fin n × Fin n // e.1 < e.2} ℤ :=
      fun r j => pairExponent F r j.val
    let B : Matrix (Fin n) {e : Fin n × Fin n // e.1 < e.2} ℤ :=
      fun x j => if CrossEdge F j.val.1 j.val.2 then
        (if x = j.val.2 then 1 else 0) - (if x = j.val.1 then 1 else 0)
      else if CrossEdge F j.val.2 j.val.1 then
        (if x = j.val.1 then 1 else 0) - (if x = j.val.2 then 1 else 0)
      else 0
    (∀ r, M r e = 0) ∧ (∀ x, (Pmat F * Dmat n * M) x e = 0) ∧
      (∀ x, B x e = 0)  := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact pairExponent_nonCross F e.val.1 e.val.2 r hpq hqp
  · intro x
    erw [full_PDM_apply]
    simp only [pairExponent_nonCross F e.val.1 e.val.2 _ hpq hqp, sub_self]
  · intro x
    simp only [if_neg hpq, if_neg hqp]

theorem rowdiff_full_pairs (n : ℕ) [NeZero n] (F : LooplessBAP n) :
    let M : Matrix (Fin n) {e : Fin n × Fin n // e.1 < e.2} ℤ :=
      fun r j => pairExponent F r j.val
    let B : Matrix (Fin n) {e : Fin n × Fin n // e.1 < e.2} ℤ :=
      fun x j => if CrossEdge F j.val.1 j.val.2 then
        (if x = j.val.2 then 1 else 0) - (if x = j.val.1 then 1 else 0)
      else if CrossEdge F j.val.2 j.val.1 then
        (if x = j.val.1 then 1 else 0) - (if x = j.val.2 then 1 else 0)
      else 0
    Pmat F * Dmat n * M = B  := by
  dsimp only
  ext x e
  erw [full_PDM_apply]
  by_cases hpq : CrossEdge F e.val.1 e.val.2
  · rw [if_pos hpq]
    exact crossing_pair_difference F e.val.1 e.val.2 x hpq
  · rw [if_neg hpq]
    by_cases hqp : CrossEdge F e.val.2 e.val.1
    · rw [if_pos hqp]
      rw [show e.val = (e.val.1, e.val.2) from rfl]
      rw [pairExponent_swap F e.val.1 e.val.2, pairExponent_swap F e.val.1 e.val.2]
      exact crossing_pair_difference F e.val.2 e.val.1 x hqp
    · rw [if_neg hqp]
      change pairExponent F (F.σ⁻¹ x + 1) (e.val.1, e.val.2) -
        pairExponent F (F.σ⁻¹ x) (e.val.1, e.val.2) = 0
      rw [pairExponent_nonCross F e.val.1 e.val.2 _ hpq hqp,
        pairExponent_nonCross F e.val.1 e.val.2 _ hpq hqp, sub_self]

end Conj43
