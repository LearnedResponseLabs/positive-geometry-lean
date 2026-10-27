/-
Conj43/RowDiff.lean — L2 proof of prop:rowdiff: P_f · D · M_N = B.

Layer over Conj43/CyclicArc.lean: (i) the membership equivalence eq:arc for the
pinned necklace recursion, (ii) the class ⟹ column lemmas (crossing kills the
Mis terms; L3 turns the crossing column into an arc indicator), (iii) assembly
of the matrix identity. No pinned definition is touched.
-/
import Conj43.CyclicArc

namespace Conj43

variable {n : ℕ}

/-! ### Preliminaries about the pinned definitions -/

theorem perm_apply_inv (F : LooplessBAP n) (y : Fin n) : F.σ (F.σ⁻¹ y) = y := by
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem perm_inv_apply (F : LooplessBAP n) (y : Fin n) : F.σ⁻¹ (F.σ y) = y := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- σ and σ⁻¹ have the same fixed points: `y` is a coloop for one iff for the
other. (L4: fixed points are no longer excluded — they are the coloops.) -/
theorem inv_fix_iff (F : LooplessBAP n) (y : Fin n) : F.σ⁻¹ y = y ↔ F.σ y = y := by
  constructor
  · intro h
    have h2 := perm_apply_inv F y
    rw [h] at h2
    exact h2
  · intro h
    have h2 := perm_inv_apply F y
    rw [h] at h2
    exact h2

/-- The pinned entry position, with its `% (5n)` discharged. -/
theorem entryPos_eq (F : LooplessBAP n) (x : Fin n) :
    entryPos F x = 5 * (F.σ⁻¹ x : ℕ) + 4 := by
  unfold entryPos
  exact Nat.mod_eq_of_lt (by have := (F.σ⁻¹ x).isLt; omega)

/-! ### eq:arc — membership in the pinned necklace is arc membership -/

/-- **eq:arc** at the recursion level: `x ∈ I_{i+1}` iff row `i` lies in the
half-open cyclic arc `(s_x, x]` (0-based), read with the coloop convention
`inArcC` — a coloop `x` (`s_x = x`) lies in EVERY necklace row. Induction over
the pinned `necklaceAux`; the census guard `i ∈ prior` is automatic (at an
active `i` because `i ∈ (s_i, i]`, at a coloop `i` because the arc is full). -/
theorem mem_necklaceAux_iff (F : LooplessBAP n) :
    ∀ i, i < n → ∀ x : Fin n,
      (x ∈ necklaceAux F i ↔ inArcC n (F.σ⁻¹ x : ℕ) (x : ℕ) i) := by
  intro i
  induction i with
  | zero =>
    intro h0 x
    have hs := (F.σ⁻¹ x).isLt
    have hx := x.isLt
    simp only [necklaceAux, necklaceFirst, Finset.mem_filter, Finset.mem_univ,
      true_and]
    unfold inArcC inArcN
    rcases step_spec h0 hs h0 with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
      rcases step_spec h0 hs hx with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
        omega
  | succ i ih =>
    intro hsucc x
    have hi : i < n := by omega
    have hn : 0 < n := by omega
    -- the guard holds: i ∈ I_{i+1} (also at a coloop i, where the arc is full)
    have hlab : (⟨i, hi⟩ : Fin n) ∈ necklaceAux F i := by
      rw [ih hi ⟨i, hi⟩]
      show inArcC n (F.σ⁻¹ (⟨i, hi⟩ : Fin n) : ℕ) i i
      have hs := (F.σ⁻¹ (⟨i, hi⟩ : Fin n)).isLt
      by_cases hcol : (F.σ⁻¹ (⟨i, hi⟩ : Fin n) : ℕ) = i
      · exact inArcC_of_coloop hcol
      · refine Or.inr ?_
        unfold inArcN
        rcases step_spec hn hs hi with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> omega
    simp only [necklaceAux]
    rw [dif_pos hi, if_pos hlab, Finset.mem_insert, Finset.mem_erase, ih hi x]
    -- convert the two Fin equalities to value form
    have hs := (F.σ⁻¹ x).isLt
    have hx := x.isLt
    have hEq1 : (x = F.σ ⟨i, hi⟩) ↔ ((F.σ⁻¹ x : ℕ) = i) := by
      constructor
      · intro h
        rw [h, perm_inv_apply]
      · intro h
        have h2 : F.σ⁻¹ x = ⟨i, hi⟩ := Fin.ext h
        rw [← perm_apply_inv F x, h2]
    have hEq2 : (x = (⟨i, hi⟩ : Fin n)) ↔ ((x : ℕ) = i) := by
      constructor
      · intro h
        rw [h]
      · intro h
        exact Fin.ext h
    rw [hEq1]
    simp only [ne_eq]
    rw [hEq2]
    have hstep := inArcC_succ (n := n) (s := (F.σ⁻¹ x : ℕ)) (x := (x : ℕ))
      (j := i) hs hx hi
    rw [Nat.mod_eq_of_lt hsucc] at hstep
    rw [hstep]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨h2, fun hh => h1 hh.symm⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨fun hh => h2 hh.symm, h1⟩

/-- **eq:arc** for the pinned `necklace` (coloop convention). -/
theorem mem_necklace_iff (F : LooplessBAP n) (r x : Fin n) :
    x ∈ necklace F r ↔ inArcC n (F.σ⁻¹ x : ℕ) (x : ℕ) (r : ℕ) :=
  mem_necklaceAux_iff F r r.isLt x

/-! ### Crossing edges: extraction and class exclusivity -/

/-- Every column of the pinned matrices is a directed crossing edge. -/
theorem crossEdge_of_mem (F : LooplessBAP n) {e : Fin n × Fin n}
    (he : e ∈ crossEdges F) : CrossEdge F e.1 e.2 := by
  simp only [crossEdges, List.mem_flatMap, List.mem_filterMap] at he
  obtain ⟨p, -, q, -, hq⟩ := he
  by_cases hc : CrossEdge F p q
  · rw [if_pos hc] at hq
    injection hq with hq2
    subst hq2
    exact hc
  · rw [if_neg hc] at hq
    exact absurd hq (by simp)

/-- A directed crossing has distinct tail and head. -/
theorem crossEdge_ne (F : LooplessBAP n) {t h : Fin n}
    (hc : CrossEdge F t h) : t ≠ h := by
  intro heq
  subst heq
  unfold CrossEdge Clockwise4 at hc
  rw [step_self] at hc
  exact absurd hc.1 (Nat.lt_irrefl 0)

/-- **Coloops carry no crossing** (paper, "Coloops" step of prop:rowdiff: the
ε-convention places the exit `b⁻_p` immediately before the entry `b⁺_p`, so no
refined endpoint lies strictly inside the clockwise arc from `b⁻_p` to
`b⁺_{s_p}`, killing both crossing orders). Stated as: a directed crossing has
both endpoints active. -/
theorem crossEdge_ne_inv (F : LooplessBAP n) {t h : Fin n}
    (hc : CrossEdge F t h) :
    (F.σ⁻¹ t : ℕ) ≠ (t : ℕ) ∧ (F.σ⁻¹ h : ℕ) ≠ (h : ℕ) := by
  have hn : 0 < n := t.pos
  have b1 := (F.σ⁻¹ t).isLt
  have b2 := (F.σ⁻¹ h).isLt
  have b3 := t.isLt
  have b4 := h.isLt
  unfold CrossEdge at hc
  simp only [entryPos_eq, exitPos] at hc
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at hc
  constructor <;> intro hbad <;> omega

/-- A directed crossing excludes both misalignment classes (in both label
orders) and the reverse crossing — the paper's "class determines the order",
via the linear canonicalization of `Clockwise4`. -/
theorem crossEdge_excl (F : LooplessBAP n) {t h : Fin n}
    (hc : CrossEdge F t h) :
    ¬ MisUD F t h ∧ ¬ MisUD F h t ∧ ¬ MisDU F t h ∧ ¬ MisDU F h t ∧
      ¬ CrossEdge F h t := by
  have hn : 0 < n := t.pos
  have b1 := (F.σ⁻¹ t).isLt
  have b2 := (F.σ⁻¹ h).isLt
  have b3 := t.isLt
  have b4 := h.isLt
  unfold CrossEdge at hc
  simp only [entryPos_eq, exitPos] at hc
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at hc
  have hg1 : negPos (5 * n) (5 * (F.σ⁻¹ t : ℕ) + 4)
      = 5 * n - (5 * (F.σ⁻¹ t : ℕ) + 4) := negPos_eq (by omega) (by omega)
  have hg2 : negPos (5 * n) (5 * (F.σ⁻¹ h : ℕ) + 4)
      = 5 * n - (5 * (F.σ⁻¹ h : ℕ) + 4) := negPos_eq (by omega) (by omega)
  have hg3 : negPos (5 * n) (5 * (t : ℕ) + 1)
      = 5 * n - (5 * (t : ℕ) + 1) := negPos_eq (by omega) (by omega)
  have hg4 : negPos (5 * n) (5 * (h : ℕ) + 1)
      = 5 * n - (5 * (h : ℕ) + 1) := negPos_eq (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro hbad
  · unfold MisUD at hbad
    simp only [entryPos_eq, exitPos] at hbad
    rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
      at hbad
    omega
  · unfold MisUD at hbad
    simp only [entryPos_eq, exitPos] at hbad
    rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
      at hbad
    omega
  · unfold MisDU at hbad
    simp only [entryPos_eq, exitPos] at hbad
    rw [hg1, hg2, hg3, hg4] at hbad
    rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
      at hbad
    omega
  · unfold MisDU at hbad
    simp only [entryPos_eq, exitPos] at hbad
    rw [hg1, hg2, hg3, hg4] at hbad
    rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
      at hbad
    omega
  · unfold CrossEdge at hbad
    simp only [entryPos_eq, exitPos] at hbad
    rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
      at hbad
    omega

/-! ### The crossing column -/

/-- **Class ⟹ column** (paper: crossing bullet + coincidence closure, all
absorbed into the arithmetic of L3): on a directed crossing t → h the pinned
Prop 5.12 exponent column is `−1_{r ∈ (s_t, s_h]}`. -/
theorem pairExponent_of_cross (F : LooplessBAP n) {t h : Fin n}
    (hc : CrossEdge F t h) (r : Fin n) :
    pairExponent F r (t, h) =
      if inArcN n (F.σ⁻¹ t : ℕ) (F.σ⁻¹ h : ℕ) (r : ℕ) then -1 else 0 := by
  have hth : t ≠ h := crossEdge_ne F hc
  obtain ⟨hUD1, hUD2, hDU1, hDU2, hCE2⟩ := crossEdge_excl F hc
  -- the crossing order in linear-position form, feeding L3
  have hcw : Clockwise4 (5 * n) (5 * (F.σ⁻¹ t : ℕ) + 4)
      (5 * (F.σ⁻¹ h : ℕ) + 4) (5 * (t : ℕ) + 1) (5 * (h : ℕ) + 1) := by
    have hc' := hc
    unfold CrossEdge at hc'
    simpa only [entryPos_eq, exitPos] using hc'
  obtain ⟨hst, hsh⟩ := crossEdge_ne_inv F hc
  have harc := arc_L3 (F.σ⁻¹ t).isLt t.isLt (F.σ⁻¹ h).isLt h.isLt hst hsh hcw
      (r : ℕ) r.isLt
  -- memberships as arcs (neither endpoint is a coloop, so `inArcC` is strict)
  have hmt := mem_necklace_iff F r t
  have hmh := mem_necklace_iff F r h
  rw [inArcC_of_ne hst] at hmt
  rw [inArcC_of_ne hsh] at hmh
  simp only [pairExponent]
  by_cases hr : inArcN n (F.σ⁻¹ t : ℕ) (F.σ⁻¹ h : ℕ) (r : ℕ)
  · obtain ⟨hat, hah⟩ := harc.mpr hr
    rw [if_pos hr]
    rcases lt_or_gt_of_ne hth with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le,
        if_neg (fun hb => hUD1 hb.1), if_neg (fun hb => hDU1 hb.1),
        if_pos ⟨hc, hmt.mpr hat, fun hm => hah (hmh.mp hm)⟩,
        if_neg (fun hb => hCE2 hb.1)]
      norm_num
    · rw [min_eq_right hgt.le, max_eq_left hgt.le,
        if_neg (fun hb => hUD2 hb.1), if_neg (fun hb => hDU2 hb.1),
        if_neg (fun hb => hCE2 hb.1),
        if_pos ⟨hc, hmt.mpr hat, fun hm => hah (hmh.mp hm)⟩]
      norm_num
  · have hno : ¬ (t ∈ necklace F r ∧ h ∉ necklace F r) := fun ⟨h1, h2⟩ =>
      hr (harc.mp ⟨hmt.mp h1, fun ha => h2 (hmh.mpr ha)⟩)
    rw [if_neg hr]
    rcases lt_or_gt_of_ne hth with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le,
        if_neg (fun hb => hUD1 hb.1), if_neg (fun hb => hDU1 hb.1),
        if_neg (fun hb => hno ⟨hb.2.1, hb.2.2⟩),
        if_neg (fun hb => hCE2 hb.1)]
      norm_num
    · rw [min_eq_right hgt.le, max_eq_left hgt.le,
        if_neg (fun hb => hUD2 hb.1), if_neg (fun hb => hDU2 hb.1),
        if_neg (fun hb => hCE2 hb.1),
        if_neg (fun hb => hno ⟨hb.2.1, hb.2.2⟩)]
      norm_num

/-! ### Assembly: P_f · D · M_N = B -/

/-- Abstract-pair form of the column lemma, for direct rewriting. -/
theorem pairExponent_of_cross' (F : LooplessBAP n) (e : Fin n × Fin n)
    (hc : CrossEdge F e.1 e.2) (r : Fin n) :
    pairExponent F r e =
      if inArcN n (F.σ⁻¹ e.1 : ℕ) (F.σ⁻¹ e.2 : ℕ) (r : ℕ) then -1 else 0 := by
  obtain ⟨t, h⟩ := e
  exact pairExponent_of_cross F hc r

/-- Row x of P_f·D picks out the necklace-relabeled difference row. -/
theorem PD_apply [NeZero n] (F : LooplessBAP n) (x r : Fin n) :
    (Pmat F * Dmat n) x r
      = (if r = F.σ⁻¹ x + 1 then (1 : ℤ) else 0)
        - (if r = F.σ⁻¹ x then 1 else 0) := by
  rw [Matrix.mul_apply]
  simp only [Pmat, Dmat, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  simp [Fintype.sum_ite_eq']

/-- The triple product row is the cyclic difference of M_N-rows at s_x. -/
theorem PDM_apply [NeZero n] (F : LooplessBAP n) (x : Fin n) (j : EdgeIdx F) :
    (Pmat F * Dmat n * Mmat F) x j
      = Mmat F (F.σ⁻¹ x + 1) j - Mmat F (F.σ⁻¹ x) j := by
  rw [Matrix.mul_apply]
  simp only [PD_apply, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  simp [Fintype.sum_ite_eq']

/-- **prop:rowdiff**: P_f · D · M_N = B, entrywise over ℤ. -/
theorem rowdiff_proof (n : ℕ) [NeZero n] (F : LooplessBAP n) :
    Pmat F * Dmat n * Mmat F = Bmat F := by
  ext x j
  rw [PDM_apply]
  have hedge : CrossEdge F (edgeOf F j).1 (edgeOf F j).2 :=
    crossEdge_of_mem F (List.get_mem _ j)
  have hth : (edgeOf F j).1 ≠ (edgeOf F j).2 := crossEdge_ne F hedge
  simp only [Mmat, Bmat, Matrix.of_apply]
  -- the crossing column is minus the indicator of the arc (s_p, s_q]
  rw [pairExponent_of_cross' F (edgeOf F j) hedge (F.σ⁻¹ x + 1),
    pairExponent_of_cross' F (edgeOf F j) hedge (F.σ⁻¹ x)]
  have hval : ((F.σ⁻¹ x + 1 : Fin n) : ℕ) = ((F.σ⁻¹ x : ℕ) + 1) % n := by
    rw [Fin.val_add, Fin.val_one']
    conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt (F.σ⁻¹ x).isLt]
  rw [hval]
  -- its row difference is the boundary of the arc, [s_q] − [s_p] ...
  have hd := inArcN_indicator_diff (F.σ⁻¹ (edgeOf F j).1).isLt (F.σ⁻¹ (edgeOf F j).2).isLt
    (F.σ⁻¹ x).isLt (fun hEq => hth (Equiv.injective F.σ⁻¹ (Fin.ext hEq)))
  -- ... which P_f relabels as [q] − [p], since σ⁻¹ is injective
  have hlab (y : Fin n) : ((F.σ⁻¹ x : ℕ) = (F.σ⁻¹ y : ℕ)) ↔ x = y :=
    ⟨fun hEq => Equiv.injective F.σ⁻¹ (Fin.ext hEq), fun hEq => by rw [hEq]⟩
  simp only [hlab] at hd
  rw [← hd]
  split_ifs <;> norm_num

end Conj43
