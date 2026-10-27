/-
Conj43/Cover.lean — the `Cover` invariant of the §7 backward induction and its
three surgery moves. A cover of `GEdgeSet σ` is an edge-disjoint list of size-≥3
Finsets whose consecutive edges exhaust `GEdgeSet σ` (as a Nodup list). The moves
mirror §5's identity / triangle-append / edge-subdivision transitions.
-/
import Conj43.CoverInsert

namespace Conj43

variable {n : ℕ}

/-- A cover of the crossing edges of `σ`: size-≥3 Finsets, edge-disjoint (Nodup
concatenation), exhausting `GEdgeSet σ`. -/
def Cover (σ : Equiv.Perm (Fin n)) (Ss : List (Finset (Fin n))) : Prop :=
  (∀ S ∈ Ss, 3 ≤ S.card) ∧ (Ss.flatMap consecutiveEdges).Nodup ∧
    (∀ e, e ∈ Ss.flatMap consecutiveEdges ↔ e ∈ GEdgeSet σ)

/-- **Move (identity).** Same edge set ⇒ same cover works. -/
theorem cover_same {σ σ' : Equiv.Perm (Fin n)} {Ss : List (Finset (Fin n))}
    (h : Cover σ Ss) (heq : ∀ e, e ∈ GEdgeSet σ' ↔ e ∈ GEdgeSet σ) : Cover σ' Ss :=
  ⟨h.1, h.2.1, fun e => (h.2.2 e).trans (heq e).symm⟩

/-- **Move (add triangle).** When `GEdgeSet σ'` is `GEdgeSet σ` plus a fresh
winding-one triangle `{b,al,be}`, prepend that Finset to the cover. -/
theorem cover_add_triangle {σ σ' : Equiv.Perm (Fin n)} {Ss : List (Finset (Fin n))}
    (h : Cover σ Ss) {b al be : Fin n} (h1 : b ≠ al) (h2 : al ≠ be) (h3 : b ≠ be)
    (hwind : advD b al + advD al be + advD be b = n)
    (hfresh : ∀ e, e ∈ GEdgeSet σ' ↔
        (e ∈ GEdgeSet σ ∨ e = (b, al) ∨ e = (al, be) ∨ e = (be, b)))
    (hn1 : (b, al) ∉ GEdgeSet σ) (hn2 : (al, be) ∉ GEdgeSet σ) (hn3 : (be, b) ∉ GEdgeSet σ) :
    Cover σ' (({b, al, be} : Finset (Fin n)) :: Ss) := by
  obtain ⟨hc, hnd, hcov⟩ := h
  have htri := consec_triangle h1 h2 h3 hwind
  have hcard3 : ({b, al, be} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_eq_three]; exact ⟨b, al, be, h1, h3, h2, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    rcases List.mem_cons.mp hS with rfl | hS
    · rw [hcard3]
    · exact hc S hS
  · rw [List.flatMap_cons, List.nodup_append]
    refine ⟨consecutiveEdges_nodup _, hnd, ?_⟩
    intro x hx y hy hxy
    have hyσ : y ∈ GEdgeSet σ := (hcov y).mp hy
    rw [htri x] at hx; rw [hxy] at hx
    rcases hx with rfl | rfl | rfl
    · exact hn1 hyσ
    · exact hn2 hyσ
    · exact hn3 hyσ
  · intro e
    rw [List.flatMap_cons, List.mem_append, htri e, hcov e, hfresh e]
    tauto

/-- **Move (subdivide).** When `GEdgeSet σ'` replaces the edge `(al,b)` by the
two-edge path `al → be → b` (both fresh), split the owner cycle of `(al,b)` by
inserting `be`; the resulting family still covers. -/
theorem cover_subdivide {σ σ' : Equiv.Perm (Fin n)} {Ss : List (Finset (Fin n))}
    (h : Cover σ Ss) {al b be : Fin n} (hedgeσ : (al, b) ∈ GEdgeSet σ)
    (harc : advD al be + advD be b = advD al b) (hpbe : 0 < advD al be) (hpb : 0 < advD be b)
    (hfresh : ∀ e, e ∈ GEdgeSet σ' ↔
        ((e ∈ GEdgeSet σ ∧ e ≠ (al, b)) ∨ e = (al, be) ∨ e = (be, b)))
    (hn1 : (al, be) ∉ GEdgeSet σ) (hn2 : (be, b) ∉ GEdgeSet σ) :
    ∃ Ss', Cover σ' Ss' := by
  obtain ⟨hc, hnd, hcov⟩ := h
  obtain ⟨S, hS, hedge⟩ := List.mem_flatMap.mp ((hcov (al, b)).mpr hedgeσ)
  have hperm : (Ss.flatMap consecutiveEdges).Perm
      (consecutiveEdges S ++ (Ss.erase S).flatMap consecutiveEdges) := by
    have hp := (List.perm_cons_erase hS).flatMap_right consecutiveEdges
    rwa [List.flatMap_cons] at hp
  obtain ⟨hndS, hndrest, hdisj⟩ := List.nodup_append.mp (hperm.nodup_iff.mp hnd)
  have hcS3 : 3 ≤ S.card := hc S hS
  have hcS2 : 2 ≤ S.card := by omega
  have hrest_sub : ∀ z ∈ (Ss.erase S).flatMap consecutiveEdges, z ∈ GEdgeSet σ := by
    intro z hz
    obtain ⟨T, hT, hzT⟩ := List.mem_flatMap.mp hz
    exact (hcov z).mp (List.mem_flatMap.mpr ⟨T, List.mem_of_mem_erase hT, hzT⟩)
  have hβS : be ∉ S := by
    intro hbeS
    obtain ⟨_, _, _, hαmin⟩ := (mem_consecutiveEdges_iff S hcS2 al b).mp hedge
    have hbene : be ≠ al := by
      intro hc'; rw [hc', advD_self] at hpbe; exact absurd hpbe (lt_irrefl 0)
    have := hαmin be hbeS hbene; omega
  refine ⟨insert be S :: Ss.erase S, ?_, ?_, ?_⟩
  · intro T hT
    rcases List.mem_cons.mp hT with rfl | hT
    · exact le_trans hcS3 (Finset.card_le_card (Finset.subset_insert be S))
    · exact hc T (List.mem_of_mem_erase hT)
  · rw [List.flatMap_cons, List.nodup_append]
    refine ⟨consecutiveEdges_nodup _, hndrest, ?_⟩
    intro x hx y hy
    rw [consec_insert S hcS2 hβS hedge harc hpbe hpb x] at hx
    intro hxy; rw [hxy] at hx
    rcases hx with ⟨hyS, _⟩ | rfl | rfl
    · exact (hdisj y hyS y hy) rfl
    · exact hn1 (hrest_sub _ hy)
    · exact hn2 (hrest_sub _ hy)
  · intro e
    rw [List.flatMap_cons, List.mem_append,
        consec_insert S hcS2 hβS hedge harc hpbe hpb e, hfresh e]
    constructor
    · rintro ((⟨hSe, hne⟩ | rfl | rfl) | hr)
      · exact Or.inl ⟨(hcov e).mp (hperm.mem_iff.mpr (List.mem_append.mpr (Or.inl hSe))), hne⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · refine Or.inl ⟨hrest_sub e hr, ?_⟩
        intro habeq; rw [habeq] at hr
        exact (hdisj (al, b) hedge (al, b) hr) rfl
    · rintro (⟨hσ, hne⟩ | rfl | rfl)
      · rcases List.mem_append.mp (hperm.mem_iff.mp ((hcov e).mpr hσ)) with hSe | hr
        · exact Or.inl (Or.inl ⟨hSe, hne⟩)
        · exact Or.inr hr
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inl (Or.inr (Or.inr rfl))

end Conj43

