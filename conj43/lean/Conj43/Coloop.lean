/-
Conj43/Coloop.lean — L4: the coloop facts that make the widened `LooplessBAP`
(loop-free only; a fixed point of σ is a coloop f(p) = p+n) carry the same
spine as the old fixed-point-free core.

This file formalizes the "Coloops" step of the paper's prop:rowdiff and the
statement of sec:reduction that "a label fixed by ā — a coloop, f(p)=p+n — is
an isolated vertex of G_f^x and carries no crossing, so it contributes nothing
to B": no crossing edge meets a coloop; a coloop lies in every necklace row;
the necklace is stationary across a coloop step; and both sides of the
row-difference identity vanish on a coloop row.

Everything here is proved from the pinned definitions. Nothing downstream
depends on this file — it is the audit surface for the widening.
-/
import Conj43.RowDiff

namespace Conj43

variable {n : ℕ}

/-! ### Coloops are fixed by σ and by σ⁻¹ -/

theorem isColoop_iff_inv (F : LooplessBAP n) (p : Fin n) :
    IsColoop F p ↔ F.σ⁻¹ p = p := (inv_fix_iff F p).symm

theorem isColoop_val (F : LooplessBAP n) {p : Fin n} (hp : IsColoop F p) :
    (F.σ⁻¹ p : ℕ) = (p : ℕ) := by
  rw [(isColoop_iff_inv F p).mp hp]

/-! ### A coloop is an isolated vertex of `G_f^x` -/

/-- No directed crossing has a coloop as its tail. -/
theorem not_crossEdge_of_coloop_fst (F : LooplessBAP n) {p q : Fin n}
    (hp : IsColoop F p) : ¬ CrossEdge F p q := fun hc =>
  (crossEdge_ne_inv F hc).1 (isColoop_val F hp)

/-- No directed crossing has a coloop as its head. -/
theorem not_crossEdge_of_coloop_snd (F : LooplessBAP n) {p q : Fin n}
    (hq : IsColoop F q) : ¬ CrossEdge F p q := fun hc =>
  (crossEdge_ne_inv F hc).2 (isColoop_val F hq)

/-- **Isolated vertex.** A coloop is an endpoint of no column of `B`/`M_N`. -/
theorem coloop_notMem_crossEdges (F : LooplessBAP n) {p : Fin n}
    (hp : IsColoop F p) {e : Fin n × Fin n} (he : e ∈ crossEdges F) :
    e.1 ≠ p ∧ e.2 ≠ p := by
  have hc := crossEdge_of_mem F he
  constructor
  · rintro rfl; exact not_crossEdge_of_coloop_fst F hp hc
  · rintro rfl; exact not_crossEdge_of_coloop_snd F hp hc

/-! ### A coloop lies in every necklace row -/

/-- **eq:arc at a coloop** (paper: "`A_x` is then the whole row set — `x` lies
in every necklace row"). -/
theorem coloop_mem_necklace (F : LooplessBAP n) {p : Fin n} (hp : IsColoop F p)
    (r : Fin n) : p ∈ necklace F r :=
  (mem_necklace_iff F r p).mpr (inArcC_of_coloop (isColoop_val F hp))

/-- **The necklace is stationary across a coloop step**: `I_{p+2} = I_{p+1}`,
because the recursion removes `p` and puts `ā(p) = p` straight back. -/
theorem necklaceAux_coloop_step (F : LooplessBAP n) {p : ℕ} (hp : p < n)
    (hcol : IsColoop F ⟨p, hp⟩) :
    necklaceAux F (p + 1) = necklaceAux F p := by
  simp only [necklaceAux, dif_pos hp]
  by_cases hmem : (⟨p, hp⟩ : Fin n) ∈ necklaceAux F p
  · rw [if_pos hmem, show F.σ ⟨p, hp⟩ = (⟨p, hp⟩ : Fin n) from hcol,
      Finset.insert_erase hmem]
  · rw [if_neg hmem]

/-! ### Both sides of prop:rowdiff vanish on a coloop row -/

/-- The `B`-row of a coloop is zero. -/
theorem Bmat_coloop_row (F : LooplessBAP n) {p : Fin n} (hp : IsColoop F p)
    (j : EdgeIdx F) : Bmat F p j = 0 := by
  obtain ⟨h1, h2⟩ := coloop_notMem_crossEdges F hp (List.get_mem (crossEdges F) j)
  have h1' : ¬ (p = (edgeOf F j).1) := fun hb => h1 hb.symm
  have h2' : ¬ (p = (edgeOf F j).2) := fun hb => h2 hb.symm
  simp [Bmat, h1', h2']

/-- The `P_f D M_N`-row of a coloop is zero as well — the identity holds there
with both sides zero, which is the paper's "Coloops" step. -/
theorem PDM_coloop_row [NeZero n] (F : LooplessBAP n) {p : Fin n}
    (hp : IsColoop F p) (j : EdgeIdx F) :
    (Pmat F * Dmat n * Mmat F) p j = 0 := by
  rw [rowdiff_proof n F]
  exact Bmat_coloop_row F hp j

end Conj43
