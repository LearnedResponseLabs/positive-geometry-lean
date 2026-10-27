/-
Conj43/Statements.lean — the three spine statements and their completed proof terms.

Paper: main.tex of the accompanying paper
  lem:cot     — cotangent cycle inequality
  prop:rowdiff — row-difference identity P_f D M_N = B
  prop:wp     — winding-one partition (W-P)
-/
import Conj43.Defs
import Conj43.CotCycle
import Conj43.RowDiff
import Conj43.FullColumns
import Conj43.Seed

namespace Conj43

/-! ### lem:cot — the cotangent cycle inequality -/

/-- **lem:cot.** Positive angles α₁,…,α_m (m ≥ 3) summing to π, and reals
d₁,…,d_m summing to 0: then Σ cot(αᵢ) dᵢ² ≥ 0, with equality iff all dᵢ = 0.
(Each αᵢ < π is implied by positivity + the sum condition, so `Real.cot` is
evaluated only on (0, π).) Proved sorry-free in `Conj43/CotCycle.lean` (L1). -/
theorem cot_cycle_inequality (m : ℕ) (hm : 3 ≤ m) (α d : Fin m → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = Real.pi) (hd : ∑ i, d i = 0) :
    0 ≤ ∑ i, Real.cot (α i) * d i ^ 2 ∧
      ((∑ i, Real.cot (α i) * d i ^ 2) = 0 ↔ ∀ i, d i = 0) :=
  cot_cycle_inequality_proof m hm α d hα hsum hd

/-! ### prop:rowdiff — the row-difference identity -/

/-- **prop:rowdiff.** For every LOOPLESS bounded affine permutation — coloops
admitted, `f(i) = i+n` at a fixed point of ā (L4, 2026-09-15) — P_f D M_N = B as
integer matrices (columns = directed crossing edges in census order; the paper's
remaining non-crossing pair columns vanish by `pairExponent_nonCross` and
`full_pair_columns_zero`; `rowdiff_full_pairs` includes them in the identity; in particular every pair meeting a coloop is dropped,
since a coloop carries no crossing — `Conj43.not_crossEdge_of_coloop_fst`). The
coloop rows of both sides vanish: `Conj43.Bmat_coloop_row`,
`Conj43.PDM_coloop_row`. -/
theorem rowdiff (n : ℕ) [NeZero n] (F : LooplessBAP n) :
    Pmat F * Dmat n * Mmat F = Bmat F := by
  exact rowdiff_proof n F

/-! ### prop:wp — the winding-one partition -/

/-- **prop:wp (W-P).** For every LOOPLESS bounded affine permutation (coloops
admitted, L4) the directed crossing-edge set of G_f^x is a disjoint
union of edge-disjoint directed cycles, each of total exit-advance n (winding
one) and length ≥ 3. Formalized: a list of vertex-simple cycles (the paper's
proof shows winding-one cycles are automatically vertex-simple) whose edge
lists, concatenated, are a permutation of `crossEdges F` — this encodes
edge-disjointness AND exhaustion, since `crossEdges F` has no duplicates.
Coloops are isolated vertices of G_f^x and simply do not occur in any cycle
(`Conj43.coloop_notMem_crossEdges`). -/
theorem winding_one_partition (n : ℕ) (F : LooplessBAP n) :
    ∃ cycles : List (List (Fin n)),
      (∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n) ∧
      (cycles.flatMap cycleEdges).Perm (crossEdges F) := by
  exact winding_one_partition_D n F

end Conj43
