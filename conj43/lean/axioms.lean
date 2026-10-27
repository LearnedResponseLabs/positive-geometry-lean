/-
axioms.lean — the spine axiom report.

Run from this directory:

    ~/.elan/bin/lake env lean axioms.lean

Every line must read `[propext, Classical.choice, Quot.sound]` — the three
standard Lean/Mathlib axioms, no `sorryAx`, no `Lean.ofReduceBool`
(`native_decide`), no project-declared `axiom`.

Since L4 (2026-09-15) all four statements are over the WIDENED `LooplessBAP`:
loop-free only, with coloops (fixed points of ā, f(i)=i+n) admitted.
-/
import Conj43

#print axioms Conj43.cot_cycle_inequality
#print axioms Conj43.rowdiff
#print axioms Conj43.crossEdges_subset_cover
#print axioms Conj43.winding_one_partition

-- The L4 coloop layer (audit surface for the widening).
#print axioms Conj43.not_crossEdge_of_coloop_fst
#print axioms Conj43.coloop_mem_necklace
#print axioms Conj43.Bmat_coloop_row
#print axioms Conj43.PDM_coloop_row
