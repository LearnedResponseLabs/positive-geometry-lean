/-
Conj43/Seed.lean — the seed decomposition of prop:wp, plus assembly.

`crossEdges_subset_cover` — the directed crossing edges of `G_f^x` are the disjoint
union of the cyclic consecutive-edge lists of subsets of size ≥ 3 — is now PROVED
sorry-free (`seed_cover_proof`, Conj43/SeedProof.lean) via the decorated-window
induction (the combinatorial second proof of prop:wp; no Postnikov/topology input):
window state space + adjacent-active-ascent swap (WindowAscent), inversion measure,
the §5 exact local edge-transition (SeedTable*/WindowSwap), and cover surgery
(Cover/CoverSurgery/CoverInsert). Historically this statement was L3's single
isolated sorry (the topological input of the paper's strand-diagram proof);
the L3B rung replaced it with the window-induction proof.

Everything downstream — turning such a cover into vertex-simple winding-one length-≥3
cycles whose edges exhaust `crossEdges F` — is proved sorry-free in `Conj43/Winding.lean`.
-/
import Conj43.Winding
import Conj43.SeedProof

namespace Conj43

/-- **Seed (proved).** The directed crossing edges decompose as the consecutive-edge
lists of a family of size-≥3 subsets. Proved by the decorated-window induction
(`seed_cover_proof`); formerly the spine's one remaining `sorry`. -/
theorem crossEdges_subset_cover (n : ℕ) (F : LooplessBAP n) :
    ∃ Ss : List (Finset (Fin n)),
      (∀ S ∈ Ss, 3 ≤ S.card) ∧
      (Ss.flatMap consecutiveEdges).Perm (crossEdges F) := by
  exact seed_cover_proof n F

/-- **prop:wp (W-P), assembled.** Uses the proved seed above and the
cover→conclusion engine. Concludes in the `windingD`/`cycleEdgesD` copies, which are
definitionally the pinned `winding`/`cycleEdges`; the glue in `Statements.lean` bridges
them by `rfl`. -/
theorem winding_one_partition_D (n : ℕ) (F : LooplessBAP n) :
    ∃ cycles : List (List (Fin n)),
      (∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ windingD c = n) ∧
      (cycles.flatMap cycleEdgesD).Perm (crossEdges F) := by
  obtain ⟨Ss, hcard, hperm⟩ := crossEdges_subset_cover n F
  exact partition_of_cover F Ss hcard hperm

end Conj43
