/-
Conj43/SeedProof.lean — the §7 backward induction and the bridge to the pinned
`crossEdges F`. Strong induction on the inversion co-measure `n·n − inv` reduces
every window to the terminal (identity) via `window_step`, assembling a `Cover`;
the derangement embedding plus the Nodup/Perm bridge discharge `crossEdges F`.
-/
import Conj43.WindowSwap

namespace Conj43

variable {n : ℕ}

/-- **Backward induction (§7).** Every window admits a cover of its crossing
edges. Strong induction on `n·n − inv`. -/
theorem exists_cover_aux :
    ∀ (m : ℕ) (W : Window n), W.measure = m → ∃ Ss, Cover W.σ Ss := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro W hm
    by_cases h : ∃ i, W.Active i
    · obtain ⟨g, hdec, htrans⟩ := window_step W h
      have hgm : g.measure < m := by rw [← hm]; exact hdec
      obtain ⟨Ss, hSs⟩ := IH g.measure hgm g rfl
      exact htrans Ss hSs
    · push_neg at h
      exact ⟨[], terminal_cover W (Equiv.ext fun i => by
        rw [Equiv.Perm.one_apply]; exact h i)⟩

theorem exists_cover (W : Window n) : ∃ Ss, Cover W.σ Ss :=
  exists_cover_aux _ W rfl

/-! ### Bridge to the pinned crossing-edge list -/

theorem mem_crossEdges (F : LooplessBAP n) (e : Fin n × Fin n) :
    e ∈ crossEdges F ↔ CrossEdge F e.1 e.2 := by
  obtain ⟨p, q⟩ := e
  simp only [crossEdges, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨p', q', hcond⟩
    split at hcond
    · rw [Option.some_inj] at hcond
      obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hcond
      subst h1; subst h2; assumption
    · exact absurd hcond (by simp)
  · intro hc
    exact ⟨p, q, by rw [if_pos hc]⟩

theorem crossEdges_nodup (F : LooplessBAP n) : (crossEdges F).Nodup := by
  rw [crossEdges, List.nodup_flatMap]
  refine ⟨fun p _ => ?_, ?_⟩
  · apply List.Nodup.filterMap ?_ (List.nodup_finRange n)
    intro q q' b hb hb'
    split at hb <;> split at hb' <;> simp_all [Prod.ext_iff]
  · apply List.Nodup.pairwise_of_forall_ne (List.nodup_finRange n)
    intro p _ p' _ hpp'
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro e he he'
    rw [List.mem_filterMap] at he he'
    obtain ⟨q, _, hq⟩ := he
    obtain ⟨q', _, hq'⟩ := he'
    split at hq <;> split at hq' <;> simp_all [Prod.ext_iff]

/-- **Seed lemma, discharged.** The crossing edges of a loopless cell decompose as
consecutive-edge lists of size-≥3 Finsets. -/
theorem seed_cover_proof (n : ℕ) (F : LooplessBAP n) :
    ∃ Ss : List (Finset (Fin n)),
      (∀ S ∈ Ss, 3 ≤ S.card) ∧
      (Ss.flatMap consecutiveEdges).Perm (crossEdges F) := by
  obtain ⟨Ss, hc, hnd, hcov⟩ := exists_cover (Window.ofDerangement F)
  rw [Window.ofDerangement_σ] at hcov
  refine ⟨Ss, hc, ?_⟩
  rw [List.perm_ext_iff_of_nodup hnd (crossEdges_nodup F)]
  intro e
  rw [hcov e, mem_GEdgeSet_iff_cross, mem_crossEdges]

end Conj43
