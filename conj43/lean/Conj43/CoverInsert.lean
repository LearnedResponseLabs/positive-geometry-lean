/-
Conj43/CoverInsert.lean — the insertion identity (§5 cases 4/6, §6 subdivision).
Inserting the arc-point `be` into `S` splits the cyclic edge `(al,b)` into the
two-edge path `al → be → b`, leaving every other edge unchanged. Proved from the
argmin characterisation (SeedCover) via the modular sub-facts (CoverSurgery).
Verified computationally by a script not included here (e), n≤7, 0 mismatches.
-/
import Conj43.CoverSurgery

namespace Conj43

variable {n : ℕ}

/-- **Insertion identity.** For `be ∉ S`, with `(al,b)` a cyclic edge of `S` and
`be` strictly inside the forward arc `(al,b)` (`advD al be + advD be b = advD al b`,
both positive), the consecutive edges of `insert be S` are those of `S` with
`(al,b)` replaced by `(al,be)` and `(be,b)`. -/
theorem consec_insert (S : Finset (Fin n)) (h2 : 2 ≤ S.card) {al b be : Fin n}
    (hβS : be ∉ S) (hedge : (al, b) ∈ consecutiveEdges S)
    (harc : advD al be + advD be b = advD al b)
    (hpbe : 0 < advD al be) (hpb : 0 < advD be b) (e : Fin n × Fin n) :
    e ∈ consecutiveEdges (insert be S) ↔
      (e ∈ consecutiveEdges S ∧ e ≠ (al, b)) ∨ e = (al, be) ∨ e = (be, b) := by
  obtain ⟨u, v⟩ := e
  have hTcard : 2 ≤ (insert be S).card :=
    le_trans h2 (Finset.card_le_card (Finset.subset_insert be S))
  obtain ⟨halS, hbS, halb, hαmin⟩ := (mem_consecutiveEdges_iff S h2 al b).mp hedge
  have halbe : al ≠ be := by intro hc; rw [hc, advD_self] at hpbe; exact absurd hpbe (lt_irrefl 0)
  have hbeb : be ≠ b := by intro hc; rw [hc, advD_self] at hpb; exact absurd hpb (lt_irrefl 0)
  have hsym := advD_add_symm halbe
  have hltab := advD_lt al b
  have hbe_min : ∀ w ∈ S, advD be b ≤ advD be w := by
    intro w hw
    by_cases hwal : w = al
    · subst hwal; omega
    · exact beta_succ harc hpbe hpb (hαmin w hw hwal)
  have halT : al ∈ insert be S := Finset.mem_insert_of_mem halS
  have hbT : b ∈ insert be S := Finset.mem_insert_of_mem hbS
  have hbeT : be ∈ insert be S := Finset.mem_insert_self be S
  constructor
  · -- forward: an edge of `insert be S` is one of the RHS cases
    intro he
    obtain ⟨huT, hvT, huv, hTmin⟩ := (mem_consecutiveEdges_iff (insert be S) hTcard u v).mp he
    rcases Finset.mem_insert.mp huT with hu_eq | huS
    · -- u = be : successor is b
      have hvS : v ∈ S := by
        rcases Finset.mem_insert.mp hvT with hv | hv
        · exact absurd (hu_eq.trans hv.symm) huv
        · exact hv
      have hbu : b ≠ u := by rw [hu_eq]; exact Ne.symm hbeb
      have h1 : advD u v ≤ advD u b := hTmin b hbT hbu
      have h2' : advD u b ≤ advD u v := by rw [hu_eq]; exact hbe_min v hvS
      have hvb : v = b := advD_inj u (le_antisymm h1 h2')
      right; right; rw [hu_eq, hvb]
    · rcases eq_or_ne u al with hu_eq | hual
      · -- u = al : successor is be
        rcases Finset.mem_insert.mp hvT with hv | hvS
        · right; left; rw [hu_eq, hv]
        · exfalso
          have h1 : advD al v ≤ advD al be := by
            have h := hTmin be hbeT (by rw [hu_eq]; exact Ne.symm halbe); rwa [hu_eq] at h
          have h2' : advD al b ≤ advD al v :=
            hαmin v hvS (fun hc => huv (hu_eq.trans hc.symm))
          omega
      · -- u ∈ S, u ≠ al : the old S-edge survives
        left
        obtain ⟨vS, hvSedge⟩ := succ_exists S h2 huS
        obtain ⟨_, hvSS, huvS, hvSmin⟩ := (mem_consecutiveEdges_iff S h2 u vS).mp hvSedge
        have hbnc : advD u vS ≤ advD u be :=
          beta_not_closer harc hpbe hpb (hvSmin al halS (Ne.symm hual)) (hαmin u huS hual)
        have hbeu : be ≠ u := by intro h; rw [h] at hβS; exact hβS huS
        have hle_vS : advD u v ≤ advD u vS :=
          hTmin vS (Finset.mem_insert_of_mem hvSS) (Ne.symm huvS)
        have hvne : v ≠ be := by
          intro hv
          have hEq : advD u vS = advD u be := le_antisymm hbnc (hv ▸ hle_vS)
          exact hβS ((advD_inj u hEq) ▸ hvSS)
        have hvS : v ∈ S := by
          rcases Finset.mem_insert.mp hvT with hv | hv
          · exact absurd hv hvne
          · exact hv
        have hvvS : v = vS := advD_inj u (le_antisymm hle_vS (hvSmin v hvS (Ne.symm huv)))
        rw [hvvS]
        exact ⟨hvSedge, fun hc => hual (congrArg Prod.fst hc)⟩
  · -- backward: each RHS case is an edge of `insert be S`
    rintro (⟨heS, hne⟩ | he | he)
    · obtain ⟨huS, hvS, huv, hSmin⟩ := (mem_consecutiveEdges_iff S h2 u v).mp heS
      rw [mem_consecutiveEdges_iff (insert be S) hTcard u v]
      refine ⟨Finset.mem_insert_of_mem huS, Finset.mem_insert_of_mem hvS, huv, ?_⟩
      intro w hw hwu
      rcases Finset.mem_insert.mp hw with hw_eq | hwS
      · rcases eq_or_ne u al with hu_eq | hual
        · exfalso
          have hvb : v = b := succ_unique S h2 (hu_eq ▸ heS) hedge
          exact hne (by rw [hu_eq, hvb])
        · rw [hw_eq]
          exact beta_not_closer harc hpbe hpb (hSmin al halS (Ne.symm hual)) (hαmin u huS hual)
      · exact hSmin w hwS hwu
    · injection he with hua hvbe
      rw [hua, hvbe, mem_consecutiveEdges_iff (insert be S) hTcard al be]
      refine ⟨halT, hbeT, halbe, ?_⟩
      intro w hw hwu
      rcases Finset.mem_insert.mp hw with hw_eq | hwS
      · exact le_of_eq (by rw [hw_eq])
      · have := hαmin w hwS hwu; omega
    · injection he with hube hvb
      rw [hube, hvb, mem_consecutiveEdges_iff (insert be S) hTcard be b]
      refine ⟨hbeT, hbT, hbeb, ?_⟩
      intro w hw hwu
      rcases Finset.mem_insert.mp hw with hw_eq | hwS
      · exact absurd hw_eq hwu
      · exact hbe_min w hwS

end Conj43
