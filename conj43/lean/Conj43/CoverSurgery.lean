/-
Conj43/CoverSurgery.lean — the `Cover` invariant and its three surgery moves
(identity / add-triangle / subdivide), built on the argmin characterisation of
`consecutiveEdges` (SeedCover.lean). These are the generic combinatorial steps
consumed by the §7 backward induction; the window/κ-lift geometry that supplies
their hypotheses lives in WindowSwap.lean.
-/
import Conj43.SeedCover

namespace Conj43

variable {n : ℕ}

/-! ### Basic facts about `consecutiveEdges` -/

theorem consecutiveEdges_length (S : Finset (Fin n)) :
    (consecutiveEdges S).length = S.card := by
  unfold consecutiveEdges cycleEdgesD
  rw [List.length_zip, List.length_rotate, Nat.min_self, Finset.length_sort]

theorem consecutiveEdges_nodup (S : Finset (Fin n)) : (consecutiveEdges S).Nodup := by
  unfold consecutiveEdges cycleEdgesD
  apply List.Nodup.of_map Prod.fst
  rw [List.map_fst_zip (le_of_eq (List.length_rotate _ _).symm)]
  exact Finset.sort_nodup _ _

/-- The two directed arcs between distinct points sum to a full turn. -/
theorem advD_add_symm {x y : Fin n} (h : x ≠ y) : advD x y + advD y x = n := by
  have hn : 0 < n := by have := x.isLt; omega
  have hxy : (x : ℕ) ≠ (y : ℕ) := fun hc => h (Fin.ext hc)
  rw [advD_eq_step, advD_eq_step]
  rcases step_spec hn x.isLt y.isLt with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases step_spec hn y.isLt x.isLt with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> omega

/-! ### The triangle identity (§5 case 5 / §6) -/

/-- A winding-one triangle `b → al → be → b` (advances summing to `n`) is exactly
the consecutive-edge set of `{b, al, be}`. -/
theorem consec_triangle {b al be : Fin n} (h1 : b ≠ al) (h2 : al ≠ be) (h3 : b ≠ be)
    (hwind : advD b al + advD al be + advD be b = n) (e : Fin n × Fin n) :
    e ∈ consecutiveEdges ({b, al, be} : Finset (Fin n)) ↔
      e = (b, al) ∨ e = (al, be) ∨ e = (be, b) := by
  set S : Finset (Fin n) := {b, al, be} with hS
  have hcard : S.card = 3 := by
    rw [hS, Finset.card_eq_three]; exact ⟨b, al, be, h1, h3, h2, rfl⟩
  have h2c : 2 ≤ S.card := by omega
  have hbS : b ∈ S := by rw [hS]; simp
  have halS : al ∈ S := by rw [hS]; simp
  have hbeS : be ∈ S := by rw [hS]; simp
  have hs1 := advD_add_symm h3
  have hs2 := advD_add_symm h1
  have hs3 := advD_add_symm h2
  have ineq1 : advD b al ≤ advD b be := by omega
  have ineq2 : advD al be ≤ advD al b := by omega
  have ineq3 : advD be b ≤ advD be al := by omega
  have mem_ba : (b, al) ∈ consecutiveEdges S := by
    rw [mem_consecutiveEdges_iff S h2c]
    refine ⟨hbS, halS, h1, ?_⟩
    intro w hw hwb; rw [hS] at hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact absurd rfl hwb
    · exact le_refl _
    · exact ineq1
  have mem_albe : (al, be) ∈ consecutiveEdges S := by
    rw [mem_consecutiveEdges_iff S h2c]
    refine ⟨halS, hbeS, h2, ?_⟩
    intro w hw hwal; rw [hS] at hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact ineq2
    · exact absurd rfl hwal
    · exact le_refl _
  have mem_beb : (be, b) ∈ consecutiveEdges S := by
    rw [mem_consecutiveEdges_iff S h2c]
    refine ⟨hbeS, hbS, h3.symm, ?_⟩
    intro w hw hwbe; rw [hS] at hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact le_refl _
    · exact ineq3
    · exact absurd rfl hwbe
  -- Nodup length-3 list containing 3 distinct members ⇒ exactly those members
  have hnodup := consecutiveEdges_nodup S
  have hlen : (consecutiveEdges S).length = 3 := by rw [consecutiveEdges_length, hcard]
  have hd1 : (b, al) ≠ (al, be) := fun hc => h1 (Prod.ext_iff.mp hc).1
  have hd2 : (b, al) ≠ (be, b) := fun hc => h3 (Prod.ext_iff.mp hc).1
  have hd3 : (al, be) ≠ (be, b) := fun hc => h2 (Prod.ext_iff.mp hc).1
  have hsub : ({(b, al), (al, be), (be, b)} : Finset (Fin n × Fin n))
      ⊆ (consecutiveEdges S).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [List.mem_toFinset]
    rcases hx with rfl | rfl | rfl
    · exact mem_ba
    · exact mem_albe
    · exact mem_beb
  have hcard3 : ({(b, al), (al, be), (be, b)} : Finset (Fin n × Fin n)).card = 3 := by
    rw [Finset.card_eq_three]; exact ⟨_, _, _, hd1, hd2, hd3, rfl⟩
  have hcardL : (consecutiveEdges S).toFinset.card = 3 := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  have heqF : (consecutiveEdges S).toFinset
      = ({(b, al), (al, be), (be, b)} : Finset (Fin n × Fin n)) :=
    (Finset.eq_of_subset_of_card_le hsub (le_of_eq (hcardL.trans hcard3.symm))).symm
  rw [← List.mem_toFinset, heqF]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-! ### Modular sub-facts for the insertion identity (§5 cases 4/6) -/

/-- `b` is the forward-nearest element of `S` from the inserted point `be`
(its cyclic successor), where `be` sits in the arc `(al, b)`. -/
theorem beta_succ {al be b w : Fin n}
    (harc : advD al be + advD be b = advD al b)
    (hpbe : 0 < advD al be) (hpb : 0 < advD be b)
    (hargmin : advD al b ≤ advD al w) : advD be b ≤ advD be w := by
  have hn : 0 < n := by have := al.isLt; omega
  simp only [advD_eq_step] at harc hpbe hpb hargmin ⊢
  have s1 := step_spec hn al.isLt be.isLt
  have s2 := step_spec hn be.isLt b.isLt
  have s3 := step_spec hn al.isLt b.isLt
  have s4 := step_spec hn al.isLt w.isLt
  have s5 := step_spec hn be.isLt w.isLt
  omega

/-- The inserted point `be` (in the arc `(al,b)`) is never closer to a source
`u ≠ al` than `u`'s own successor `v`. -/
theorem beta_not_closer {al be b u v : Fin n}
    (harc : advD al be + advD be b = advD al b)
    (hpbe : 0 < advD al be) (hpb : 0 < advD be b)
    (huv_al : advD u v ≤ advD u al) (hal_u : advD al b ≤ advD al u) :
    advD u v ≤ advD u be := by
  have hn : 0 < n := by have := al.isLt; omega
  simp only [advD_eq_step] at harc hpbe hpb huv_al hal_u ⊢
  have s1 := step_spec hn al.isLt be.isLt
  have s2 := step_spec hn be.isLt b.isLt
  have s3 := step_spec hn al.isLt b.isLt
  have s4 := step_spec hn u.isLt v.isLt
  have s5 := step_spec hn u.isLt b.isLt
  have s6 := step_spec hn u.isLt al.isLt
  have s7 := step_spec hn al.isLt u.isLt
  have s8 := step_spec hn u.isLt be.isLt
  omega

/-- Every vertex of a size-≥2 set has a cyclic successor. -/
theorem succ_exists (S : Finset (Fin n)) (h2 : 2 ≤ S.card) {u : Fin n} (hu : u ∈ S) :
    ∃ v, (u, v) ∈ consecutiveEdges S := by
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort _
  obtain ⟨i, hi, hui⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr hu)
  have hkpos : 0 < (S.sort (· ≤ ·)).length := by omega
  have hs : (i + 1) % (S.sort (· ≤ ·)).length < (S.sort (· ≤ ·)).length := Nat.mod_lt _ hkpos
  exact ⟨_, (edge_index_mem S u _).mpr ⟨i, hi, hs, hui, rfl⟩⟩

/-- The cyclic successor is unique. -/
theorem succ_unique (S : Finset (Fin n)) (h2 : 2 ≤ S.card) {u v v' : Fin n}
    (h : (u, v) ∈ consecutiveEdges S) (h' : (u, v') ∈ consecutiveEdges S) : v = v' := by
  rw [mem_consecutiveEdges_iff S h2] at h h'
  obtain ⟨_, hvS, huv, hmin⟩ := h
  obtain ⟨_, hv'S, huv', hmin'⟩ := h'
  exact advD_inj u (le_antisymm (hmin v' hv'S huv'.symm) (hmin' v hvS huv.symm))

end Conj43
