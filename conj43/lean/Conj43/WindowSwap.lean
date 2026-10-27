/-
Conj43/WindowSwap.lean — window dynamics: the inversion measure, the derangement
embedding, the empty (terminal) cover, and the single reduction step
`window_step` that bundles §3 (adjacent active ascent exists), §4 (inv strictly
increases) and §5 (the local edge-transition) into a cover-transforming move.
-/
import Conj43.Cover
import Conj43.WindowAscent
import Conj43.SeedTableMaster

namespace Conj43

variable {n : ℕ}

namespace Window

/-- Inversions of the lift: pairs `i<j` (as labels) with `w i > w j`. -/
def inv (W : Window n) : ℕ :=
  (Finset.univ.filter
    (fun p : Fin n × Fin n => (p.1 : ℕ) < (p.2 : ℕ) ∧ W.w p.2 < W.w p.1)).card

theorem inv_le (W : Window n) : W.inv ≤ n * n := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- The fixed-point-free derangement `F` embeds as an all-active window. -/
def ofDerangement (F : LooplessBAP n) : Window n where
  σ := F.σ
  w := fun i => if (i : ℕ) < (F.σ i : ℕ) then (F.σ i : ℕ) else (F.σ i : ℕ) + n
  hres := by
    intro i; split
    · exact Nat.mod_eq_of_lt (F.σ i).isLt
    · rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt (F.σ i).isLt
  hlb := by
    intro i; have := i.isLt; have := (F.σ i).isLt; split <;> omega
  hub := by
    intro i; have := i.isLt; have := (F.σ i).isLt; split <;> omega

@[simp] theorem ofDerangement_σ (F : LooplessBAP n) : (ofDerangement F).σ = F.σ := rfl

end Window

/-- The identity permutation carries no crossing edges. -/
theorem not_GCross_one {p q : Fin n} : ¬ GCross (1 : Equiv.Perm (Fin n)) p q := by
  have hp := p.isLt; have hq := q.isLt
  have hn : 0 < n := by omega
  unfold GCross
  simp only [inv_one, Equiv.Perm.one_apply]
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem GEdgeSet_one : GEdgeSet (1 : Equiv.Perm (Fin n)) = ∅ := by
  ext e
  constructor
  · intro he; exact absurd (mem_GEdgeSet.mp he) not_GCross_one
  · intro he; exact absurd he (Finset.notMem_empty e)

/-- **Terminal cover.** The identity window's crossing graph is empty; the empty
family covers it. -/
theorem terminal_cover (W : Window n) (hσ : W.σ = 1) : Cover W.σ [] := by
  refine ⟨by simp, by simp, ?_⟩
  intro e
  rw [hσ, GEdgeSet_one]
  simp

/-- **§5 (the doubly machine-verified core).** The `(a,b)`-swap changes only the
edges among `{b, α, β}` (`α = σa, β = σb`), and the change is one of identity /
triangle-append / left- or right-subdivision (PROOF.md §5 table, formalized in
`SeedTableMaster`; verified by an exact table audit (script not included): n≤7, 44,745 pairs, 0 fails).
Discharged by `cover_same` / `cover_add_triangle` / `cover_subdivide`. -/
theorem edge_transition (W : Window n) {a b : Fin n} (hab : a < b) (haact : W.Active a)
    (hbact : W.Active b) (hadj : ∀ c : Fin n, a < c → c < b → ¬ W.Active c)
    (hasc : W.w a < W.w b) {h1 h2 h3 h4} (Ss : List (Finset (Fin n)))
    (hCov : Cover (W.swapWindow a b hab h1 h2 h3 h4).σ Ss) :
    ∃ Ss', Cover W.σ Ss' := by
  rw [Window.swapWindow_σ] at hCov
  obtain ⟨hbA', hBan⟩ := W.ascent_bounds hab haact hbact hadj
  rcases eq_or_lt_of_le hbA' with hAb | hbA
  · -- A = b : identity transition
    exact ⟨Ss, cover_same hCov
      (Window.master_identity hab haact hbact hadj hBan hAb.symm)⟩
  · -- A > b : the three table regimes
    obtain ⟨c, hc⟩ : ∃ c, W.σ⁻¹ b = c := ⟨W.σ⁻¹ b, rfl⟩
    have hσc : W.σ c = b := by rw [← hc, perm_apply_inv']
    have hαb : W.σ a ≠ b := Window.alpha_ne_b haact hab hbA
    have hca : c ≠ a := fun h => hαb (h ▸ hσc)
    have hcb : c ≠ b := fun h => hbact (h ▸ hσc)
    have hcact : W.Active c := fun hfix => hcb (hσc.symm.trans hfix).symm
    have hcpos' := Window.pos_avoid hadj hcact hcb
    have hcane : (c : ℕ) ≠ (a : ℕ) := fun h => hca (Fin.ext h)
    have hcpos : (c : ℕ) < (a : ℕ) ∨ (b : ℕ) < (c : ℕ) := by
      rcases hcpos' with h | h
      · left; omega
      · right; exact h
    obtain ⟨S, hS⟩ : ∃ S : ℕ,
        ((c : ℕ) < (a : ℕ) ∧ S = (c : ℕ) + n) ∨ ((b : ℕ) < (c : ℕ) ∧ S = (c : ℕ)) := by
      rcases hcpos with h | h
      · exact ⟨(c : ℕ) + n, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨(c : ℕ), Or.inr ⟨h, rfl⟩⟩
    have hαd := lift_decomp W a
    have hβd := lift_decomp W b
    have hA1 := W.active_strict haact
    have hB1 := W.active_strict hbact
    have habn : (a : ℕ) < (b : ℕ) := hab
    have hadv_bα : advD b (W.σ a) = W.w a - (b : ℕ) :=
      advD_of_lifts (Or.inl rfl) hαd hbA (by omega)
    have hadv_αβ : advD (W.σ a) (W.σ b) = W.w b - W.w a :=
      advD_of_lifts hαd hβd hasc (by omega)
    have hadv_βb : advD (W.σ b) b = (b : ℕ) + n - W.w b :=
      advD_of_lifts hβd (Or.inr rfl) hB1.2 (by omega)
    have hadv_αb : advD (W.σ a) b = (b : ℕ) + n - W.w a :=
      advD_of_lifts hαd (Or.inr rfl) (by omega) (by omega)
    have hadv_bβ : advD b (W.σ b) = W.w b - (b : ℕ) :=
      advD_of_lifts (Or.inl rfl) hβd hB1.1 (by omega)
    rcases Nat.lt_or_ge S (W.w a) with hSA | hAS
    · -- LEFT subdivision: remove (α,b), insert β on the path α→β→b
      obtain ⟨hedge, hn1, hn2, hfresh⟩ :=
        Window.master_left hab haact hbact hadj hasc hBan hbA hc hS hSA
      exact cover_subdivide hCov hedge
        (by rw [hadv_αβ, hadv_βb, hadv_αb]; omega)
        (by rw [hadv_αβ]; omega)
        (by rw [hadv_βb]; omega)
        hfresh hn1 hn2
    rcases Nat.lt_or_ge S (W.w b) with hSB | hBS
    · -- TRIANGLE: append the fresh winding-one triangle {b, α, β}
      obtain ⟨hn1, hn2, hn3, hfresh⟩ :=
        Window.master_triangle hab haact hbact hadj hasc hBan hbA hc hS hAS hSB
      refine ⟨_, cover_add_triangle hCov (Ne.symm hαb)
        (fun h => (ne_of_lt hab) (W.σ.injective h)) (Ne.symm hbact)
        (by rw [hadv_bα, hadv_αβ, hadv_βb]; omega)
        hfresh hn1 hn2 hn3⟩
    · -- RIGHT subdivision: remove (b,β), insert α on the path b→α→β
      obtain ⟨hedge, hn1, hn2, hfresh⟩ :=
        Window.master_right hab haact hbact hadj hasc hBan hbA hc hS hBS
      exact cover_subdivide hCov hedge
        (by rw [hadv_bα, hadv_αβ, hadv_bβ]; omega)
        (by rw [hadv_bα]; omega)
        (by rw [hadv_αβ]; omega)
        hfresh hn1 hn2

theorem window_step (W : Window n) (h : ∃ i, W.Active i) :
    ∃ g : Window n, g.measure < W.measure ∧
      (∀ Ss, Cover g.σ Ss → ∃ Ss', Cover W.σ Ss') := by
  obtain ⟨a, b, hab, haact, hbact, hadj, hasc⟩ := Window.ascent_exists W h
  obtain ⟨hb_wa, hwb_an⟩ := W.ascent_bounds hab haact hbact hadj
  obtain ⟨haS_lo, haS_hi⟩ := W.active_strict haact
  obtain ⟨hbS_lo, hbS_hi⟩ := W.active_strict hbact
  have habn : (a : ℕ) < (b : ℕ) := hab
  have h3 : (a : ℕ) ≤ W.w b := by omega
  have h4 : W.w a ≤ (b : ℕ) + n := by omega
  refine ⟨W.swapWindow a b hab hb_wa hwb_an h3 h4, ?_, ?_⟩
  · exact W.swap_measure_lt a b hab hb_wa hwb_an h3 h4 hasc
  · exact fun Ss hCov => edge_transition W hab haact hbact hadj hasc Ss hCov

end Conj43
