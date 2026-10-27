/-
Conj43/SeedTableLocal.lean — §5 locality: pairs not inside {b, α, β} keep their
crossing verdict across the (a,b)-swap. Trivial for pairs missing both moved
labels (identical points); mixed pairs via the move lemma (the three stationary
endpoints avoid the swept arc, PAPER_SECTION.tex three-stationary-points
argument); fixed labels are edge-free on both sides.
-/
import Conj43.SeedTableVerdicts
import Conj43.WindowAscent

namespace Conj43

variable {n : ℕ}

theorem perm_apply_inv' (σ : Equiv.Perm (Fin n)) (x : Fin n) : σ (σ⁻¹ x) = x := by
  rw [Equiv.Perm.inv_def]
  exact σ.apply_symm_apply x

theorem perm_inv_apply' (σ : Equiv.Perm (Fin n)) (x : Fin n) : σ⁻¹ (σ x) = x := by
  rw [Equiv.Perm.inv_def]
  exact σ.symm_apply_apply x

theorem mul_swap_inv_apply (σ : Equiv.Perm (Fin n)) (a b x : Fin n) :
    (σ * Equiv.swap a b)⁻¹ x = Equiv.swap a b (σ⁻¹ x) := by
  rw [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]

namespace Window

variable {W : Window n} {a b : Fin n}

/-- Positions of active labels avoid the open ascent gap `(a, b]`. -/
theorem pos_avoid (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x)
    {x : Fin n} (hx : W.Active x) (hxb : x ≠ b) : (x : ℕ) ≤ (a : ℕ) ∨ (b : ℕ) < (x : ℕ) := by
  rcases Nat.lt_or_ge (a : ℕ) (x : ℕ) with h | h
  · right
    rcases Nat.lt_or_ge (x : ℕ) (b : ℕ) with h2 | h2
    · exact absurd hx (hadj x h h2)
    · have : (x : ℕ) ≠ (b : ℕ) := fun hh => hxb (Fin.ext hh)
      omega
  · left; exact h

/-- The inverse position of an active label is active. -/
theorem inv_active {q : Fin n} (hq : W.Active q) : W.Active (W.σ⁻¹ q) := by
  intro hcon
  have h1 : W.σ (W.σ⁻¹ q) = q := perm_apply_inv' W.σ q
  have h2 : W.σ⁻¹ q = q := hcon.symm.trans h1
  rw [h2] at h1
  exact hq h1

/-- **Trivial locality.** Pairs whose labels are both outside `{α, β}` have
identical endpoint data in `w` and `g`. -/
theorem triv_pair {p q : Fin n} (hp1 : p ≠ W.σ a) (hp2 : p ≠ W.σ b)
    (hq1 : q ≠ W.σ a) (hq2 : q ≠ W.σ b) :
    GCross W.σ p q ↔ GCross (W.σ * Equiv.swap a b) p q := by
  have hpa : W.σ⁻¹ p ≠ a := fun h => hp1 (by rw [← h, perm_apply_inv'])
  have hpb : W.σ⁻¹ p ≠ b := fun h => hp2 (by rw [← h, perm_apply_inv'])
  have hqa : W.σ⁻¹ q ≠ a := fun h => hq1 (by rw [← h, perm_apply_inv'])
  have hqb : W.σ⁻¹ q ≠ b := fun h => hq2 (by rw [← h, perm_apply_inv'])
  have h1 : (W.σ * Equiv.swap a b)⁻¹ p = W.σ⁻¹ p := by
    rw [mul_swap_inv_apply]
    exact Equiv.swap_apply_of_ne_of_ne hpa hpb
  have h2 : (W.σ * Equiv.swap a b)⁻¹ q = W.σ⁻¹ q := by
    rw [mul_swap_inv_apply]
    exact Equiv.swap_apply_of_ne_of_ne hqa hqb
  unfold GCross
  rw [h1, h2]

/-- α is not the label `b` when the ascent is non-degenerate (`A > b`). -/
theorem alpha_ne_b (haact : W.Active a) (hab : a < b) (hbA : (b : ℕ) < W.w a) :
    W.σ a ≠ b := by
  intro hh
  have hres := W.hres a
  rw [hh] at hres
  have h1 := (W.active_strict haact).2
  have ha := a.isLt
  have hbn := b.isLt
  rcases Nat.lt_or_ge (W.w a) n with h2 | h2
  · rw [Nat.mod_eq_of_lt h2] at hres; omega
  · rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)] at hres; omega

/-- **Mixed locality, `(α, q)`.** For `q ∉ {α, β, b}` the moved entry of α sweeps
the arc `(a⁺, b⁺)`, avoided by the three stationary endpoints. -/
theorem mixed_alpha_fst (hab : a < b) (haact : W.Active a) (hbact : W.Active b)
    (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x) (hbA : (b : ℕ) < W.w a)
    (q : Fin n) (hq1 : q ≠ W.σ a) (hq2 : q ≠ W.σ b) (hq3 : q ≠ b) :
    GCross W.σ (W.σ a) q ↔ GCross (W.σ * Equiv.swap a b) (W.σ a) q := by
  by_cases hqfix : W.σ q = q
  · have hqa : q ≠ a := fun h => haact (by rw [← h]; exact hqfix)
    have hgfix : (W.σ * Equiv.swap a b) q = q := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hqa hq3, hqfix]
    exact iff_of_false (not_gcross_fixed_snd hqfix _) (not_gcross_fixed_snd hgfix _)
  · have hqact : W.Active q := hqfix
    have hsact : W.Active (W.σ⁻¹ q) := inv_active hqact
    have hsa : W.σ⁻¹ q ≠ a := fun h => hq1 (by rw [← h, perm_apply_inv'])
    have hsb : W.σ⁻¹ q ≠ b := fun h => hq2 (by rw [← h, perm_apply_inv'])
    have hspos := pos_avoid hadj hsact hsb
    have hsane : ((W.σ⁻¹ q : Fin n) : ℕ) ≠ (a : ℕ) := fun h => hsa (Fin.ext h)
    have hqpos := pos_avoid hadj hqact hq3
    have hαb : W.σ a ≠ b := alpha_ne_b haact hab hbA
    have hαpos := pos_avoid hadj (W.sigma_active haact) hαb
    have hswα : ((W.σ⁻¹ (W.σ a) : Fin n) : ℕ) = (a : ℕ) := by rw [perm_inv_apply']
    have hgswα : (((W.σ * Equiv.swap a b)⁻¹ (W.σ a) : Fin n) : ℕ) = (b : ℕ) := by
      rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_left]
    have hsq : ((W.σ⁻¹ q : Fin n) : ℕ) = ((W.σ⁻¹ q : Fin n) : ℕ) := rfl
    have hgsq : (((W.σ * Equiv.swap a b)⁻¹ q : Fin n) : ℕ) = ((W.σ⁻¹ q : Fin n) : ℕ) := by
      rw [mul_swap_inv_apply, Equiv.swap_apply_of_ne_of_ne hsa hsb]
    rw [gcross_points hswα hsq, gcross_points hgswα hgsq]
    have hb1 := a.isLt
    have hb2 := b.isLt
    have hb3 := q.isLt
    have hb4 := (W.σ⁻¹ q).isLt
    have hb5 := (W.σ a).isLt
    have habn : (a : ℕ) < (b : ℕ) := hab
    exact cw4_move₁ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)

/-- **Mixed locality, `(q, α)`.** -/
theorem mixed_alpha_snd (hab : a < b) (haact : W.Active a) (hbact : W.Active b)
    (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x) (hbA : (b : ℕ) < W.w a)
    (p : Fin n) (hp1 : p ≠ W.σ a) (hp2 : p ≠ W.σ b) (hp3 : p ≠ b) :
    GCross W.σ p (W.σ a) ↔ GCross (W.σ * Equiv.swap a b) p (W.σ a) := by
  by_cases hpfix : W.σ p = p
  · have hpa : p ≠ a := fun h => haact (by rw [← h]; exact hpfix)
    have hgfix : (W.σ * Equiv.swap a b) p = p := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpa hp3, hpfix]
    exact iff_of_false (not_gcross_fixed_fst hpfix _) (not_gcross_fixed_fst hgfix _)
  · have hpact : W.Active p := hpfix
    have hsact : W.Active (W.σ⁻¹ p) := inv_active hpact
    have hsa : W.σ⁻¹ p ≠ a := fun h => hp1 (by rw [← h, perm_apply_inv'])
    have hsb : W.σ⁻¹ p ≠ b := fun h => hp2 (by rw [← h, perm_apply_inv'])
    have hspos := pos_avoid hadj hsact hsb
    have hsane : ((W.σ⁻¹ p : Fin n) : ℕ) ≠ (a : ℕ) := fun h => hsa (Fin.ext h)
    have hppos := pos_avoid hadj hpact hp3
    have hαb : W.σ a ≠ b := alpha_ne_b haact hab hbA
    have hαpos := pos_avoid hadj (W.sigma_active haact) hαb
    have hswα : ((W.σ⁻¹ (W.σ a) : Fin n) : ℕ) = (a : ℕ) := by rw [perm_inv_apply']
    have hgswα : (((W.σ * Equiv.swap a b)⁻¹ (W.σ a) : Fin n) : ℕ) = (b : ℕ) := by
      rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_left]
    have hsp : ((W.σ⁻¹ p : Fin n) : ℕ) = ((W.σ⁻¹ p : Fin n) : ℕ) := rfl
    have hgsp : (((W.σ * Equiv.swap a b)⁻¹ p : Fin n) : ℕ) = ((W.σ⁻¹ p : Fin n) : ℕ) := by
      rw [mul_swap_inv_apply, Equiv.swap_apply_of_ne_of_ne hsa hsb]
    rw [gcross_points hsp hswα, gcross_points hgsp hgswα]
    have hb1 := a.isLt
    have hb2 := b.isLt
    have hb3 := p.isLt
    have hb4 := (W.σ⁻¹ p).isLt
    have hb5 := (W.σ a).isLt
    have habn : (a : ℕ) < (b : ℕ) := hab
    exact cw4_move₂ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)

/-- **Mixed locality, `(β, q)`.** The entry of β moves back along the same arc. -/
theorem mixed_beta_fst (hab : a < b) (haact : W.Active a) (hbact : W.Active b)
    (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x)
    (q : Fin n) (hq1 : q ≠ W.σ a) (hq2 : q ≠ W.σ b) (hq3 : q ≠ b) :
    GCross W.σ (W.σ b) q ↔ GCross (W.σ * Equiv.swap a b) (W.σ b) q := by
  by_cases hqfix : W.σ q = q
  · have hqa : q ≠ a := fun h => haact (by rw [← h]; exact hqfix)
    have hgfix : (W.σ * Equiv.swap a b) q = q := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hqa hq3, hqfix]
    exact iff_of_false (not_gcross_fixed_snd hqfix _) (not_gcross_fixed_snd hgfix _)
  · have hqact : W.Active q := hqfix
    have hsact : W.Active (W.σ⁻¹ q) := inv_active hqact
    have hsa : W.σ⁻¹ q ≠ a := fun h => hq1 (by rw [← h, perm_apply_inv'])
    have hsb : W.σ⁻¹ q ≠ b := fun h => hq2 (by rw [← h, perm_apply_inv'])
    have hspos := pos_avoid hadj hsact hsb
    have hsane : ((W.σ⁻¹ q : Fin n) : ℕ) ≠ (a : ℕ) := fun h => hsa (Fin.ext h)
    have hqpos := pos_avoid hadj hqact hq3
    have hβb : W.σ b ≠ b := hbact
    have hβpos := pos_avoid hadj (W.sigma_active hbact) hβb
    have hswβ : ((W.σ⁻¹ (W.σ b) : Fin n) : ℕ) = (b : ℕ) := by rw [perm_inv_apply']
    have hgswβ : (((W.σ * Equiv.swap a b)⁻¹ (W.σ b) : Fin n) : ℕ) = (a : ℕ) := by
      rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_right]
    have hsq : ((W.σ⁻¹ q : Fin n) : ℕ) = ((W.σ⁻¹ q : Fin n) : ℕ) := rfl
    have hgsq : (((W.σ * Equiv.swap a b)⁻¹ q : Fin n) : ℕ) = ((W.σ⁻¹ q : Fin n) : ℕ) := by
      rw [mul_swap_inv_apply, Equiv.swap_apply_of_ne_of_ne hsa hsb]
    rw [gcross_points hswβ hsq, gcross_points hgswβ hgsq]
    have hb1 := a.isLt
    have hb2 := b.isLt
    have hb3 := q.isLt
    have hb4 := (W.σ⁻¹ q).isLt
    have hb5 := (W.σ b).isLt
    have habn : (a : ℕ) < (b : ℕ) := hab
    exact (cw4_move₁ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)).symm

/-- **Mixed locality, `(q, β)`.** -/
theorem mixed_beta_snd (hab : a < b) (haact : W.Active a) (hbact : W.Active b)
    (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x)
    (p : Fin n) (hp1 : p ≠ W.σ a) (hp2 : p ≠ W.σ b) (hp3 : p ≠ b) :
    GCross W.σ p (W.σ b) ↔ GCross (W.σ * Equiv.swap a b) p (W.σ b) := by
  by_cases hpfix : W.σ p = p
  · have hpa : p ≠ a := fun h => haact (by rw [← h]; exact hpfix)
    have hgfix : (W.σ * Equiv.swap a b) p = p := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpa hp3, hpfix]
    exact iff_of_false (not_gcross_fixed_fst hpfix _) (not_gcross_fixed_fst hgfix _)
  · have hpact : W.Active p := hpfix
    have hsact : W.Active (W.σ⁻¹ p) := inv_active hpact
    have hsa : W.σ⁻¹ p ≠ a := fun h => hp1 (by rw [← h, perm_apply_inv'])
    have hsb : W.σ⁻¹ p ≠ b := fun h => hp2 (by rw [← h, perm_apply_inv'])
    have hspos := pos_avoid hadj hsact hsb
    have hsane : ((W.σ⁻¹ p : Fin n) : ℕ) ≠ (a : ℕ) := fun h => hsa (Fin.ext h)
    have hppos := pos_avoid hadj hpact hp3
    have hβb : W.σ b ≠ b := hbact
    have hβpos := pos_avoid hadj (W.sigma_active hbact) hβb
    have hswβ : ((W.σ⁻¹ (W.σ b) : Fin n) : ℕ) = (b : ℕ) := by rw [perm_inv_apply']
    have hgswβ : (((W.σ * Equiv.swap a b)⁻¹ (W.σ b) : Fin n) : ℕ) = (a : ℕ) := by
      rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_right]
    have hsp : ((W.σ⁻¹ p : Fin n) : ℕ) = ((W.σ⁻¹ p : Fin n) : ℕ) := rfl
    have hgsp : (((W.σ * Equiv.swap a b)⁻¹ p : Fin n) : ℕ) = ((W.σ⁻¹ p : Fin n) : ℕ) := by
      rw [mul_swap_inv_apply, Equiv.swap_apply_of_ne_of_ne hsa hsb]
    rw [gcross_points hsp hswβ, gcross_points hgsp hgswβ]
    have hb1 := a.isLt
    have hb2 := b.isLt
    have hb3 := p.isLt
    have hb4 := (W.σ⁻¹ p).isLt
    have hb5 := (W.σ b).isLt
    have habn : (a : ℕ) < (b : ℕ) := hab
    exact (cw4_move₂ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)).symm

/-- **Nonspecial pairs are unchanged** (`A > b` case): any ordered pair other
than the six within `{α, β, b}` has the same verdict in `w` and `g`. -/
theorem nonspecial (hab : a < b) (haact : W.Active a) (hbact : W.Active b)
    (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x) (hbA : (b : ℕ) < W.w a)
    (p q : Fin n)
    (h1 : (p, q) ≠ (W.σ a, W.σ b)) (h2 : (p, q) ≠ (W.σ b, W.σ a))
    (h3 : (p, q) ≠ (W.σ a, b)) (h4 : (p, q) ≠ (b, W.σ a))
    (h5 : (p, q) ≠ (W.σ b, b)) (h6 : (p, q) ≠ (b, W.σ b)) :
    GCross W.σ p q ↔ GCross (W.σ * Equiv.swap a b) p q := by
  by_cases hpq : p = q
  · subst hpq
    exact iff_of_false (not_gcross_self _ _) (not_gcross_self _ _)
  by_cases hpα : p = W.σ a
  · subst hpα
    exact mixed_alpha_fst hab haact hbact hadj hbA q (fun h => hpq h.symm)
      (fun h => h1 (by rw [h])) (fun h => h3 (by rw [h]))
  by_cases hpβ : p = W.σ b
  · subst hpβ
    exact mixed_beta_fst hab haact hbact hadj q (fun h => h2 (by rw [h]))
      (fun h => hpq h.symm) (fun h => h5 (by rw [h]))
  by_cases hqα : q = W.σ a
  · subst hqα
    exact mixed_alpha_snd hab haact hbact hadj hbA p hpα hpβ (fun h => h4 (by rw [h]))
  by_cases hqβ : q = W.σ b
  · subst hqβ
    exact mixed_beta_snd hab haact hbact hadj p hpα hpβ (fun h => h6 (by rw [h]))
  · exact triv_pair hpα hpβ hqα hqβ

end Window

end Conj43
