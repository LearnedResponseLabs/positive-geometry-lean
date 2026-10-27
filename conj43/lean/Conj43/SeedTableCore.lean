/-
Conj43/SeedTableCore.lean — §5 toolkit: cyclic-shift and point-move lemmas for
`Clockwise4`, edge-freeness of self/fixed labels, the `GCross` point evaluator,
and `advD` from integer lifts. All statements validated exhaustively in
checks/scripts/validate_table_abstractions.py (move lemma: 274,456 tuples, 0 fails).
-/
import Conj43.Window

namespace Conj43

variable {n : ℕ}

/-- `Clockwise4` is invariant under cyclic rotation of its four points. -/
theorem cw4_shift {m a b c d : ℕ} : Clockwise4 m a b c d ↔ Clockwise4 m b c d a := by
  unfold Clockwise4
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h2, h3, h4, h1, by omega⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h4, h1, h2, h3, by omega⟩

/-- **Move lemma (slot 1).** Moving one point of a `Clockwise4` configuration
within an interval `[x, x']` avoided strictly by the three stationary points
preserves the predicate. -/
theorem cw4_move₁ {m x x' c d e : ℕ} (hm : 0 < m) (hx : x < m) (hx' : x' < m)
    (hc : c < m) (hd : d < m) (he : e < m) (hxx : x ≤ x')
    (havc : c < x ∨ x' < c) (havd : d < x ∨ x' < d) (have' : e < x ∨ x' < e) :
    Clockwise4 m x c d e ↔ Clockwise4 m x' c d e := by
  rw [cw4_iff_linear hm hx hc hd he, cw4_iff_linear hm hx' hc hd he]
  omega

/-- **Move lemma (slot 2).** -/
theorem cw4_move₂ {m x x' c d e : ℕ} (hm : 0 < m) (hx : x < m) (hx' : x' < m)
    (hc : c < m) (hd : d < m) (he : e < m) (hxx : x ≤ x')
    (havc : c < x ∨ x' < c) (havd : d < x ∨ x' < d) (have' : e < x ∨ x' < e) :
    Clockwise4 m c x d e ↔ Clockwise4 m c x' d e := by
  constructor
  · intro h
    exact cw4_shift.mpr
      ((cw4_move₁ hm hx hx' hd he hc hxx havd have' havc).mp (cw4_shift.mp h))
  · intro h
    exact cw4_shift.mpr
      ((cw4_move₁ hm hx hx' hd he hc hxx havd have' havc).mpr (cw4_shift.mp h))

/-- No label crosses itself. -/
theorem not_gcross_self (σ : Equiv.Perm (Fin n)) (p : Fin n) : ¬ GCross σ p p := by
  unfold GCross Clockwise4
  rintro ⟨h1, -, -, -, -⟩
  rw [step_self] at h1
  exact lt_irrefl 0 h1

/-- A fixed label has no incoming crossing edges: its entry `2q+1` and exit `2q`
are adjacent on the refined circle. -/
theorem not_gcross_fixed_snd {σ : Equiv.Perm (Fin n)} {q : Fin n} (hq : σ q = q)
    (p : Fin n) : ¬ GCross σ p q := by
  have hb1 := (σ⁻¹ p).isLt
  have hb2 := p.isLt
  have hb3 := q.isLt
  have hinv : σ⁻¹ q = q := by
    rw [Equiv.Perm.inv_def]
    exact (Equiv.symm_apply_eq σ).mpr hq.symm
  intro hcw
  unfold GCross at hcw
  rw [hinv] at hcw
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at hcw
  omega

/-- A fixed label has no outgoing crossing edges. -/
theorem not_gcross_fixed_fst {σ : Equiv.Perm (Fin n)} {q : Fin n} (hq : σ q = q)
    (p : Fin n) : ¬ GCross σ q p := by
  have hb1 := (σ⁻¹ p).isLt
  have hb2 := p.isLt
  have hb3 := q.isLt
  have hinv : σ⁻¹ q = q := by
    rw [Equiv.Perm.inv_def]
    exact (Equiv.symm_apply_eq σ).mpr hq.symm
  intro hcw
  unfold GCross at hcw
  rw [hinv] at hcw
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at hcw
  omega

/-- Evaluate `GCross` at known inverse-permutation values. -/
theorem gcross_points {σ : Equiv.Perm (Fin n)} {p q : Fin n} {sp sq : ℕ}
    (hp : ((σ⁻¹ p : Fin n) : ℕ) = sp) (hq : ((σ⁻¹ q : Fin n) : ℕ) = sq) :
    GCross σ p q ↔
      Clockwise4 (2 * n) (2 * sp + 1) (2 * sq + 1) (2 * (p : ℕ)) (2 * (q : ℕ)) := by
  unfold GCross
  rw [hp, hq]

/-- `advD` from integer lifts: if `X, Y` lift `x, y` with `X < Y < X + n`, the
advance is the lift difference. -/
theorem advD_of_lifts {x y : Fin n} {X Y : ℕ}
    (hx : (x : ℕ) = X ∨ (x : ℕ) + n = X) (hy : (y : ℕ) = Y ∨ (y : ℕ) + n = Y)
    (h1 : X < Y) (h2 : Y < X + n) : advD x y = Y - X := by
  have hxlt := x.isLt
  have hylt := y.isLt
  have hlt : Y - X < n := by omega
  unfold advD
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have he : (y : ℕ) + n - (x : ℕ) = (Y - X) + n := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  · have he : (y : ℕ) + n - (x : ℕ) = Y - X := by omega
    rw [he, Nat.mod_eq_of_lt hlt]
  · exact absurd h1 (by omega)
  · have he : (y : ℕ) + n - (x : ℕ) = (Y - X) + n := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

end Conj43
