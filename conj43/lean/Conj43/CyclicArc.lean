/-
Conj43/CyclicArc.lean — L2 arithmetic layer: the half-open cyclic-arc lemmas
(paper eq:L1–L3) in the pinned ε-resolved position encoding of Conj43/Defs.lean.

Bespoke integer arithmetic over the pinned `step` (Mathlib's cyclic-order library
is thin; this fallback is pre-approved). Strategy: `step_spec` pins each `step`
atom to a linear form, `cw4_iff_linear` canonicalizes `Clockwise4` into the 4-way
disjunction of linear orders (the paper's "cut the circle to a line"), and `omega`
closes every branch. All lemma statements were brute-force verified externally
over n ≤ 7 including all label coincidences before formalization.
-/
import Conj43.Defs

namespace Conj43

/-! ### `step` toolkit -/

/-- For points `a b < m`, `step m a b` is `b - a` (if `a ≤ b`) else `b + m - a`.
This eliminates the variable-modulus `%`, which `omega` cannot handle. -/
theorem step_spec {m a b : ℕ} (hm : 0 < m) (ha : a < m) (hb : b < m) :
    (a ≤ b ∧ step m a b = b - a) ∨ (b < a ∧ step m a b = b + m - a) := by
  rcases Nat.lt_or_ge b a with h | h
  · refine Or.inr ⟨h, ?_⟩
    unfold step
    exact Nat.mod_eq_of_lt (by omega)
  · refine Or.inl ⟨h, ?_⟩
    unfold step
    have hrw : b + m - a = m + (b - a) := by omega
    rw [hrw, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)

theorem step_self (m a : ℕ) : step m a a = 0 := by
  unfold step
  have hrw : a + m - a = m := by omega
  rw [hrw, Nat.mod_self]

/-- Cutting the circle to a line: `Clockwise4` on points `< m` is exactly one of
the four linear rotations of `a < b < c < d`. -/
theorem cw4_iff_linear {m a b c d : ℕ} (hm : 0 < m)
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m) :
    Clockwise4 m a b c d ↔
      ((a < b ∧ b < c ∧ c < d) ∨ (d < a ∧ a < b ∧ b < c) ∨
        (c < d ∧ d < a ∧ a < b) ∨ (b < c ∧ c < d ∧ d < a)) := by
  unfold Clockwise4
  rcases step_spec hm ha hb with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases step_spec hm hb hc with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
      rcases step_spec hm hc hd with ⟨h3, e3⟩ | ⟨h3, e3⟩ <;>
        rcases step_spec hm hd ha with ⟨h4, e4⟩ | ⟨h4, e4⟩ <;>
          omega

/-- `negPos` is genuine reflection on nonzero points below the modulus. -/
theorem negPos_eq {m v : ℕ} (h0 : 0 < v) (hv : v < m) : negPos m v = m - v := by
  unfold negPos
  exact Nat.mod_eq_of_lt (by omega)

/-! ### Half-open cyclic arcs on the row circle ℤ/n -/

/-- `r ∈ (s, x]` cyclically on ℤ/n, 0-based, in the STRICT regime `s ≠ x`
(the predicate is empty when `s = x`). House style: `step`-arithmetic. -/
def inArcN (n s x r : ℕ) : Prop :=
  0 < step n s r ∧ step n s r ≤ step n s x

instance (n s x r : ℕ) : Decidable (inArcN n s x r) := by
  unfold inArcN; infer_instance

theorem inArcN_not_start {n s x : ℕ} : ¬ inArcN n s x s := by
  intro h
  obtain ⟨h1, -⟩ := h
  rw [step_self] at h1
  exact Nat.lt_irrefl 0 h1

theorem inArcN_end {n s x : ℕ} (hs : s < n) (hx : x < n) (hsx : s ≠ x) :
    inArcN n s x x := by
  have hn : 0 < n := by omega
  unfold inArcN
  rcases step_spec hn hs hx with ⟨h, e⟩ | ⟨h, e⟩ <;> omega

/-- Successor step around the arc: entering at `s`, leaving after `x`. -/
theorem inArcN_succ {n s x j : ℕ} (hs : s < n) (hx : x < n) (hj : j < n)
    (hsx : s ≠ x) :
    inArcN n s x ((j + 1) % n) ↔ (j = s ∨ (inArcN n s x j ∧ j ≠ x)) := by
  have hn : 0 < n := by omega
  unfold inArcN
  rcases Nat.lt_or_ge (j + 1) n with hj1 | hj1
  · rw [Nat.mod_eq_of_lt hj1]
    rcases step_spec hn hs hj1 with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
      rcases step_spec hn hs hj with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
        rcases step_spec hn hs hx with ⟨h3, e3⟩ | ⟨h3, e3⟩ <;>
          omega
  · have hjn : j + 1 = n := by omega
    rw [hjn, Nat.mod_self]
    rcases step_spec hn hs hn with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
      rcases step_spec hn hs hj with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
        rcases step_spec hn hs hx with ⟨h3, e3⟩ | ⟨h3, e3⟩ <;>
          omega

/-- **The boundary of a half-open arc:** one step around the circle, the indicator of `(s, x]` falls by one at the
end `x` and rises by one at the start `s`, `1[j ∈ (s,x]] − 1[j+1 ∈ (s,x]] = 1[j = x] − 1[j = s]`; that is,
∂(s, x] = [x] − [s]. This is the step of prop:rowdiff "Dm = e_{s_q} − e_{s_p}". -/
theorem inArcN_indicator_diff {n s x j : ℕ} (hs : s < n) (hx : x < n) (hj : j < n)
    (hsx : s ≠ x) :
    (if inArcN n s x j then (1 : ℤ) else 0) - (if inArcN n s x ((j + 1) % n) then 1 else 0)
      = (if j = x then 1 else 0) - (if j = s then 1 else 0) := by
  have hsucc := inArcN_succ hs hx hj hsx
  by_cases h1 : j = s
  · -- the start: outside the arc, and the next position is inside
    have hjx : j ≠ x := by rw [h1]; exact hsx
    have hn : ¬ inArcN n s x j := by rw [h1]; exact inArcN_not_start
    rw [if_neg hn, if_pos (hsucc.mpr (Or.inl h1)), if_neg hjx, if_pos h1]
  · by_cases h2 : j = x
    · -- the end: inside the arc, and the next position is outside
      have ha : inArcN n s x j := by rw [h2]; exact inArcN_end hs hx hsx
      have hnb : ¬ inArcN n s x ((j + 1) % n) := by
        intro hb
        rcases hsucc.mp hb with hc | ⟨-, hc⟩
        · exact h1 hc
        · exact hc h2
      rw [if_pos ha, if_neg hnb, if_pos h2, if_neg h1]
    · -- elsewhere: one step does not cross an end, so the indicator does not change
      have hiff : inArcN n s x ((j + 1) % n) ↔ inArcN n s x j := by
        rw [hsucc]
        constructor
        · rintro (hc | ⟨ha, -⟩)
          · exact absurd hc h1
          · exact ha
        · intro ha
          exact Or.inr ⟨ha, h2⟩
      rw [if_neg h1, if_neg h2]
      by_cases ha : inArcN n s x j
      · rw [if_pos ha, if_pos (hiff.mpr ha)]
        norm_num
      · rw [if_neg ha, if_neg (fun hb => ha (hiff.mp hb))]

/-! ### The coloop-tolerant arc (L4)

For a coloop `x` the paired lift obeys `x' - s = n` rather than `x' - s < n`
(paper, proof of prop:rowdiff: "The inequality x'-s ≤ n is strict exactly when x
is not a coloop; for a coloop one has x'-s = n, and A_x is then the whole row
set"). `inArcC` is the arc `(s, x]` read with that convention: the full circle
when `s = x`, and `inArcN` otherwise. -/

/-- The arc `(s, x]` on ℤ/n with the coloop convention: `s = x` means a full
turn (every row), not the empty arc. -/
def inArcC (n s x r : ℕ) : Prop := s = x ∨ inArcN n s x r

instance (n s x r : ℕ) : Decidable (inArcC n s x r) := by
  unfold inArcC; infer_instance

/-- Off the coloop locus `inArcC` is the strict arc. -/
theorem inArcC_of_ne {n s x r : ℕ} (h : s ≠ x) : inArcC n s x r ↔ inArcN n s x r := by
  unfold inArcC
  exact ⟨fun hc => hc.resolve_left h, Or.inr⟩

/-- A coloop lies in every row (paper: `A_x` is the whole row set). -/
theorem inArcC_of_coloop {n s x r : ℕ} (h : s = x) : inArcC n s x r := Or.inl h

/-- Successor step for the coloop-tolerant arc. Unlike `inArcN_succ` this needs
NO `s ≠ x` side condition: on the coloop locus both sides are `True`. -/
theorem inArcC_succ {n s x j : ℕ} (hs : s < n) (hx : x < n) (hj : j < n) :
    inArcC n s x ((j + 1) % n) ↔ (j = s ∨ (inArcC n s x j ∧ j ≠ x)) := by
  by_cases hsx : s = x
  · constructor
    · intro _
      by_cases hjs : j = s
      · exact Or.inl hjs
      · exact Or.inr ⟨Or.inl hsx, fun hjx => hjs (hjx.trans hsx.symm)⟩
    · intro _
      exact Or.inl hsx
  · rw [inArcC_of_ne (r := (j + 1) % n) hsx, inArcC_of_ne (r := j) hsx]
    exact inArcN_succ hs hx hj hsx

/-! ### The half-open cyclic-arc lemmas (paper eq:L1, eq:L2, eq:L3)

Stated in the pinned position encoding: on ℤ/5n, the entry endpoint of the arc
`(s, x]` sits at `5s + 4` and the exit endpoint at `5x + 1` (Defs.lean). Side
conditions `sp ≠ p`, `sq ≠ q` come, at every use site, from the fact that the
four endpoints form a directed crossing and a coloop carries no crossing
(`Conj43.not_crossEdge_of_coloop`). -/

/-- **(L1).** Endpoints `sp⁺, p⁻, sq⁺, q⁻` in clockwise resolved order ⟹ the
arcs `(sp, p]` and `(sq, q]` are disjoint. (MisUD configuration.) -/
theorem arc_L1 {n sp p sq q : ℕ} (hsp : sp < n) (hp : p < n) (hsq : sq < n)
    (hq : q < n) (hspp : sp ≠ p) (hsqq : sq ≠ q)
    (hcw : Clockwise4 (5 * n) (5 * sp + 4) (5 * p + 1) (5 * sq + 4) (5 * q + 1)) :
    ∀ r < n, ¬ (inArcN n sp p r ∧ inArcN n sq q r) := by
  intro r hr
  have hn : 0 < n := by omega
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at hcw
  unfold inArcN
  rcases step_spec hn hsp hr with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases step_spec hn hsp hp with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
      rcases step_spec hn hsq hr with ⟨h3, e3⟩ | ⟨h3, e3⟩ <;>
        rcases step_spec hn hsq hq with ⟨h4, e4⟩ | ⟨h4, e4⟩ <;>
          omega

/-- **(L2).** The same four endpoints counterclockwise (pinned as: reflected
positions clockwise) ⟹ the arcs `(sp, p]` and `(sq, q]` cover the circle.
(MisDU configuration.) -/
theorem arc_L2 {n sp p sq q : ℕ} (hsp : sp < n) (hp : p < n) (hsq : sq < n)
    (hq : q < n) (hspp : sp ≠ p) (hsqq : sq ≠ q)
    (hcw : Clockwise4 (5 * n) (negPos (5 * n) (5 * sp + 4))
      (negPos (5 * n) (5 * p + 1)) (negPos (5 * n) (5 * sq + 4))
      (negPos (5 * n) (5 * q + 1))) :
    ∀ r < n, inArcN n sp p r ∨ inArcN n sq q r := by
  intro r hr
  have hn : 0 < n := by omega
  rw [negPos_eq (by omega) (by omega), negPos_eq (by omega) (by omega),
    negPos_eq (by omega) (by omega), negPos_eq (by omega) (by omega)] at hcw
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at hcw
  unfold inArcN
  rcases step_spec hn hsp hr with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases step_spec hn hsp hp with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
      rcases step_spec hn hsq hr with ⟨h3, e3⟩ | ⟨h3, e3⟩ <;>
        rcases step_spec hn hsq hq with ⟨h4, e4⟩ | ⟨h4, e4⟩ <;>
          omega

/-- **(L3).** Order `sp⁺, sq⁺, p⁻, q⁻` clockwise (the directed-crossing
configuration) ⟹ `(sp, p] \ (sq, q] = (sp, sq]`. -/
theorem arc_L3 {n sp p sq q : ℕ} (hsp : sp < n) (hp : p < n) (hsq : sq < n)
    (hq : q < n) (hspp : sp ≠ p) (hsqq : sq ≠ q)
    (hcw : Clockwise4 (5 * n) (5 * sp + 4) (5 * sq + 4) (5 * p + 1) (5 * q + 1)) :
    ∀ r < n, ((inArcN n sp p r ∧ ¬ inArcN n sq q r) ↔ inArcN n sp sq r) := by
  intro r hr
  have hn : 0 < n := by omega
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)] at hcw
  unfold inArcN
  rcases step_spec hn hsp hr with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases step_spec hn hsp hp with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
      rcases step_spec hn hsq hr with ⟨h3, e3⟩ | ⟨h3, e3⟩ <;>
        rcases step_spec hn hsq hq with ⟨h4, e4⟩ | ⟨h4, e4⟩ <;>
          rcases step_spec hn hsp hsq with ⟨h5, e5⟩ | ⟨h5, e5⟩ <;>
            omega

end Conj43
