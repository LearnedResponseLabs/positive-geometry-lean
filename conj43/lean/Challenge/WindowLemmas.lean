/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.WindowLemmasDefs
namespace Conj43
namespace WindowLemmas
variable {n : ℕ}

/-! ### Group `window_lemmas`: Lemma 14 and Lemmas 17-21 of the combinatorial W-P proof -/

/-- **Lemma 14 (lem:winding-simple), first part.** A closed walk of at least two labels whose consecutive labels,
the closing pair included, are distinct has total advance a positive multiple of `n`. -/
theorem walk_advance_multiple (c : List (Fin n)) (hm : 2 ≤ c.length)
    (hc : ∀ e ∈ cycleEdges c, e.1 ≠ e.2) :
    0 < winding c ∧ n ∣ winding c := by
  sorry

/-- **Lemma 14 (lem:winding-simple), second part.** If that total advance equals `n`, the labels are pairwise
distinct. -/
theorem walk_simple_of_advance (c : List (Fin n)) (hm : 2 ≤ c.length)
    (hc : ∀ e ∈ cycleEdges c, e.1 ≠ e.2) (hw : winding c = n) :
    c.Nodup := by
  sorry

/-- **Lemma 17 (lem:wp-active-set).** The residue permutation restricts to a permutation of the active
positions. -/
theorem active_set_restriction (W : DWindow n) :
    Set.BijOn W.σ {i | Active W i} {i | Active W i} := by
  sorry

/-- **Lemma 18 (lem:wp-adjacent-active-ascent), existence.** A window with an active position has an adjacent
active ascent. -/
theorem adjacent_active_ascent (W : DWindow n) (h : ∃ i, Active W i) :
    ∃ a b : Fin n, IsAdjacentAscent W a b := by
  sorry

/-- **Lemma 18 (lem:wp-adjacent-active-ascent), bounds.** For every adjacent active ascent, `b ≤ A < B ≤ a + n`
(eq. (wp-bridge-bounds)), and swapping `A` and `B` gives a decorated bounded window again. -/
theorem adjacent_ascent_bounds (W : DWindow n) {a b : Fin n} (h : IsAdjacentAscent W a b) :
    (b : ℕ) ≤ W.w a ∧ W.w b ≤ (a : ℕ) + n ∧ ∃ g : DWindow n, g.w = swapLift W.w a b := by
  sorry

/-- **Lemma 19 (lem:wp-measure-decrease).** The swap of an adjacent active ascent adds exactly one inversion,
so `μ` drops by one (eq. (wp-measure-drop)). -/
theorem swap_measure_drop (W g : DWindow n) {a b : Fin n} (h : IsAdjacentAscent W a b)
    (hg : g.w = swapLift W.w a b) :
    invLift g.w = invLift W.w + 1 ∧ mu n g.w + 1 = mu n W.w := by
  sorry

/-- **Lemma 20 (lem:wp-local-transition), the case `A = b`.** The swap does not change the edge set
(eq. (wp-transition-identity)). -/
theorem local_transition_identity (W g : DWindow n) {a b : Fin n} (h : IsAdjacentAscent W a b)
    (hg : g.w = swapLift W.w a b) (hA : W.w a = (b : ℕ)) :
    edgeSet W.σ = edgeSet g.σ := by
  sorry

/-- **Lemma 20 (lem:wp-local-transition), the case `A > b`.** With `α = σ a`, `β = σ b` and `S` of
eq. (wp-S-lift): `b < S < a + n`, and according as `S < A`, `A ≤ S < B` or `B ≤ S`, the edge set of `w` is that
of `g` with the left subdivision, the triangle, or the right subdivision (eqs. (wp-transition-left),
(wp-transition-triangle), (wp-transition-right)); every added edge is absent from `E(g)` and every removed edge
is absent from `E(w)`. The three guards are mutually exclusive. -/
theorem local_transition (W g : DWindow n) {a b : Fin n} (h : IsAdjacentAscent W a b)
    (hg : g.w = swapLift W.w a b) (hA : (b : ℕ) < W.w a) :
    (b : ℕ) < sLift W a b ∧ sLift W a b < (a : ℕ) + n ∧
    ((sLift W a b < W.w a ∧
        edgeSet W.σ = (edgeSet g.σ \ {(W.σ a, b)}) ∪ {(W.σ a, W.σ b), (W.σ b, b)} ∧
        (W.σ a, W.σ b) ∉ edgeSet g.σ ∧ (W.σ b, b) ∉ edgeSet g.σ ∧ (W.σ a, b) ∉ edgeSet W.σ) ∨
     (W.w a ≤ sLift W a b ∧ sLift W a b < W.w b ∧
        edgeSet W.σ = edgeSet g.σ ∪ {(b, W.σ a), (W.σ a, W.σ b), (W.σ b, b)} ∧
        (b, W.σ a) ∉ edgeSet g.σ ∧ (W.σ a, W.σ b) ∉ edgeSet g.σ ∧ (W.σ b, b) ∉ edgeSet g.σ) ∨
     (W.w b ≤ sLift W a b ∧
        edgeSet W.σ = (edgeSet g.σ \ {(b, W.σ b)}) ∪ {(b, W.σ a), (W.σ a, W.σ b)} ∧
        (b, W.σ a) ∉ edgeSet g.σ ∧ (W.σ a, W.σ b) ∉ edgeSet g.σ ∧ (b, W.σ b) ∉ edgeSet W.σ)) := by
  sorry

/-- **Lemma 21 (lem:wp-winding-arithmetic).** When `A > b`, the triangle `b → α → β → b` has total advance `n`
(winding one), and each two-edge replacement has the advance of the edge it replaces. (The paper states each
identity in its own regime of Lemma 20; none uses the regime.) -/
theorem winding_arithmetic (W : DWindow n) {a b : Fin n} (h : IsAdjacentAscent W a b)
    (hA : (b : ℕ) < W.w a) :
    winding [b, W.σ a, W.σ b] = n ∧
    adv (W.σ a) b = adv (W.σ a) (W.σ b) + adv (W.σ b) b ∧
    adv b (W.σ b) = adv b (W.σ a) + adv (W.σ a) (W.σ b) := by
  sorry

/-! ### Controls -/

/-- **Control for Lemma 14.** The second part needs total advance exactly `n`: the walk `0 → 1 → 0 → 1 → 0` in
`Fin 3` has consecutive labels distinct and total advance `2 · 3`, and repeats its labels. -/
theorem control_two_laps :
    winding ([0, 1, 0, 1] : List (Fin 3)) = 2 * 3 ∧
    (∀ e ∈ cycleEdges ([0, 1, 0, 1] : List (Fin 3)), e.1 ≠ e.2) ∧
    ¬ ([0, 1, 0, 1] : List (Fin 3)).Nodup := by
  sorry

/-- **Control for Lemma 19.** Adjacency is needed: in the window `(2, 3, 4, 5)` of `Fin 4` (every position
active), swapping positions `0` and `2`, which have the active position `1` between them, gives a window again
but adds three inversions. -/
theorem control_nonadjacent_swap :
    IsWindowLift (![2, 3, 4, 5] : Fin 4 → ℕ) ∧
    IsWindowLift (swapLift (![2, 3, 4, 5] : Fin 4 → ℕ) 0 2) ∧
    invLift (swapLift (![2, 3, 4, 5] : Fin 4 → ℕ) 0 2) = invLift (![2, 3, 4, 5] : Fin 4 → ℕ) + 3 := by
  sorry

end WindowLemmas
end Conj43
