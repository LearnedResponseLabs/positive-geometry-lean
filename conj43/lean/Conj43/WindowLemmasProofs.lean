/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.WindowLemmasWalk
import Conj43.WindowLemmasInversions
import Conj43.WindowLemmasTransitions

namespace Conj43
namespace WindowLemmas
variable {n : ℕ}

theorem walk_advance_multiple (c : List (Fin n)) (hm : 2 ≤ c.length)
    (hc : ∀ e ∈ cycleEdges c, e.1 ≠ e.2) :
    0 < winding c ∧ n ∣ winding c := by
  constructor
  · cases c with
    | nil => simp at hm
    | cons a t =>
      cases t with
      | nil => simp at hm
      | cons b t =>
        have he : (a,b) ∈ cycleEdges (a :: b :: t) := by
          simp [cycleEdges]
        apply List.sum_pos_iff_exists_pos_nat.mpr
        exact ⟨adv a b, List.mem_map.mpr ⟨(a,b),he,rfl⟩, advance_pos (hc _ he)⟩
  · rw [winding_count_descents]
    exact dvd_mul_right _ _

theorem walk_simple_of_advance (c : List (Fin n)) (hm : 2 ≤ c.length)
    (hc : ∀ e ∈ cycleEdges c, e.1 ≠ e.2) (hw : winding c = n) :
    c.Nodup := by
  have hn : 0 < n := by
    have hpos := (walk_advance_multiple c hm hc).1
    omega
  apply nodup_of_one_descent c hm hc
  have heq := winding_count_descents c
  rw [hw] at heq
  nlinarith

theorem swap_measure_drop (W g : DWindow n) {a b : Fin n} (h : IsAdjacentAscent W a b)
    (hg : g.w = swapLift W.w a b) :
    invLift g.w = invLift W.w + 1 ∧ mu n g.w + 1 = mu n W.w := by
  have hinv : invLift g.w = invLift W.w + 1 := by
    rw [hg]
    exact invLift_swap_add_one W h
  refine ⟨hinv, ?_⟩
  have hbound := invLift_le_choose g.w
  unfold mu
  omega

theorem active_set_restriction (W : DWindow n) :
    Set.BijOn W.σ {i | Active W i} {i | Active W i} := by
  refine ⟨fun i hi => W.toWindow.sigma_active hi, W.σ.injective.injOn, ?_⟩
  intro j hj
  refine ⟨W.σ.symm j, ?_, W.σ.apply_symm_apply j⟩
  intro hfix
  have heq : W.σ.symm j = j := hfix.symm.trans (W.σ.apply_symm_apply j)
  exact hj (by simpa only [heq] using W.σ.apply_symm_apply j)

theorem adjacent_active_ascent (W : DWindow n) (h : ∃ i, Active W i) :
    ∃ a b : Fin n, IsAdjacentAscent W a b := by
  exact W.toWindow.ascent_exists h

theorem adjacent_ascent_bounds (W : DWindow n) {a b : Fin n} (h : IsAdjacentAscent W a b) :
    (b : ℕ) ≤ W.w a ∧ W.w b ≤ (a : ℕ) + n ∧ ∃ g : DWindow n, g.w = swapLift W.w a b := by
  obtain ⟨h1,h2⟩ := ascent_bounds_bridge W h
  have hab : (a : ℕ) < b := h.1
  have h3 : (a : ℕ) ≤ W.w b := le_trans (by omega) (W.hlb b)
  have h4 : W.w a ≤ (b : ℕ) + n := le_trans (W.hub a) (by omega)
  exact ⟨h1,h2,ofWindow (W.toWindow.swapWindow a b h.1 h1 h2 h3 h4),rfl⟩

theorem local_transition_identity (W g : DWindow n) {a b : Fin n} (h : IsAdjacentAscent W a b)
    (hg : g.w = swapLift W.w a b) (hA : W.w a = (b : ℕ)) :
    edgeSet W.σ = edgeSet g.σ := by
  have hb := (ascent_bounds_bridge W h).2
  apply Finset.ext
  intro e
  simpa only [edgeSet_eq_GEdgeSet, swap_sigma W g hg, DWindow.toWindow] using
    Window.master_identity (W := W.toWindow) h.1 h.2.1 h.2.2.1 h.2.2.2.1 hb hA e

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
  have hBan := (ascent_bounds_bridge W h).2
  have hS := sLift_cases W h hA
  have hbS := sLift_bounds W h hA
  have hαb : W.σ a ≠ b := Window.alpha_ne_b (W := W.toWindow) h.2.1 h.1 hA
  have hβb : W.σ b ≠ b := h.2.2.1
  have hαβ : W.σ a ≠ W.σ b := fun he => (ne_of_lt h.1) (W.σ.injective he)
  refine ⟨hbS.1,hbS.2,?_⟩
  simp only [edgeSet_eq_GEdgeSet, swap_sigma W g hg]
  rcases Nat.lt_or_ge (sLift W a b) (W.w a) with hSA | hAS
  · obtain ⟨_,hn1,hn2,hfresh⟩ := Window.master_left (W := W.toWindow)
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hBan hA rfl hS hSA
    refine Or.inl ⟨hSA,?_,hn1,hn2,?_⟩
    · apply Finset.ext
      intro e
      simpa only [DWindow.toWindow, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton,
        Finset.mem_insert] using hfresh e
    · intro he
      rcases (hfresh _).mp he with ⟨_,hne⟩ | he | he
      · exact hne rfl
      · exact hβb (congrArg Prod.snd he).symm
      · exact hαβ (congrArg Prod.fst he)
  · rcases Nat.lt_or_ge (sLift W a b) (W.w b) with hSB | hBS
    · obtain ⟨hn1,hn2,hn3,hfresh⟩ := Window.master_triangle (W := W.toWindow)
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hBan hA rfl hS hAS hSB
      refine Or.inr (Or.inl ⟨hAS,hSB,?_,hn1,hn2,hn3⟩)
      apply Finset.ext
      intro e
      simpa only [DWindow.toWindow, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] using hfresh e
    · obtain ⟨_,hn1,hn2,hfresh⟩ := Window.master_right (W := W.toWindow)
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hBan hA rfl hS hBS
      refine Or.inr (Or.inr ⟨hBS,?_,hn1,hn2,?_⟩)
      · apply Finset.ext
        intro e
        simpa only [DWindow.toWindow, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton,
          Finset.mem_insert] using hfresh e
      · intro he
        rcases (hfresh _).mp he with ⟨_,hne⟩ | he | he
        · exact hne rfl
        · exact hαβ (congrArg Prod.snd he).symm
        · exact hαb (congrArg Prod.fst he).symm

theorem winding_arithmetic (W : DWindow n) {a b : Fin n} (h : IsAdjacentAscent W a b)
    (hA : (b : ℕ) < W.w a) :
    winding [b, W.σ a, W.σ b] = n ∧
    adv (W.σ a) b = adv (W.σ a) (W.σ b) + adv (W.σ b) b ∧
    adv b (W.σ b) = adv b (W.σ a) + adv (W.σ a) (W.σ b) := by
  have hαd := lift_decomp W.toWindow a
  have hβd := lift_decomp W.toWindow b
  have hA1 := W.toWindow.active_strict h.2.1
  have hB1 := W.toWindow.active_strict h.2.2.1
  have habn : (a : ℕ) < (b : ℕ) := h.1
  have hasc := h.2.2.2.2
  have hBan := (ascent_bounds_bridge W h).2
  have hadv_bα : adv b (W.σ a) = W.w a - (b : ℕ) :=
    advD_of_lifts (Or.inl rfl) hαd hA (by omega)
  have hadv_αβ : adv (W.σ a) (W.σ b) = W.w b - W.w a :=
    advD_of_lifts hαd hβd hasc (by omega)
  have hadv_βb : adv (W.σ b) b = (b : ℕ) + n - W.w b :=
    advD_of_lifts hβd (Or.inr rfl) hB1.2 (by omega)
  have hadv_αb : adv (W.σ a) b = (b : ℕ) + n - W.w a :=
    advD_of_lifts hαd (Or.inr rfl) (by omega) (by omega)
  have hadv_bβ : adv b (W.σ b) = W.w b - (b : ℕ) :=
    advD_of_lifts (Or.inl rfl) hβd hB1.1 (by omega)
  refine ⟨?_,?_,?_⟩
  · change adv b (W.σ a) + (adv (W.σ a) (W.σ b) + (adv (W.σ b) b + 0)) = n
    rw [hadv_bα, hadv_αβ, hadv_βb]
    omega
  · rw [hadv_αb, hadv_αβ, hadv_βb]
    omega
  · rw [hadv_bβ, hadv_bα, hadv_αβ]
    omega

theorem control_two_laps :
    winding ([0, 1, 0, 1] : List (Fin 3)) = 2 * 3 ∧
    (∀ e ∈ cycleEdges ([0, 1, 0, 1] : List (Fin 3)), e.1 ≠ e.2) ∧
    ¬ ([0, 1, 0, 1] : List (Fin 3)).Nodup := by
  decide

theorem control_nonadjacent_swap :
    IsWindowLift (![2, 3, 4, 5] : Fin 4 → ℕ) ∧
    IsWindowLift (swapLift (![2, 3, 4, 5] : Fin 4 → ℕ) 0 2) ∧
    invLift (swapLift (![2, 3, 4, 5] : Fin 4 → ℕ) 0 2) = invLift (![2, 3, 4, 5] : Fin 4 → ℕ) + 3 := by
  decide

end WindowLemmas
end Conj43
