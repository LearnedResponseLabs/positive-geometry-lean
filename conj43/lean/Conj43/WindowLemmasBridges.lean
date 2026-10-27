/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.WindowLemmasDefs
import Conj43.WindowAscent

/-! Field-preserving bridges to the existing L3B window library (Apache-2.0). -/
namespace Conj43.WindowLemmas
variable {n : ℕ}

def DWindow.toWindow (W : DWindow n) : Conj43.Window n :=
  ⟨W.σ, W.w, W.hres, W.hlb, W.hub⟩

def ofWindow (W : Conj43.Window n) : DWindow n :=
  ⟨W.σ, W.w, W.hres, W.hlb, W.hub⟩

theorem ascent_bounds_bridge (W : DWindow n) {a b : Fin n}
    (h : IsAdjacentAscent W a b) :
    (b : ℕ) ≤ W.w a ∧ W.w b ≤ (a : ℕ) + n :=
  W.toWindow.ascent_bounds h.1 h.2.1 h.2.2.1 h.2.2.2.1

theorem swap_sigma (W g : DWindow n) {a b : Fin n}
    (hg : g.w = swapLift W.w a b) : g.σ = W.σ * Equiv.swap a b := by
  ext i
  rw [← g.hres i, hg]
  by_cases hia : i = a
  · subst i
    simp [swapLift, Equiv.Perm.mul_apply, W.hres]
  · by_cases hib : i = b
    · subst i
      simp [swapLift, hia, Equiv.Perm.mul_apply, W.hres]
    · simp [swapLift, hia, hib, Equiv.Perm.mul_apply, W.hres,
        Equiv.swap_apply_of_ne_of_ne hia hib]

theorem middle_lift_outside (W : DWindow n) {a b r : Fin n}
    (h : IsAdjacentAscent W a b) (har : a < r) (hrb : r < b) :
    W.w r < W.w a ∨ W.w b < W.w r := by
  have bounds := ascent_bounds_bridge W h
  have hr := W.toWindow.fixed_decoration (h.2.2.2.1 r har hrb)
  change W.w r = (r : ℕ) ∨ W.w r = (r : ℕ) + n at hr
  have har' : (a : ℕ) < r := har
  have hrb' : (r : ℕ) < b := hrb
  omega

end Conj43.WindowLemmas
