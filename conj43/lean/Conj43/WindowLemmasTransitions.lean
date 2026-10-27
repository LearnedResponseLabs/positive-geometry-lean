/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.WindowLemmasBridges
import Conj43.SeedTableMaster

/-!
Bridges to the four existing transition masters. The inverse-position argument
is ported from `Conj43/WindowSwap.lean`, `edge_transition` (Apache-2.0), keeping
the refined endpoint order and the lifted inverse position exactly.
-/
namespace Conj43.WindowLemmas
variable {n : ℕ}

theorem edgeSet_eq_GEdgeSet (σ : Equiv.Perm (Fin n)) : edgeSet σ = GEdgeSet σ := by
  apply Finset.ext
  intro e
  simp only [edgeSet, Finset.mem_filter, Finset.mem_univ, true_and, mem_GEdgeSet]
  change (e.1 ≠ e.2 ∧ GCross σ e.1 e.2) ↔ GCross σ e.1 e.2
  constructor
  · exact And.right
  · intro he
    refine ⟨?_,he⟩
    intro heq
    exact not_gcross_self σ e.2 (heq ▸ he)

theorem sLift_cases (W : DWindow n) {a b : Fin n}
    (h : IsAdjacentAscent W a b) (hA : (b : ℕ) < W.w a) :
    (((W.σ⁻¹ b : Fin n) : ℕ) < (a : ℕ) ∧
      sLift W a b = ((W.σ⁻¹ b : Fin n) : ℕ) + n) ∨
    ((b : ℕ) < ((W.σ⁻¹ b : Fin n) : ℕ) ∧
      sLift W a b = ((W.σ⁻¹ b : Fin n) : ℕ)) := by
  let c : Fin n := W.σ⁻¹ b
  have hc : W.σ c = b := perm_apply_inv' W.σ b
  have hαb : W.σ a ≠ b := Window.alpha_ne_b (W := W.toWindow) h.2.1 h.1 hA
  have hca : c ≠ a := fun he => hαb (he ▸ hc)
  have hcb : c ≠ b := fun he => h.2.2.1 (he ▸ hc)
  have hcact : W.toWindow.Active c := Window.inv_active (W := W.toWindow) h.2.2.1
  have hpos := Window.pos_avoid (W := W.toWindow) h.2.2.2.1 hcact hcb
  have hcane : (c : ℕ) ≠ (a : ℕ) := fun he => hca (Fin.ext he)
  by_cases hlt : (c : ℕ) < (a : ℕ)
  · exact Or.inl ⟨hlt, if_pos hlt⟩
  · exact Or.inr ⟨by change (b : ℕ) < (c : ℕ); omega, if_neg hlt⟩

theorem sLift_bounds (W : DWindow n) {a b : Fin n}
    (h : IsAdjacentAscent W a b) (hA : (b : ℕ) < W.w a) :
    (b : ℕ) < sLift W a b ∧ sLift W a b < (a : ℕ) + n := by
  have hc := (W.σ⁻¹ b).isLt
  have hb := b.isLt
  rcases sLift_cases W h hA with ⟨hcpos,hS⟩ | ⟨hcpos,hS⟩ <;> omega

end Conj43.WindowLemmas
