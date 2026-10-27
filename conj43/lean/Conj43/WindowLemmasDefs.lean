/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.Defs

/-!
# The window induction of the combinatorial W-P proof: definitions as the paper states them

The paper proves Proposition 15 (the winding-one partition) by a finite induction on decorated bounded windows
(subsection "A combinatorial proof of partition existence"). These definitions transcribe that subsection's
objects for its Lemmas 17-21, and Lemma 14 uses the pinned `adv`, `cycleEdges` and `winding` of `Conj43.Defs`.
Labels are `Fin n`, as in the paper's `ℤ_n = {0, …, n-1}`.
-/

namespace Conj43
namespace WindowLemmas

variable {n : ℕ}

/-- A decorated bounded window (paper, before Lemma 17): a lift `w` whose residues `w i % n` form the permutation
`σ`, with `i ≤ w i ≤ i + n`. -/
structure DWindow (n : ℕ) where
  σ : Equiv.Perm (Fin n)
  w : Fin n → ℕ
  hres : ∀ i : Fin n, w i % n = (σ i : ℕ)
  hlb : ∀ i : Fin n, (i : ℕ) ≤ w i
  hub : ∀ i : Fin n, w i ≤ (i : ℕ) + n

/-- A position is active when its residue differs from it, and fixed otherwise. -/
def Active (W : DWindow n) (i : Fin n) : Prop := W.σ i ≠ i

instance (W : DWindow n) (i : Fin n) : Decidable (Active W i) := by
  unfold Active; infer_instance

/-- The directed edge set `E(σ)` of eq. (wp-directed-crossing): for distinct `p, q`, `p → q` when
`s(p)⁺, s(q)⁺, p⁻, q⁻` occur in clockwise cyclic order, with `s = σ⁻¹`, on the refined circle of `2n` points
where `r⁻` sits at `2r` and `r⁺` at `2r + 1` (eq. (wp-kappa)). For a window `W`, `E(w)` is `edgeSet W.σ`. -/
def edgeSet (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => e.1 ≠ e.2 ∧
    Clockwise4 (2 * n) (2 * (σ⁻¹ e.1 : ℕ) + 1) (2 * (σ⁻¹ e.2 : ℕ) + 1) (2 * (e.1 : ℕ)) (2 * (e.2 : ℕ))

/-- `inv(w)` of eq. (wp-measure): the pairs `i < j` with `w i > w j`. -/
def invLift (w : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1).card

/-- `μ(w) = C(n, 2) - inv(w)` of eq. (wp-measure). -/
def mu (n : ℕ) (w : Fin n → ℕ) : ℕ := n.choose 2 - invLift w

/-- The tuple with the values at positions `a` and `b` exchanged. -/
def swapLift (w : Fin n → ℕ) (a b : Fin n) : Fin n → ℕ :=
  fun i => if i = a then w b else if i = b then w a else w i

/-- The pair `a < b` of Lemma 18: adjacent in the increasing list of active positions (both active, every position
strictly between them fixed), with `A = w a < B = w b`. -/
def IsAdjacentAscent (W : DWindow n) (a b : Fin n) : Prop :=
  a < b ∧ Active W a ∧ Active W b ∧ (∀ r : Fin n, a < r → r < b → ¬ Active W r) ∧ W.w a < W.w b

/-- The lift `S` of eq. (wp-S-lift): with `c = s_w(b) = σ⁻¹ b`, `S = c + n` if `c < a` and `S = c` otherwise
(Lemma 20 shows `c > b` in that case). -/
def sLift (W : DWindow n) (a b : Fin n) : ℕ :=
  if ((W.σ⁻¹ b : Fin n) : ℕ) < (a : ℕ) then ((W.σ⁻¹ b : Fin n) : ℕ) + n else ((W.σ⁻¹ b : Fin n) : ℕ)

/-- A tuple is the lift of a decorated bounded window: distinct residues (so they form a permutation of `Fin n`)
and `i ≤ w i ≤ i + n`. Used only by the control `control_nonadjacent_swap`. -/
def IsWindowLift (w : Fin n → ℕ) : Prop :=
  (∀ i j : Fin n, w i % n = w j % n → i = j) ∧ ∀ i : Fin n, (i : ℕ) ≤ w i ∧ w i ≤ (i : ℕ) + n

instance (w : Fin n → ℕ) : Decidable (IsWindowLift w) := by
  unfold IsWindowLift; infer_instance

end WindowLemmas
end Conj43
