/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.L5Defs

/-! ### Component reduction (the paper's Lemma 5): definitions

Frozen on 2026-10-26, before any proof. `LooplessBAP n` stores the induced permutation `σ`; strand `x` exits at
`exitPos x = 5x + 1` and enters at `entryPos F x = 5 σ⁻¹(x) + 4` on the ε-resolved circle of modulus `5n`
(`Conj43.Defs`). A component of the crossing graph is a set of strands; erasing the others and relabeling the survivors
by their order gives the paper's `f^(r)`. -/

namespace Conj43

variable {n : ℕ}

/-- Crossing adjacency in either direction: the undirected crossing graph. -/
def crossAdj (F : LooplessBAP n) (p q : Fin n) : Prop :=
  CrossEdge F p q ∨ CrossEdge F q p

instance (F : LooplessBAP n) (p q : Fin n) : Decidable (crossAdj F p q) := by
  unfold crossAdj; infer_instance

/-- The labels reached from `p` in at most `k` crossing steps. -/
def reachAux (F : LooplessBAP n) (p : Fin n) : ℕ → Finset (Fin n)
  | 0 => {p}
  | k + 1 => reachAux F p k ∪ Finset.univ.filter (fun q => ∃ r ∈ reachAux F p k, crossAdj F r q)

/-- The crossing component of `p`: the labels reached in at most `n` steps. -/
def component (F : LooplessBAP n) (p : Fin n) : Finset (Fin n) :=
  reachAux F p n

/-- The increasing enumeration of a set of labels: `labelsOf C j` is its `j`-th least element. -/
def labelsOf (C : Finset (Fin n)) : Fin C.card ↪o Fin n :=
  C.orderEmbOfFin rfl

/-- Erase every strand outside `C` and relabel the survivors by their order. New boundary vertex `i` carries the exit of
surviving strand `i` followed by one entry. The entry of surviving strand `j`, at old vertex `σ⁻¹ (labelsOf C j)`, goes
to the new vertex of the last surviving exit at or before that vertex, cyclically: the index of the greatest element of
`C` that is at most `σ⁻¹ (labelsOf C j)`, or the last index if there is none. -/
def entryMapOn (F : LooplessBAP n) (C : Finset (Fin n)) (j : Fin C.card) : Fin C.card :=
  ⟨((C.filter (· ≤ F.σ⁻¹ (labelsOf C j))).card + C.card - 1) % C.card, Nat.mod_lt _ j.pos⟩

/-- The relabeled entry vertices of the strands of `p`'s component. -/
def restrictEntry (F : LooplessBAP n) (p : Fin n) :
    Fin (component F p).card → Fin (component F p).card :=
  entryMapOn F (component F p)

open Classical in
/-- The paper's `f^(r)` for the component of `p`: the loopless bounded affine permutation whose `σ⁻¹` is
`restrictEntry F p` when that map is a bijection (the frozen `restrictEntry_bijective`), and the identity otherwise. -/
noncomputable def restrictBAP (F : LooplessBAP n) (p : Fin n) : LooplessBAP (component F p).card :=
  if h : Function.Bijective (restrictEntry F p) then ⟨(Equiv.ofBijective _ h).symm⟩ else ⟨1⟩

/-- Angles restricted to the component of `p`, in its relabeled order (the paper's `θ|_{C}`). -/
def restrictAngles (F : LooplessBAP n) (p : Fin n) (θ : Fin n → ℝ) : Fin (component F p).card → ℝ :=
  fun j => θ (labelsOf (component F p) j)

/-- A label least in its component (the paper's representative `p_C = min C`). -/
def IsAnchor (F : LooplessBAP n) (p : Fin n) : Prop :=
  ∀ q, SameComponent F p q → p ≤ q

/-- The gauge slice `S_a` of Appendix A: admissible angles equal to `a` at every anchor. With `a = 0` it is Galashin's
slice. -/
def gaugeSlice (F : LooplessBAP n) (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {θ | Admissible F θ ∧ ∀ p, IsAnchor F p → θ p = a p}

/-- The slice is the set `S` of the frozen analytic statements (`Challenge/Conj43.lean`), written out. -/
example (F : LooplessBAP n) (a : Fin n → ℝ) : gaugeSlice F a =
    {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q →
        0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧
        (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q)
          < Real.pi) ∧
      ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} :=
  rfl

/-! ### Fixtures -/

/-- Two labels exchanged: no crossing, two singleton components, neither fixed by `σ` (the paper's Remark 6). -/
def FSwap : LooplessBAP 2 := ⟨Equiv.swap 0 1⟩

/-- One label, a coloop. -/
def FColoop : LooplessBAP 1 := ⟨1⟩

/-- `σ = (2, 0, 1)`: one component of three labels. -/
def FTop3 : LooplessBAP 3 := ⟨⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩⟩

/-- `σ = (2, 0, 1, 5, 3, 4)`, the paper's Figure 5(a) (`σ̄ = (3,1,2,6,4,5)` in labels from one): two components. -/
def FTwo : LooplessBAP 6 := ⟨⟨![2, 0, 1, 5, 3, 4], ![1, 2, 0, 4, 5, 3], by decide, by decide⟩⟩

end Conj43
