/-
Conj43/NecklaceEmbeddingDefs.lean: definitions for the conditional form of the paper's Corollary 32
(cor:necklace-embedding, "the necklace coordinates determine the critical point").

The positive projective space P^{n-1}_{>0} is modelled as the positive orthant modulo positive rescaling, with the
quotient topology. This is the subspace topology of the real projective space on its positive points.
-/
import Conj43.Defs

namespace Conj43

variable {n : ℕ}

/-- The positive orthant `{v : 0 < v i for every i}`, with the subspace topology of `Fin n → ℝ`. -/
abbrev PosVec (n : ℕ) := {v : Fin n → ℝ // ∀ i, 0 < v i}

/-- Two positive vectors are related when the second is a positive multiple of the first. -/
def posRescale (v w : PosVec n) : Prop := ∃ c : ℝ, 0 < c ∧ w.val = c • v.val

/-- The positive projective space `P^{n-1}_{>0}`: positive vectors up to positive rescaling, with the quotient
topology. -/
abbrev PosProj (n : ℕ) := Quot (@posRescale n)

/-- The projective class `[v_0 : ⋯ : v_{n-1}]` of a positive vector. -/
def posClass (v : PosVec n) : PosProj n := Quot.mk _ v

/-- The fixture of the control `necklace_log_needed`: σ = (2, 0, 1) on three labels (i ↦ i − 1), whose crossing
graph is the directed 3-cycle 0 → 1 → 2 → 0, one component. -/
def fixtureCycle : LooplessBAP 3 := ⟨(finRotate 3).symm⟩

end Conj43
