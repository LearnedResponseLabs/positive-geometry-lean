import Conj43.Defs

/-! Definitions for the lifted angles, assembled form, and complex hinge. -/
namespace Conj43

variable {n : ℕ}

/-- Lift the head forward by one half-turn precisely on wrapped edges. -/
noncomputable def delta (θ : Fin n → ℝ) (e : Fin n × Fin n) : ℝ :=
  θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)

/-- The open admissible chamber, including cells with isolated coloops. -/
def Admissible (F : LooplessBAP n) (θ : Fin n → ℝ) : Prop :=
  ∀ p q, CrossEdge F p q → 0 < delta θ (p, q) ∧ delta θ (p, q) < Real.pi

/-- The quadratic form of the assembled Hessian. -/
noncomputable def hessianQ (F : LooplessBAP n) (θ h : Fin n → ℝ) : ℝ :=
  ((crossEdges F).map fun e => Real.cot (delta θ e) * (h e.2 - h e.1) ^ 2).sum

/-- Two vertices are in the same component if joined by a finite undirected
crossing path; the reflexive closure includes isolated vertices. -/
def SameComponent (F : LooplessBAP n) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p)

/-- Real incidence matrix, obtained by casting the existing integer matrix. -/
noncomputable def realB (F : LooplessBAP n) : Matrix (Fin n) (EdgeIdx F) ℝ :=
  fun r j => (Bmat F r j : ℝ)

/-- The assembled matrix B diag(cot delta) B transpose. -/
noncomputable def hessianMatrix (F : LooplessBAP n) (θ : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  realB F * Matrix.diagonal (fun j => Real.cot (delta θ (edgeOf F j))) * (realB F).transpose

/-- The paper's complex specialization. -/
noncomputable def angleParameter (θ : Fin n → ℝ) (j : Fin n) : ℂ :=
  Complex.exp (Complex.I * (θ j : ℂ))

/-- The bracket, with complex division. -/
noncomputable def bracket (x y : ℂ) : ℂ := x / y - y / x

/-- Symmetric bracket convention: put the greater label first. -/
noncomputable def bracketPlus (t : Fin n → ℂ) (p q : Fin n) : ℂ :=
  if p < q then bracket (t q) (t p) else bracket (t p) (t q)

end Conj43
