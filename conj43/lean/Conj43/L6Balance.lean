import Conj43.L6Calculus

/-! Degree balance and invariance under component shifts. -/
namespace Conj43
variable {n : ℕ}

/-- A closed cycle has zero incidence at every label. -/
private theorem cycle_balance (c : List (Fin n)) (r : Fin n) :
    ((cycleEdges c).map fun e =>
      (if r = e.2 then (1 : ℝ) else 0) - (if r = e.1 then 1 else 0)).sum = 0 := by
  classical
  exact cycle_difference_sum c (fun p => if r = p then 1 else 0)

/-- Degree balance derived from the winding-one cycle partition. -/
theorem degree_balance_core (F : LooplessBAP n) : (realB F).mulVec (fun _ => 1) = 0 := by
  classical
  ext r
  change (∑ j : EdgeIdx F, realB F r j * 1) = 0
  simp only [mul_one]
  have hb (j : EdgeIdx F) : realB F r j =
      (if r = (edgeOf F j).2 then (1 : ℝ) else 0) -
        (if r = (edgeOf F j).1 then 1 else 0) := by
    simp [realB, Bmat]
  simp_rw [hb]
  unfold edgeOf
  rw [l5_sum_get (crossEdges F) (fun e => (if r = e.2 then (1 : ℝ) else 0) - (if r = e.1 then 1 else 0))]
  obtain ⟨cs, _, hp⟩ := winding_one_partition n F
  rw [← (hp.map (fun e => (if r = e.2 then (1 : ℝ) else 0) -
    (if r = e.1 then 1 else 0))).sum_eq, l5_sum_flatMap]
  exact List.sum_eq_zero (by intro x hx; obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; exact cycle_balance c r)

/-- Every component-constant displacement preserves the lifted edge angles. -/
theorem delta_shift_core (F : LooplessBAP n) (θ s : Fin n → ℝ)
    (hs : ∀ p q, SameComponent F p q → s p = s q)
    (p q : Fin n) (he : CrossEdge F p q) : delta (θ + s) (p, q) = delta θ (p, q) := by
  have h := hs p q (Relation.ReflTransGen.single (Or.inl he))
  simp only [delta, Pi.add_apply]
  rw [h]
  ring

/-- The gradient is invariant under arbitrary component shifts. -/
theorem gradient_shift_core (F : LooplessBAP n) (θ s : Fin n → ℝ)
    (hs : ∀ p q, SameComponent F p q → s p = s q) :
    gradientMap F (θ + s) = gradientMap F θ := by
  unfold gradientMap
  congr 1
  funext j
  congr 2
  exact delta_shift_core F θ s hs _ _ ((l5_mem_crossEdges F _ _).mp (List.get_mem _ j))

/-- Degree balance removes every constant from the edge logarithms. -/
theorem gradient_constant_core (F : LooplessBAP n) (θ : Fin n → ℝ) (c : ℝ) :
    (realB F).mulVec (fun j => Real.log (Real.sin (delta θ (edgeOf F j))) + c) =
      gradientMap F θ := by
  have hc : (realB F).mulVec (fun _ => c) = 0 := by
    calc
      _ = (realB F).mulVec (c • (fun _ => (1 : ℝ))) := by congr 1; ext j; exact (mul_one c).symm
      _ = c • ((realB F).mulVec (fun _ => 1)) := Matrix.mulVec_smul _ _ _
      _ = 0 := by rw [degree_balance_core, smul_zero]
  change (realB F).mulVec ((fun j => Real.log (Real.sin (delta θ (edgeOf F j)))) + (fun _ => c)) = _
  rw [Matrix.mulVec_add, hc, add_zero]
  rfl

end Conj43
