import Conj43.L6Conditional

/-! Layer 6 frozen calculus and composition statements. -/
namespace Conj43
variable {n : ℕ}

theorem logSinPrimitive_derivative (u : ℝ) (hu : 0 < u) (huπ : u < Real.pi) :
    HasDerivAt (fun u => ∫ t in (Real.pi / 2)..u, Real.log (Real.sin t)) (Real.log (Real.sin u)) u ∧
    HasStrictDerivAt (fun u => ∫ t in (Real.pi / 2)..u, Real.log (Real.sin t)) (Real.log (Real.sin u)) u := by
  exact ⟨(primitive_strict_core u hu huπ).hasDerivAt, primitive_strict_core u hu huπ⟩

theorem admissible_isOpen (F : LooplessBAP n) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    IsOpen {θ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi)} := by
  exact admissible_open_core F

theorem potential_gradient (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    HasFDerivAt Ψ (∑ r, G θ r • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) r)) θ ∧ HasStrictFDerivAt Ψ (∑ r, G θ r • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) r)) θ := by
  exact ⟨(potential_strict_core F θ hθ).hasFDerivAt, potential_strict_core F θ hθ⟩

theorem gradient_hessian (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let H := (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))) * Matrix.diagonal (fun j => Real.cot (δ θ (edgeOf F j))) * (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).transpose
    HasFDerivAt G (ContinuousLinearMap.pi (fun r => ∑ s, H r s • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) s))) θ ∧ HasStrictFDerivAt G (ContinuousLinearMap.pi (fun r => ∑ s, H r s • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) s))) θ ∧
      ∀ h, dotProduct h (H.mulVec h) = ((crossEdges F).map fun e => Real.cot (δ θ e) * (h e.2 - h e.1)^2).sum := by
  exact ⟨(gradient_strict_core F θ hθ).hasFDerivAt, gradient_strict_core F θ hθ, hessian_matrix_form_core F θ⟩

theorem incidence_degree_balance (F : LooplessBAP n) :
    (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun _ => 1) = 0 := by
  exact degree_balance_core F

theorem gradient_component_shifts (F : LooplessBAP n) (θ s : Fin n → ℝ)
    (hs : ∀ p q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → s p = s q) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    G (θ + s) = G θ := by
  exact gradient_shift_core F θ s hs

theorem gradient_edge_constant (F : LooplessBAP n) (θ : Fin n → ℝ) (c : ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j))) + c) = G θ := by
  exact gradient_constant_core F θ c

theorem hessian_gauge_positive (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) (h : Fin n → ℝ)
    (hh : ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → h p = 0) (hne : h ≠ 0) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    0 < ((crossEdges F).map fun e => Real.cot (δ θ e) * (h e.2 - h e.1)^2).sum := by
  exact tangent_positive_core F θ hθ h hh hne

theorem potential_slice_strictConvex (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    StrictConvexOn ℝ S Ψ := by
  exact potential_strictConvex_core F a

theorem gradient_slice_strictMonotone (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 0 < dotProduct (G y - G x) (y-x) := by
  dsimp only
  intro x hx y hy hne
  exact gradient_monotone_core F a x y hx hy hne

theorem gradient_slice_injective (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    Set.InjOn G S := by
  exact gradient_injective_core F a

/-- The original gradient is a homeomorphism onto its image in the ambient coordinate space.
Openness is proved internally for the gradient with anchor coordinates deleted;
no identification with the incidence range is asserted by this statement. -/
theorem gradient_slice_embedding (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    Topology.IsEmbedding (fun θ : S => G θ.val) := by
  exact gradient_embedding_core F a

theorem potential_variational_inverse (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∀ x ∈ S, ∀ z ∈ S, Ψ x - dotProduct (G x) x ≤ Ψ z - dotProduct (G x) z ∧
      (Ψ z - dotProduct (G x) z = Ψ x - dotProduct (G x) x ↔ z = x) := by
  exact variational_core F a

/-- Conditional end-to-end theorem. X is the ambient space, Crit its critical subset.
hMeas: continuity of measurement (Galashin Proposition 5.1 and admissible extension).
honto: gauge surjectivity (Galashin Proposition 4.2 and the sentence following (4.3)).
hR: continuity of logarithmic twisted necklace coordinates (Muller--Speyer twist and nonvanishing).
hcompat: the assembled identity R composed with Meas equals G (paper Proposition grad),
whose external monomial input is Galashin Proposition 5.12. This identity remains an
explicit hypothesis; the twist and the measurement map are not constructed in Lean.
No properness, coercivity, inverse-continuity, or dimension hypothesis is assumed. -/
theorem measurement_conditional_homeomorphism (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} [TopologicalSpace X] (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (R : Crit → (Fin n → ℝ))
    (hMeas : Continuous Meas) (honto : Function.Surjective Meas)
    (hR : Continuous R) (hcompat : ∀ θ, R (Meas θ) = (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j))))) θ.val) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∃ g : S ≃ₜ Set.range (fun θ : S => G θ.val), (∀ θ, (g θ).val = G θ.val) ∧
      ∃ e : S ≃ₜ Crit, (∀ θ, e θ = Meas θ) ∧
        ∀ z, ∃ hz : R z ∈ Set.range (fun θ : S => G θ.val), e.symm z = g.symm ⟨R z, hz⟩ := by
  exact conditional_homeomorphism_core F a Crit Meas R hMeas honto hR hcompat

/-- The codomain is the literal real incidence image, with the subspace topology. -/
theorem gradient_incidence_openEmbedding (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    let W := LinearMap.range (Matrix.toLin' (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))))
    ∃ g : S → W, (∀ θ, (g θ).val = G θ.val) ∧ Topology.IsOpenEmbedding g := by
  exact gradient_range_openEmbedding_core F a

theorem variational_image_minimizer (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∀ y ∈ G '' S, ∃! x, x ∈ S ∧ ∀ z ∈ S, Ψ x - dotProduct y x ≤ Ψ z - dotProduct y z := by
  exact variational_image_core F a

end Conj43
