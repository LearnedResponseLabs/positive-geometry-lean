import Conj43.L7Conditional

/-! Layer 7 frozen necklace log statements. -/
namespace Conj43
variable {n : ℕ}

/-- All unordered pairs occur on the left; Mis and other non-crossing exponents
vanish formally, before any row differences. -/
theorem necklace_log_crossing (F : LooplessBAP n) (θ : Fin n → ℝ) :
    (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ = (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Mmat F r j : ℝ))).mulVec (fun j => (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ (edgeOf F j)) := by
  exact necklaceLogModel_crossing_core F θ

theorem necklace_recovery_constant [NeZero n] (F : LooplessBAP n) (z : Fin n → ℝ) (c : ℝ) :
    (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (z + fun _ => c) = (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) z := by
  exact necklaceRecovery_constant_core F z c

theorem necklace_log_hinge (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) (j : EdgeIdx F) :
    (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ (edgeOf F j) = Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j))) + Real.log 2 := by
  exact pairLog_hinge_core F θ hθ j

theorem necklace_log_gradient [NeZero n] (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) :
    (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) ((fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ) = (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j))))) θ := by
  exact necklaceLogModel_gradient_core F θ hθ

/-- hlog: Galashin Proposition 5.12, equation (5.8), restricted to necklace
rows after log absolute value and a common projective scalar. Includes the
admissible collision extension; zero-exponent pairs use the totalized log. -/
theorem gal512_gradient [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (N : Crit → (Fin n → ℝ))
    (hlog : ∀ θ, ∃ c : ℝ, N (Meas θ) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) :
    ∀ θ, (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (N (Meas θ)) = (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j))))) θ.val := by
  exact gal512_gradient_core F a Crit Meas N hlog

theorem gal512_recovery_incidence [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (N : Crit → (Fin n → ℝ))
    (honto : Function.Surjective Meas)
    (hlog : ∀ θ, ∃ c : ℝ, N (Meas θ) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) :
    ∀ z, (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (N z) ∈ LinearMap.range (Matrix.toLin' (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ)))) := by
  exact gal512_recovery_range_core F a Crit Meas N honto hlog

/-- hMeas: Galashin Proposition 5.1 and Theorem 6.9 (admissible measurement).
honto: Galashin Proposition 4.2 and gauge surjectivity following (4.3).
hN: Muller--Speyer twist regularity on the open cell and nonzero necklace
coordinates, with a continuous choice of logarithmic representatives.
hlog: Galashin Proposition 5.12, equation (5.8), on necklace rows, including
the admissible collision extension, up to a common projective log scalar.
The identity R composed with Meas equals G is derived internally. -/
theorem gal512_measurement_homeomorphism [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} [TopologicalSpace X] (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (N : Crit → (Fin n → ℝ))
    (hMeas : Continuous Meas) (honto : Function.Surjective Meas)
    (hN : Continuous N)
    (hlog : ∀ θ, ∃ c : ℝ, N (Meas θ) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) :
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j)))))
    let R := fun z => (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (N z)
    ∃ g : S ≃ₜ Set.range (fun θ : S => G θ.val), (∀ θ, (g θ).val = G θ.val) ∧
      ∃ e : S ≃ₜ Crit, (∀ θ, e θ = Meas θ) ∧
        ∀ z, ∃ hz : R z ∈ Set.range (fun θ : S => G θ.val), e.symm z = g.symm ⟨R z, hz⟩ := by
  exact gal512_homeomorphism_core F a Crit Meas N hMeas honto hN hlog

theorem gauge_slice_nonempty (F : LooplessBAP n) (a : Fin n → ℝ) :
    ({θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}).Nonempty := by
  exact gaugeSlice_nonempty_core F a

/-- The hypotheses are jointly realized by the image of the necklace log
map and its inclusion. Crit is nonempty for every F and every anchor vector. -/
theorem gal512_hypotheses_nonvacuous (F : LooplessBAP n) (a : Fin n → ℝ) :
    ∃ Crit : Set (Fin n → ℝ), Crit.Nonempty ∧
      ∃ Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit, ∃ N : Crit → (Fin n → ℝ),
        Continuous Meas ∧ Function.Surjective Meas ∧ Continuous N ∧
        (∀ θ, ∃ c : ℝ, N (Meas θ) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) := by
  exact gal512_model_core F a

end Conj43
