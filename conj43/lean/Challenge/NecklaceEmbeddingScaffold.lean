/-
Challenge/NecklaceEmbedding.lean: the paper's Corollary 32 (cor:necklace-embedding) and Theorem 1 restated in the
ordinary Grassmann-necklace minors, in a conditional form, frozen 2026-10-26.

Lean constructs neither the critical measurement map nor the Grassmannian. As in
`Conj43.gal512_measurement_homeomorphism`, the critical cell is an abstract `Crit` in a topological space `X`, the
measurement map an abstract `Meas` on the gauge slice, and the necklace minors an abstract `Δ : Crit → (Fin n → ℝ)`,
a continuous choice of positive representatives of `(Δ_{I_1}(X), …, Δ_{I_n}(X))` (Lean row r is the paper's
I_{r+1}). No hypothesis mentions the twist.

Hypotheses and what they stand for:
* hMeas: the measurement map is continuous on the slice (Galashin, Prop. 5.1 with Lem. 5.13), as (H1).
* honto: it maps the slice onto the critical cell (Galashin, Prop. 4.2 and the sentence after eq. (4.3)), as (H2).
* hΔ, hpos: the ordinary necklace minors are continuous and positive on the critical cell, for a continuous choice of
  representative (the critical cell lies in the totally positive cell, Galashin Prop. 4.2, Def. 1.8 and eq. (2.6);
  necklace minors do not vanish on the open positroid variety, Galashin eq. (2.4); Plücker coordinates are polynomial).
  They replace (H3), with no twist.
* hlog: minus the logarithm of the ordinary necklace minors is the logarithmic necklace monomial of Galashin's
  Prop. 5.12 up to one common constant (the paper's eq. (untwisted): Galashin Prop. 5.12 at the twisted minors,
  with Δ_I(A) Δ_I(τ̃(A)) = 1 from the proof of Galashin Prop. 5.4, citing the proof of Muller–Speyer Prop. 6.6).
  It replaces (H4) of `gal512_measurement_homeomorphism`.

The expressions for the gauge slice, the necklace monomial, `P_f D` and the gradient `G` are verbatim those of the
frozen statements of `Challenge/Conj43.lean`.
-/
import Conj43.NecklaceEmbeddingDefs

namespace Conj43

variable {n : ℕ}

/-- eq. (untwisted), its ratio form: for a positive vector v, `(−P_f D log v)_x = log(v_{s_x} / v_{s_x+1})`,
`s_x = σ⁻¹ x`, the necklace position read cyclically. -/
theorem untwisted_recovery_ratio [NeZero n] (F : LooplessBAP n) (v : Fin n → ℝ) (hv : ∀ r, 0 < v r) (x : Fin n) :
    -((fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (fun r => Real.log (v r))) x = Real.log (v (F.σ⁻¹ x) / v (F.σ⁻¹ x + 1)) := by
  sorry

/-- The recovered vector does not depend on the positive representative. -/
theorem untwisted_recovery_rescale [NeZero n] (F : LooplessBAP n) (v : Fin n → ℝ) (hv : ∀ r, 0 < v r)
    (c : ℝ) (hc : 0 < c) :
    (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (fun r => Real.log (c * v r)) = (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (fun r => Real.log (v r)) := by
  sorry

/-- Theorem 1 in the ordinary necklace minors: under the hypotheses above, the gradient is a homeomorphism of the
slice onto its image, the measurement map is a homeomorphism of the slice onto `Crit`, and its inverse is
`G⁻¹ ∘ R` with `R z = −P_f D log Δ(z)`. -/
theorem untwisted_measurement_homeomorphism [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} [TopologicalSpace X] (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (Δ : Crit → (Fin n → ℝ))
    (hMeas : Continuous Meas) (honto : Function.Surjective Meas)
    (hΔ : Continuous Δ) (hpos : ∀ z r, 0 < Δ z r)
    (hlog : ∀ θ, ∃ c : ℝ, (fun r => -Real.log (Δ (Meas θ) r)) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) :
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j)))))
    let R := fun z => -((fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (fun r => Real.log (Δ z r)))
    ∃ g : S ≃ₜ Set.range (fun θ : S => G θ.val), (∀ θ, (g θ).val = G θ.val) ∧
      ∃ e : S ≃ₜ Crit, (∀ θ, e θ = Meas θ) ∧
        ∀ z, ∃ hz : R z ∈ Set.range (fun θ : S => G θ.val), e.symm z = g.symm ⟨R z, hz⟩ := by
  sorry

/-- Corollary 32: the necklace map `N_f z = [Δ(z)_0 : ⋯ : Δ(z)_{n-1}]` into `P^{n-1}_{>0}` is a topological
embedding, with inverse `N ↦ Meas(G⁻¹(−P_f D log N))` on its image, for any positive representative of `N`. -/
theorem necklace_conditional_embedding [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} [TopologicalSpace X] (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (Δ : Crit → (Fin n → ℝ))
    (hMeas : Continuous Meas) (honto : Function.Surjective Meas)
    (hΔ : Continuous Δ) (hpos : ∀ z r, 0 < Δ z r)
    (hlog : ∀ θ, ∃ c : ℝ, (fun r => -Real.log (Δ (Meas θ) r)) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) :
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j)))))
    Topology.IsEmbedding (fun z : Crit => posClass ⟨Δ z, hpos z⟩) ∧
      ∃ g : S ≃ₜ Set.range (fun θ : S => G θ.val), (∀ θ, (g θ).val = G θ.val) ∧
        ∀ z (v : PosVec n), posClass v = posClass ⟨Δ z, hpos z⟩ →
          ∃ hv : -((fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (fun r => Real.log (v.val r))) ∈ Set.range (fun θ : S => G θ.val),
            Meas (g.symm ⟨-((fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (fun r => Real.log (v.val r))), hv⟩) = z := by
  sorry

/-- The hypotheses are jointly satisfiable, for every `F` and anchor `a`, with `Crit` nonempty. -/
theorem necklace_hypotheses_nonvacuous (F : LooplessBAP n) (a : Fin n → ℝ) :
    ∃ Crit : Set (Fin n → ℝ), Crit.Nonempty ∧
      ∃ Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit, ∃ Δ : Crit → (Fin n → ℝ),
        Continuous Meas ∧ Function.Surjective Meas ∧ Continuous Δ ∧ (∀ z r, 0 < Δ z r) ∧
        (∀ θ, ∃ c : ℝ, (fun r => -Real.log (Δ (Meas θ) r)) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) := by
  sorry

/-- Control: `hlog` cannot be dropped. For `fixtureCycle` and the anchor 0 there are `Crit`, `Meas`, `Δ` meeting
every other hypothesis (the slice itself, its identity, the constant vector 1) whose necklace map is not an
embedding: the slice has two distinct points with the same necklace class. -/
theorem necklace_log_needed :
    ∃ Crit : Set (Fin 3 → ℝ),
      ∃ Meas : {θ : Fin 3 → ℝ | (∀ p q, CrossEdge fixtureCycle p q → 0 < (fun (θ : Fin 3 → ℝ) (e : Fin 3 × Fin 3) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin 3 → ℝ) (e : Fin 3 × Fin 3) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge fixtureCycle p q ∨ CrossEdge fixtureCycle q p) p q → p ≤ q) → θ p = (0 : Fin 3 → ℝ) p} → Crit,
        ∃ Δ : Crit → (Fin 3 → ℝ), ∃ hpos : ∀ z r, 0 < Δ z r,
          Continuous Meas ∧ Function.Surjective Meas ∧ Continuous Δ ∧
            ¬ Topology.IsEmbedding (fun z : Crit => posClass ⟨Δ z, hpos z⟩) := by
  sorry

end Conj43
