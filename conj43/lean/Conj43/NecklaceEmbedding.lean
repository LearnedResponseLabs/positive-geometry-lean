-- SPDX-License-Identifier: Apache-2.0
import Conj43.NecklaceEmbeddingRecovery
import Conj43.NecklaceEmbeddingControl
import Conj43.L7Conditional

/-! Ordinary necklace coordinates. The layer-7 analytic theorem is reused unchanged. -/
namespace Conj43
variable {n : ℕ}

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

  have hN : Continuous (fun z : Crit => fun r => -Real.log (Δ z r)) := by
    apply continuous_pi
    intro r
    exact (((continuous_apply r).comp hΔ).log (fun z => ne_of_gt (hpos z r))).neg
  obtain ⟨g, hg, e, he, hinv⟩ :=
    gal512_homeomorphism_core F a Crit Meas (fun z => -(fun r => Real.log (Δ z r)))
      hMeas honto hN hlog
  refine ⟨g, hg, e, he, ?_⟩
  intro z
  have hneg : necklaceRecovery F (-(fun r => Real.log (Δ z r))) =
      -necklaceRecovery F (fun r => Real.log (Δ z r)) := by
    simp only [necklaceRecovery, Matrix.mulVec_neg]
  have hz := hinv z
  rw [hneg] at hz
  exact hz

/-- The conditional form of Corollary 32, including recovery from every representative. -/
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

  obtain ⟨g, hg, e, he, hinv⟩ :=
    untwisted_measurement_homeomorphism F a Crit Meas Δ hMeas honto hΔ hpos hlog
  have hclass : Continuous (fun z : Crit => posClass ⟨Δ z, hpos z⟩) :=
    continuous_quot_mk.comp (hΔ.subtype_mk hpos)
  have hR (z : Crit) : -necklaceRecovery F (fun r => Real.log (Δ z r)) =
      (g (e.symm z)).val := by
    obtain ⟨hz, heq⟩ := hinv z
    rw [heq, g.apply_symm_apply]
    rfl
  have hcomp : projectiveRecovery F ∘ (fun z : Crit => posClass ⟨Δ z, hpos z⟩) =
      (fun z => (g (e.symm z)).val) := funext hR
  have hEmb : Topology.IsEmbedding
      (projectiveRecovery F ∘ (fun z : Crit => posClass ⟨Δ z, hpos z⟩)) := by
    rw [hcomp]
    exact Topology.IsEmbedding.subtypeVal.comp (g.isEmbedding.comp e.symm.isEmbedding)
  refine ⟨Topology.IsEmbedding.of_comp hclass (projectiveRecovery_continuous F) hEmb,
    g, hg, ?_⟩
  intro z v hv
  have hk := congrArg (projectiveRecovery F) hv
  change -necklaceRecovery F (fun r => Real.log (v.val r)) =
    -necklaceRecovery F (fun r => Real.log (Δ z r)) at hk
  obtain ⟨hz, heq⟩ := hinv z
  have hv' : -necklaceRecovery F (fun r => Real.log (v.val r)) ∈
      Set.range (fun θ : GaugeSlice F a => gradientMap F θ.val) := hk.symm ▸ hz
  refine ⟨hv', ?_⟩
  have hp : (⟨-necklaceRecovery F (fun r => Real.log (v.val r)), hv'⟩ :
      Set.range (fun θ : GaugeSlice F a => gradientMap F θ.val)) =
      ⟨-necklaceRecovery F (fun r => Real.log (Δ z r)), hz⟩ := Subtype.ext hk
  exact (he _).symm.trans
    ((congrArg e ((congrArg g.symm hp).trans heq.symm)).trans (e.apply_symm_apply z))

theorem untwisted_recovery_ratio [NeZero n] (F : LooplessBAP n) (v : Fin n → ℝ) (hv : ∀ r, 0 < v r) (x : Fin n) :
    -((fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (fun r => Real.log (v r))) x = Real.log (v (F.σ⁻¹ x) / v (F.σ⁻¹ x + 1)) := by
  rw [Real.log_div (ne_of_gt (hv _)) (ne_of_gt (hv _))]
  simp [Matrix.mulVec, dotProduct, Pmat, Dmat, sub_mul, Finset.sum_sub_distrib]

theorem untwisted_recovery_rescale [NeZero n] (F : LooplessBAP n) (v : Fin n → ℝ) (hv : ∀ r, 0 < v r)
    (c : ℝ) (hc : 0 < c) :
    (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (fun r => Real.log (c * v r)) = (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (fun r => Real.log (v r)) := by
  exact ordinary_log_rescale F v hv c hc

theorem necklace_hypotheses_nonvacuous (F : LooplessBAP n) (a : Fin n → ℝ) :
    ∃ Crit : Set (Fin n → ℝ), Crit.Nonempty ∧
      ∃ Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit, ∃ Δ : Crit → (Fin n → ℝ),
        Continuous Meas ∧ Function.Surjective Meas ∧ Continuous Δ ∧ (∀ z r, 0 < Δ z r) ∧
        (∀ θ, ∃ c : ℝ, (fun r => -Real.log (Δ (Meas θ) r)) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) := by
  let f : GaugeSlice F a → (Fin n → ℝ) :=
    fun θ r => Real.exp (-necklaceLogModel F θ.val r)
  let Meas : GaugeSlice F a → Set.range f := fun θ => ⟨f θ, ⟨θ, rfl⟩⟩
  obtain ⟨θ, hθ⟩ := gaugeSlice_nonempty_core F a
  refine ⟨Set.range f, ⟨f ⟨θ, hθ⟩, ⟨⟨θ, hθ⟩, rfl⟩⟩, Meas, Subtype.val,
    ?_, ?_, continuous_subtype_val, ?_, ?_⟩
  · have hf : Continuous f := by
      apply continuous_pi
      intro r
      exact Real.continuous_exp.comp
        (((continuous_apply r).comp (necklaceLogModel_continuous_core F a)).neg)
    exact hf.subtype_mk _
  · rintro ⟨z, θ, rfl⟩
    exact ⟨θ, rfl⟩
  · rintro ⟨z, θ, rfl⟩ r
    exact Real.exp_pos _
  · intro θ
    refine ⟨0, ?_⟩
    change (fun r => -Real.log (Real.exp (-necklaceLogModel F θ.val r))) =
      necklaceLogModel F θ.val + fun _ => 0
    funext r
    simp

/-- The omitted-log-hypothesis control has two explicit, unequal slice points. -/
theorem necklace_log_needed :
    ∃ Crit : Set (Fin 3 → ℝ),
      ∃ Meas : {θ : Fin 3 → ℝ | (∀ p q, CrossEdge fixtureCycle p q → 0 < (fun (θ : Fin 3 → ℝ) (e : Fin 3 × Fin 3) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin 3 → ℝ) (e : Fin 3 × Fin 3) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge fixtureCycle p q ∨ CrossEdge fixtureCycle q p) p q → p ≤ q) → θ p = (0 : Fin 3 → ℝ) p} → Crit,
        ∃ Δ : Crit → (Fin 3 → ℝ), ∃ hpos : ∀ z r, 0 < Δ z r,
          Continuous Meas ∧ Function.Surjective Meas ∧ Continuous Δ ∧
            ¬ Topology.IsEmbedding (fun z : Crit => posClass ⟨Δ z, hpos z⟩) := by
  refine ⟨GaugeSlice fixtureCycle 0, id, (fun _ _ => 1), (fun _ _ => zero_lt_one),
    continuous_id, Function.surjective_id, continuous_const, ?_⟩
  intro h
  let u : GaugeSlice fixtureCycle 0 :=
    ⟨fixtureAngle 1, fixtureAngle_mem (by norm_num) (by norm_num)⟩
  let v : GaugeSlice fixtureCycle 0 :=
    ⟨fixtureAngle (1 / 2), fixtureAngle_mem (by norm_num) (by norm_num)⟩
  have heq : u = v := h.injective rfl
  have hc := congrArg (fun θ : GaugeSlice fixtureCycle 0 => θ.val 1) heq
  norm_num [u, v, fixtureAngle] at hc

end Conj43
