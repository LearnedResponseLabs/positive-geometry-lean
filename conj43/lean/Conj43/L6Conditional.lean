import Conj43.L6Range

/-! The end-to-end composition, with the measurement and twist inputs explicit. -/
namespace Conj43
variable {n : ℕ}

/-- Conditional composition theorem. `X` is the ambient topological space and `Crit`
its critical subset. `hMeas` supplies continuity of measurement (Galashin Proposition 5.1
and its admissible extension); `honto` supplies gauge surjectivity (Proposition 4.2
and the sentence following (4.3)); `hR` supplies continuity of logarithmic twisted
necklace coordinates (Muller--Speyer twist and nonvanishing); `hcompat` is the
assembled identity of Proposition grad, whose external monomial input is Galashin
Proposition 5.12. The identity is a hypothesis here, not a formalization of the twist.
No properness, coercivity, dimension, or inverse-continuity hypothesis is assumed. -/
theorem conditional_homeomorphism_core (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} [TopologicalSpace X] (Crit : Set X)
    (Meas : GaugeSlice F a → Crit) (R : Crit → (Fin n → ℝ))
    (hMeas : Continuous Meas) (honto : Function.Surjective Meas)
    (hR : Continuous R) (hcompat : ∀ θ, R (Meas θ) = gradientMap F θ.val) :
    ∃ g : GaugeSlice F a ≃ₜ Set.range (fun θ : GaugeSlice F a => gradientMap F θ.val),
      (∀ θ, (g θ).val = gradientMap F θ.val) ∧
      ∃ e : GaugeSlice F a ≃ₜ Crit, (∀ θ, e θ = Meas θ) ∧
        ∀ z, ∃ hz : R z ∈ Set.range (fun θ : GaugeSlice F a => gradientMap F θ.val),
          e.symm z = g.symm ⟨R z, hz⟩ := by
  have hG := gradient_embedding_core F a
  have hRM : Topology.IsEmbedding (R ∘ Meas) := by
    have heq : R ∘ Meas = (fun θ : GaugeSlice F a => gradientMap F θ.val) := funext hcompat
    rw [heq]
    exact hG
  have hM := Topology.IsEmbedding.of_comp hMeas hR hRM
  let g := hG.toHomeomorph
  let e := hM.toHomeomorphOfSurjective honto
  refine ⟨g, (fun _ => rfl), e, (fun _ => rfl), ?_⟩
  intro z
  have he : Meas (e.symm z) = z := e.apply_symm_apply z
  have hz : R z ∈ Set.range (fun θ : GaugeSlice F a => gradientMap F θ.val) := by
    refine ⟨e.symm z, ?_⟩
    change gradientMap F (e.symm z).val = R z
    rw [← hcompat, he]
  refine ⟨hz, ?_⟩
  apply g.injective
  rw [g.apply_symm_apply]
  apply Subtype.ext
  change gradientMap F (e.symm z).val = R z
  rw [← hcompat, he]

/-- Every target in the gradient image has exactly one variational minimizer. -/
theorem variational_image_core (F : LooplessBAP n) (a y : Fin n → ℝ)
    (hy : y ∈ gradientMap F '' GaugeSlice F a) :
    ∃! x, x ∈ GaugeSlice F a ∧ ∀ z ∈ GaugeSlice F a,
      potential F x - dotProduct y x ≤ potential F z - dotProduct y z := by
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨x, ⟨hx, fun z hz => (variational_core F a x hx z hz).1⟩, ?_⟩
  intro z hz
  apply (variational_core F a x hx z hz.1).2.mp
  exact le_antisymm (hz.2 x hx) (variational_core F a x hx z hz.1).1

end Conj43
