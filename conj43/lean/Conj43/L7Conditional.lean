import Conj43.L7Log

/-! Proposition 5.12 as the external premise, and an inhabited model. -/
namespace Conj43
variable {n : ℕ}

/-- hlog is Galashin Proposition 5.12, equation (5.8), restricted to necklace
rows and after log absolute value: the same scalar c occurs in every row.
The full-pair formula is interpreted on the admissible locus, including the
continuous extension at non-crossing collisions described in Proposition grad. -/
theorem gal512_gradient_core [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} (Crit : Set X) (Meas : GaugeSlice F a → Crit)
    (N : Crit → (Fin n → ℝ))
    (hlog : ∀ θ, ∃ c : ℝ, N (Meas θ) = necklaceLogModel F θ.val + fun _ => c) :
    ∀ θ, necklaceRecovery F (N (Meas θ)) = gradientMap F θ.val := by
  intro θ
  obtain ⟨c, hc⟩ := hlog θ
  rw [hc, necklaceRecovery_constant_core]
  exact necklaceLogModel_gradient_core F θ.val θ.property.1

/-- Surjectivity and the derived identity place P D N in the literal incidence range. -/
theorem gal512_recovery_range_core [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} (Crit : Set X) (Meas : GaugeSlice F a → Crit)
    (N : Crit → (Fin n → ℝ)) (honto : Function.Surjective Meas)
    (hlog : ∀ θ, ∃ c : ℝ, N (Meas θ) = necklaceLogModel F θ.val + fun _ => c) :
    ∀ z, necklaceRecovery F (N z) ∈ LinearMap.range (Matrix.toLin' (realB F)) := by
  intro z
  obtain ⟨θ, rfl⟩ := honto z
  rw [gal512_gradient_core F a Crit Meas N hlog θ]
  exact ⟨(fun j => Real.log (Real.sin (delta θ.val (edgeOf F j)))), rfl⟩

/-- hMeas: Galashin Proposition 5.1 and Theorem 6.9, continuity on the
admissible locus. honto: Galashin Proposition 4.2 and gauge surjectivity
following (4.3). hN: Muller--Speyer regularity of the twist on the open cell,
nonzero necklace coordinates, and a continuous choice of log representatives.
hlog: Galashin Proposition 5.12, equation (5.8), on necklace rows, up to a
common projective log scalar; includes its admissible collision extension.
The twist and measurement themselves remain external; P D N = G is derived. -/
theorem gal512_homeomorphism_core [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} [TopologicalSpace X] (Crit : Set X)
    (Meas : GaugeSlice F a → Crit) (N : Crit → (Fin n → ℝ))
    (hMeas : Continuous Meas) (honto : Function.Surjective Meas)
    (hN : Continuous N)
    (hlog : ∀ θ, ∃ c : ℝ, N (Meas θ) = necklaceLogModel F θ.val + fun _ => c) :
    ∃ g : GaugeSlice F a ≃ₜ Set.range (fun θ : GaugeSlice F a => gradientMap F θ.val),
      (∀ θ, (g θ).val = gradientMap F θ.val) ∧
      ∃ e : GaugeSlice F a ≃ₜ Crit, (∀ θ, e θ = Meas θ) ∧
        ∀ z, ∃ hz : necklaceRecovery F (N z) ∈
            Set.range (fun θ : GaugeSlice F a => gradientMap F θ.val),
          e.symm z = g.symm ⟨necklaceRecovery F (N z), hz⟩ := by
  apply conditional_homeomorphism_core F a Crit Meas (fun z => necklaceRecovery F (N z))
    hMeas honto
  · exact continuous_const.matrix_mulVec (continuous_const.matrix_mulVec hN)
  · exact gal512_gradient_core F a Crit Meas N hlog

/-- Continuity follows from crossing-only positive sine factors; no non-crossing
logarithm is assumed continuous at a collision. -/
theorem necklaceLogModel_continuous_core (F : LooplessBAP n) (a : Fin n → ℝ) :
    Continuous (fun θ : GaugeSlice F a => necklaceLogModel F θ.val) := by
  have heq (θ : GaugeSlice F a) : necklaceLogModel F θ.val =
      (Matrix.of (fun r j => (Mmat F r j : ℝ))).mulVec
        (fun j => Real.log (Real.sin (delta θ.val (edgeOf F j))) + Real.log 2) := by
    rw [necklaceLogModel_crossing_core]
    simp_rw [pairLog_hinge_core F θ.val θ.property.1]
  simp_rw [heq]
  apply continuous_const.matrix_mulVec
  apply continuous_pi
  intro j
  apply Continuous.add _ continuous_const
  apply Continuous.log
  · apply Real.continuous_sin.comp
    change Continuous (fun θ : GaugeSlice F a =>
      θ.val (edgeOf F j).2 - θ.val (edgeOf F j).1 +
        Real.pi * (if (edgeOf F j).2 < (edgeOf F j).1 then 1 else 0))
    exact (((continuous_apply (edgeOf F j).2).comp
      (continuous_subtype_val : Continuous (fun θ : GaugeSlice F a => θ.val))).sub
      ((continuous_apply (edgeOf F j).1).comp continuous_subtype_val)).add continuous_const
  · intro θ
    have he : CrossEdge F (edgeOf F j).1 (edgeOf F j).2 :=
      crossEdge_of_mem F (List.get_mem _ j)
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (θ.property.1 _ _ he).1 (θ.property.1 _ _ he).2)

private theorem component_symm_l7 (F : LooplessBAP n) {p q : Fin n}
    (h : SameComponent F p q) : SameComponent F q p := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head h _ ih => exact ih.trans (.single h.symm)

/-- Equally spaced labels give an admissible point before imposing the gauge. -/
theorem equally_spaced_admissible_core (F : LooplessBAP n) :
    Admissible F (fun p => Real.pi * (p : ℝ) / n) := by
  intro p q he
  have hn : (0 : ℝ) < n := by exact_mod_cast p.pos
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hpn : (p : ℝ) < n := by exact_mod_cast p.isLt
  have hqn : (q : ℝ) < n := by exact_mod_cast q.isLt
  have hpq := crossEdge_ne F he
  have hd : delta (fun p : Fin n => Real.pi * (p : ℝ) / n) (p,q) * n =
      Real.pi * ((q : ℝ) - p + n * (if q < p then 1 else 0)) := by
    dsimp [delta]
    field_simp
  by_cases hqp : q < p
  · have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
    simp only [if_pos hqp, mul_one] at hd
    constructor <;> nlinarith [Real.pi_pos]
  · have hpqR : (p : ℝ) < q := by exact_mod_cast (lt_of_le_of_ne (le_of_not_gt hqp) hpq)
    simp only [if_neg hqp, mul_zero, add_zero] at hd
    constructor <;> nlinarith [Real.pi_pos]

/-- Every gauge slice is inhabited, including cells with coloops and n = 0. -/
theorem gaugeSlice_nonempty_core (F : LooplessBAP n) (a : Fin n → ℝ) :
    (GaugeSlice F a).Nonempty := by
  classical
  let b : Fin n → Fin n := fun p => Classical.choose (anchor_exists_core F p)
  have hb (p : Fin n) : SameComponent F p (b p) ∧ IsGaugeAnchor F (b p) :=
    Classical.choose_spec (anchor_exists_core F p)
  have hbc (p q : Fin n) (h : SameComponent F p q) : b p = b q :=
    anchor_unique_core F _ _ (hb p).2 (hb q).2
      ((component_symm_l7 F (hb p).1).trans (h.trans (hb q).1))
  let θ₀ : Fin n → ℝ := fun p => Real.pi * (p : ℝ) / n
  let s : Fin n → ℝ := fun p => a (b p) - θ₀ (b p)
  have hs : ∀ p q, SameComponent F p q → s p = s q := by
    intro p q h
    simp only [s, hbc p q h]
  refine ⟨θ₀ + s, ?_, ?_⟩
  · intro p q he
    rw [delta_shift_core F θ₀ s hs p q he]
    exact equally_spaced_admissible_core F p q he
  · intro p hp
    have he : b p = p := anchor_unique_core F _ _ (hb p).2 hp
      (component_symm_l7 F (hb p).1)
    simp [s, he]

/-- A concrete inhabited model: Crit is the image of the full necklace log
map, Meas its range restriction, and N the inclusion. Both continuities,
surjectivity, and the log formula (c = 0) hold for every F and anchor vector. -/
theorem gal512_model_core (F : LooplessBAP n) (a : Fin n → ℝ) :
    ∃ Crit : Set (Fin n → ℝ), Crit.Nonempty ∧
      ∃ Meas : GaugeSlice F a → Crit, ∃ N : Crit → (Fin n → ℝ),
        Continuous Meas ∧ Function.Surjective Meas ∧ Continuous N ∧
        (∀ θ, ∃ c : ℝ, N (Meas θ) = necklaceLogModel F θ.val + fun _ => c) := by
  let f : GaugeSlice F a → (Fin n → ℝ) := fun θ => necklaceLogModel F θ.val
  let Meas : GaugeSlice F a → Set.range f := fun θ => ⟨f θ, ⟨θ, rfl⟩⟩
  obtain ⟨θ, hθ⟩ := gaugeSlice_nonempty_core F a
  refine ⟨Set.range f, ⟨f ⟨θ,hθ⟩, ⟨⟨θ,hθ⟩, rfl⟩⟩, Meas, Subtype.val, ?_, ?_,
    continuous_subtype_val, ?_⟩
  · exact (necklaceLogModel_continuous_core F a).subtype_mk _
  · rintro ⟨z, θ, rfl⟩
    exact ⟨θ, rfl⟩
  · intro θ
    refine ⟨0, ?_⟩
    funext r
    simp [Meas, f]

end Conj43
