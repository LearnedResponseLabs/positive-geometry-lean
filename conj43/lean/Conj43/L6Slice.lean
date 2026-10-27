import Conj43.L6Balance

/-! The gauge uses the least label of each crossing component. -/
namespace Conj43
variable {n : ℕ}

/-- A label is fixed exactly when it is least in its component. -/
def IsGaugeAnchor (F : LooplessBAP n) (p : Fin n) : Prop :=
  ∀ q, SameComponent F p q → p ≤ q

/-- One prescribed coordinate per component, including isolated vertices. -/
def GaugeSlice (F : LooplessBAP n) (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {θ | Admissible F θ ∧ ∀ p, IsGaugeAnchor F p → θ p = a p}

/-- Tangent space of the affine gauge plane. -/
def gaugeTangent (F : LooplessBAP n) : Submodule ℝ (Fin n → ℝ) where
  carrier := {h | ∀ p, IsGaugeAnchor F p → h p = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy p hp; simp [hx p hp, hy p hp]
  smul_mem' := by intro c x hx p hp; simp [hx p hp]

/-- Every component contains a least label. -/
theorem anchor_exists_core (F : LooplessBAP n) (p : Fin n) :
    ∃ q, SameComponent F p q ∧ IsGaugeAnchor F q := by
  classical
  let s := Finset.univ.filter (SameComponent F p)
  have hs : s.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, Relation.ReflTransGen.refl⟩⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  · intro r hr
    apply Finset.min'_le
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ r, ((Finset.mem_filter.mp (Finset.min'_mem s hs)).2).trans hr⟩

/-- Distinct anchor labels cannot belong to the same component. -/
theorem anchor_unique_core (F : LooplessBAP n) (p q : Fin n)
    (hp : IsGaugeAnchor F p) (hq : IsGaugeAnchor F q) (hpq : SameComponent F p q) : p = q := by
  have hqp : SameComponent F q p := by
    clear hp hq
    induction hpq using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head h _ ih => exact ih.trans (.single h.symm)
  exact le_antisymm (hp q hpq) (hq p hqp)

/-- The Hessian is positive definite on the tangent space. -/
theorem tangent_positive_core (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) (h : Fin n → ℝ) (hh : h ∈ gaugeTangent F) (hne : h ≠ 0) :
    0 < hessianQ F θ h := by
  have hn := (hessian_psd_core F θ hθ h).1
  apply lt_of_le_of_ne hn
  intro hz
  have hc := (hessian_kernel_components_core F θ hθ h).mp hz.symm
  apply hne
  funext p
  obtain ⟨q, hpq, hq⟩ := anchor_exists_core F p
  exact (hc p q hpq).trans (hh q hq)

/-- The chamber is convex: all edge bounds are affine inequalities. -/
theorem admissible_convex_core (F : LooplessBAP n) : Convex ℝ {θ | Admissible F θ} := by
  intro x hx y hy a b ha hb hab p q he
  have hdx := hx p q he
  have hdy := hy p q he
  have heq : delta (a • x + b • y) (p, q) = a * delta x (p, q) + b * delta y (p, q) := by
    simp only [delta, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => z * (Real.pi * (if q < p then 1 else 0))) hab]
  rw [heq]
  exact (convex_Ioo (0 : ℝ) Real.pi) hdx hdy ha hb hab

/-- The affine gauge constraints preserve convexity. -/
theorem slice_convex_core (F : LooplessBAP n) (a : Fin n → ℝ) : Convex ℝ (GaugeSlice F a) := by
  intro x hx y hy c d hc hd hcd
  refine ⟨admissible_convex_core F hx.1 hy.1 hc hd hcd, ?_⟩
  intro p hp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx.2 p hp, hy.2 p hp]
  rw [← add_mul, hcd, one_mul]

private theorem slice_sub_tangent (F : LooplessBAP n) (a x y : Fin n → ℝ)
    (hx : x ∈ GaugeSlice F a) (hy : y ∈ GaugeSlice F a) : y - x ∈ gaugeTangent F := by
  intro p hp
  simp [hy.2 p hp, hx.2 p hp]

private theorem pairing_apply (v h : Fin n → ℝ) : coordinatePairing v h = dotProduct v h := by
  simp [coordinatePairing, dotProduct]

private theorem matrix_apply (M : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    matrixCLM M h = M.mulVec h := by
  ext r
  simp [matrixCLM, pairing_apply, Matrix.mulVec]

private theorem line_slice (F : LooplessBAP n) (a x y : Fin n → ℝ)
    (hx : x ∈ GaugeSlice F a) (hy : y ∈ GaugeSlice F a) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ GaugeSlice F a := by
  have heq : x + t • (y - x) = (1-t) • x + t • y := by module
  rw [heq]
  exact slice_convex_core F a hx hy (by linarith [ht.2]) ht.1 (by ring)

private theorem line_gradient_deriv (F : LooplessBAP n) (x h : Fin n → ℝ) (t : ℝ)
    (ht : Admissible F (x + t • h)) :
    HasDerivAt (fun t => dotProduct h (gradientMap F (x + t • h)))
      (hessianQ F (x + t • h) h) t := by
  have hp : HasDerivAt (fun t : ℝ => x + t • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hg := (gradient_strict_core F _ ht).hasFDerivAt.comp_hasDerivAt t hp
  have hd := (coordinatePairing h).hasFDerivAt.comp_hasDerivAt t hg
  simpa only [Function.comp_def, pairing_apply, matrix_apply, hessian_matrix_form_core] using hd

private theorem line_gradient_mono (F : LooplessBAP n) (a x y : Fin n → ℝ)
    (hx : x ∈ GaugeSlice F a) (hy : y ∈ GaugeSlice F a) (hne : x ≠ y) :
    StrictMonoOn (fun t : ℝ => dotProduct (y-x) (gradientMap F (x + t • (y-x)))) (Set.Icc 0 1) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :=
    line_gradient_deriv F x (y-x) t (line_slice F a x y hx hy t ht).1
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    apply tangent_positive_core F _ (line_slice F a x y hx hy t (interior_subset ht)).1
      (y-x) (slice_sub_tangent F a x y hx hy)
    exact sub_ne_zero.mpr hne.symm

/-- Strict monotonicity of the gradient on the gauge slice. -/
theorem gradient_monotone_core (F : LooplessBAP n) (a x y : Fin n → ℝ)
    (hx : x ∈ GaugeSlice F a) (hy : y ∈ GaugeSlice F a) (hne : x ≠ y) :
    0 < dotProduct (gradientMap F y - gradientMap F x) (y-x) := by
  have hm := line_gradient_mono F a x y hx hy hne
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp) (show (1 : ℝ) ∈ Set.Icc 0 1 by simp) (by norm_num)
  simpa only [zero_smul, add_zero, one_smul, add_sub_cancel, dotProduct_sub,
    dotProduct_comm, sub_pos] using hm

/-- Injectivity on the slice follows from strict monotonicity. -/
theorem gradient_injective_core (F : LooplessBAP n) (a : Fin n → ℝ) :
    Set.InjOn (gradientMap F) (GaugeSlice F a) := by
  intro x hx y hy heq
  by_contra hne
  have h := gradient_monotone_core F a x y hx hy hne
  rw [heq, sub_self, zero_dotProduct] at h
  exact lt_irrefl 0 h

private theorem line_potential_deriv (F : LooplessBAP n) (x h : Fin n → ℝ) (t : ℝ)
    (ht : Admissible F (x + t • h)) :
    HasDerivAt (fun t => potential F (x + t • h))
      (dotProduct h (gradientMap F (x + t • h))) t := by
  have hp : HasDerivAt (fun t : ℝ => x + t • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hd := (potential_strict_core F _ ht).hasFDerivAt.comp_hasDerivAt t hp
  simpa only [Function.comp_def, pairing_apply, dotProduct_comm] using hd

private theorem line_strictConvex (F : LooplessBAP n) (a x y : Fin n → ℝ)
    (hx : x ∈ GaugeSlice F a) (hy : y ∈ GaugeSlice F a) (hne : x ≠ y) :
    StrictConvexOn ℝ (Set.Icc 0 1) (fun t : ℝ => potential F (x + t • (y-x))) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :=
    line_potential_deriv F x (y-x) t (line_slice F a x y hx hy t ht).1
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht u hu htu
    rw [(hd t (interior_subset ht)).deriv, (hd u (interior_subset hu)).deriv]
    exact line_gradient_mono F a x y hx hy hne (interior_subset ht) (interior_subset hu) htu

/-- Strict convexity of the integral potential on the gauge slice. -/
theorem potential_strictConvex_core (F : LooplessBAP n) (a : Fin n → ℝ) :
    StrictConvexOn ℝ (GaugeSlice F a) (potential F) := by
  refine ⟨slice_convex_core F a, ?_⟩
  intro x hx y hy hne c d hc hd hcd
  have h := (line_strictConvex F a x y hx hy hne).2
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp) (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
    (by norm_num) hc hd hcd
  have heq : x + d • (y-x) = c • x + d • y := by
    have : c = 1-d := by linarith
    rw [this]; module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, one_smul,
    add_zero, add_sub_cancel, heq] using h

/-- The tangent plane at any slice point is a strict supporting plane. -/
theorem potential_support_core (F : LooplessBAP n) (a x y : Fin n → ℝ)
    (hx : x ∈ GaugeSlice F a) (hy : y ∈ GaugeSlice F a) (hne : x ≠ y) :
    dotProduct (gradientMap F x) (y-x) < potential F y - potential F x := by
  have hd := line_potential_deriv F x (y-x) 0 (by simpa using hx.1)
  have h := (line_strictConvex F a x y hx hy hne).lt_slope_of_hasDerivAt
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp) (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
    (by norm_num) hd
  simpa [slope_def_field, dotProduct_comm] using h

/-- For a target already in the gradient image, its preimage is the unique minimizer. -/
theorem variational_core (F : LooplessBAP n) (a x : Fin n → ℝ) (hx : x ∈ GaugeSlice F a) :
    ∀ z ∈ GaugeSlice F a,
      potential F x - dotProduct (gradientMap F x) x ≤
        potential F z - dotProduct (gradientMap F x) z ∧
      (potential F z - dotProduct (gradientMap F x) z =
        potential F x - dotProduct (gradientMap F x) x ↔ z = x) := by
  intro z hz
  by_cases heq : z = x
  · subst z; simp
  · have h := potential_support_core F a x z hx hz (fun h => heq h.symm)
    rw [dotProduct_sub] at h
    constructor
    · linarith
    · constructor
      · intro he; exfalso; linarith
      · exact fun he => (heq he).elim

end Conj43
