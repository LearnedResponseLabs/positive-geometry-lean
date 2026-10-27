import Conj43.Delta
import Conj43.Statements

/-! Assembly of the cotangent forms along the winding-one partition. -/
namespace Conj43
variable {n : ℕ}

theorem l5_mem_crossEdges (F : LooplessBAP n) (p q : Fin n) :
    (p, q) ∈ crossEdges F ↔ CrossEdge F p q := by
  simp [crossEdges, List.mem_flatMap, List.mem_filterMap]

theorem l5_sum_get {α : Type*} (l : List α) (f : α → ℝ) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem cycle_cot_form (F : LooplessBAP n) (θ h : Fin n → ℝ)
    (hθ : Admissible F θ) (c : List (Fin n)) (hlen : 3 ≤ c.length)
    (hnd : c.Nodup) (hw : winding c = n)
    (he : ∀ e ∈ cycleEdges c, CrossEdge F e.1 e.2) :
    0 ≤ ((cycleEdges c).map fun e => Real.cot (delta θ e) * (h e.2 - h e.1)^2).sum ∧
    (((cycleEdges c).map fun e => Real.cot (delta θ e) * (h e.2 - h e.1)^2).sum = 0 ↔
      ∀ e ∈ cycleEdges c, h e.1 = h e.2) := by
  let es := cycleEdges c
  have hlen' : 3 ≤ es.length := by simpa [es, cycleEdges] using hlen
  have hc := cot_cycle_inequality es.length hlen'
    (fun i => delta θ (es.get i)) (fun i => h (es.get i).2 - h (es.get i).1)
    (fun i => (hθ _ _ (he _ (List.get_mem _ _))).1)
    (by rw [l5_sum_get]; exact delta_cycle_sum_core θ c hlen hnd hw)
    (by rw [l5_sum_get es (fun e => h e.2 - h e.1)]; exact cycle_difference_sum c h)
  rw [l5_sum_get es (fun e => Real.cot (delta θ e) * (h e.2 - h e.1)^2)] at hc
  refine ⟨hc.1, hc.2.trans ?_⟩
  constructor
  · intro hh e he'
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp he'
    exact (sub_eq_zero.mp (hh i)).symm
  · intro hh i
    exact sub_eq_zero.mpr (hh _ (List.get_mem _ _)).symm

theorem l5_sum_flatMap {α β : Type*} (cs : List α) (es : α → List β) (f : β → ℝ) :
    ((cs.flatMap es).map f).sum = (cs.map fun c => ((es c).map f).sum).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem l5_sum_zero_iff {α : Type*} (l : List α) (f : α → ℝ)
    (hf : ∀ a ∈ l, 0 ≤ f a) : (l.map f).sum = 0 ↔ ∀ a ∈ l, f a = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hf a (by simp)
    have hl := List.sum_nonneg (l := l.map f) (by
      intro x hx; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact hf b (by simp [hb]))
    rw [List.map_cons, List.sum_cons, add_eq_zero_iff_of_nonneg ha hl,
      ih (fun b hb => hf b (by simp [hb]))]
    simp

/-- The assembled form is positive semidefinite, with precisely the edge shifts
as its zero set. No sign condition is imposed on individual cotangents. -/
theorem hessian_psd_core (F : LooplessBAP n) (θ : Fin n → ℝ) (hθ : Admissible F θ)
    (h : Fin n → ℝ) :
    0 ≤ hessianQ F θ h ∧
      (hessianQ F θ h = 0 ↔ ∀ p q, CrossEdge F p q → h p = h q) := by
  obtain ⟨cs, hcs, hp⟩ := winding_one_partition n F
  let f := fun e : Fin n × Fin n => Real.cot (delta θ e) * (h e.2 - h e.1)^2
  let g := fun c => ((cycleEdges c).map f).sum
  have he (c) (hc : c ∈ cs) (e) (he : e ∈ cycleEdges c) : CrossEdge F e.1 e.2 := by
    apply (l5_mem_crossEdges F e.1 e.2).mp
    exact hp.mem_iff.mp (List.mem_flatMap.mpr ⟨c, hc, he⟩)
  have hg (c) (hc : c ∈ cs) :=
    cycle_cot_form F θ h hθ c (hcs c hc).1 (hcs c hc).2.1 (hcs c hc).2.2 (he c hc)
  have hq : hessianQ F θ h = (cs.map g).sum := by
    unfold hessianQ
    rw [← (hp.map f).sum_eq, l5_sum_flatMap]
  rw [hq]
  refine ⟨List.sum_nonneg ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact (hg c hc).1
  · rw [l5_sum_zero_iff cs g (fun c hc => (hg c hc).1)]
    constructor
    · intro hz p q hpq
      have hm := hp.mem_iff.mpr ((l5_mem_crossEdges F p q).mpr hpq)
      obtain ⟨c, hc, he'⟩ := List.mem_flatMap.mp hm
      exact (hg c hc).2.mp (hz c hc) (p, q) he'
    · intro hz c hc
      exact (hg c hc).2.mpr (fun e he' => hz _ _ (he c hc e he'))

/-- Constancy on crossing edges is equivalent to constancy on every component,
where components are finite undirected crossing paths, including length zero. -/
theorem edge_constant_iff_component_constant (F : LooplessBAP n) (h : Fin n → ℝ) :
    (∀ p q, CrossEdge F p q → h p = h q) ↔
      (∀ p q, SameComponent F p q → h p = h q) := by
  constructor
  · intro hh p q hpq
    induction hpq using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head he _ ih =>
      rcases he with he | he
      · exact (hh _ _ he).trans ih
      · exact (hh _ _ he).symm.trans ih
  · intro hh p q he
    exact hh p q (Relation.ReflTransGen.single (Or.inl he))

/-- The null directions are exactly the component shifts. -/
theorem hessian_kernel_components_core (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) (h : Fin n → ℝ) :
    hessianQ F θ h = 0 ↔ ∀ p q, SameComponent F p q → h p = h q :=
  (hessian_psd_core F θ hθ h).2.trans (edge_constant_iff_component_constant F h)

/-- Multiplication by the transpose incidence matrix takes edge differences. -/
theorem realB_vecMul (F : LooplessBAP n) (h : Fin n → ℝ) (j : EdgeIdx F) :
    Matrix.vecMul h (realB F) j = h (edgeOf F j).2 - h (edgeOf F j).1 := by
  classical
  simp [Matrix.vecMul, dotProduct, realB, Bmat, mul_sub, Finset.sum_sub_distrib]

/-- The matrix quadratic form agrees exactly with the crossing-edge sum. -/
theorem hessian_matrix_form_core (F : LooplessBAP n) (θ h : Fin n → ℝ) :
    dotProduct h ((hessianMatrix F θ).mulVec h) = hessianQ F θ h := by
  classical
  unfold hessianMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have ht : (realB F).transpose.mulVec h = Matrix.vecMul h (realB F) := by
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rw [ht]
  simp only [dotProduct, Matrix.mulVec_diagonal, realB_vecMul]
  calc
    _ = ∑ j : EdgeIdx F, Real.cot (delta θ (edgeOf F j)) *
        (h (edgeOf F j).2 - h (edgeOf F j).1)^2 := by
      apply Finset.sum_congr rfl; intro j _; ring
    _ = hessianQ F θ h := l5_sum_get (crossEdges F)
      (fun e => Real.cot (delta θ e) * (h e.2 - h e.1)^2)

/-- The actual matrix kernel is exactly the component-shift space. -/
theorem hessian_matrix_kernel_core (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : Admissible F θ) (h : Fin n → ℝ) :
    (hessianMatrix F θ).mulVec h = 0 ↔
      ∀ p q, SameComponent F p q → h p = h q := by
  constructor
  · intro hz
    apply (hessian_kernel_components_core F θ hθ h).mp
    rw [← hessian_matrix_form_core, hz, dotProduct_zero]
  · intro hh
    have he := (edge_constant_iff_component_constant F h).mpr hh
    have hb : (realB F).transpose.mulVec h = 0 := by
      ext j
      rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose, realB_vecMul]
      apply sub_eq_zero.mpr
      exact (he _ _ ((l5_mem_crossEdges F _ _).mp (List.get_mem _ j))).symm
    unfold hessianMatrix
    rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_zero]

end Conj43
