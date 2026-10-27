/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.LipschitzDefs
import Conj43.ExtensionsSandwich
import Conj43.L6Calculus

noncomputable section
namespace Conj43
variable {n : ℕ}

lemma extensions_lipschitz_gradient_eq (F : LooplessBAP n) :
    necklaceGradient F = gradientMap F := rfl

/-- Port of the cycle upper-angle argument in the accepted sandwich. -/
lemma extensions_lipschitz_admissible (F : LooplessBAP n)
    (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F))
    (θ : Fin n → ℝ) (η : ℝ) (hη : 0 < η)
    (hδ : ∀ p q, CrossEdge F p q → η ≤ delta θ (p, q)) : Admissible F θ := by
  have he (c) (hcm : c ∈ cycles) (e) (hem : e ∈ cycleEdges c) : CrossEdge F e.1 e.2 := by
    apply (l5_mem_crossEdges F e.1 e.2).mp
    exact hp.mem_iff.mp (List.mem_flatMap.mpr ⟨c, hcm, hem⟩)
  intro p q hpq
  refine ⟨lt_of_lt_of_le hη (hδ p q hpq), ?_⟩
  obtain ⟨c, hcm, hec⟩ := List.mem_flatMap.mp
    (hp.mem_iff.mpr ((l5_mem_crossEdges F p q).mpr hpq))
  let es := cycleEdges c
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hec
  have hsum : ∑ j : Fin es.length, delta θ (es.get j) = Real.pi := by
    rw [l5_sum_get]
    exact delta_cycle_sum_core θ c (hc c hcm).1 (hc c hcm).2.1 (hc c hcm).2.2
  have hu := extensions_angle_upper es.length η (fun j => delta θ (es.get j))
    (fun j => hδ _ _ (he c hcm _ (List.get_mem _ j))) hsum i
  have hlen3 : 3 ≤ es.length := by simpa [es, cycleEdges] using (hc c hcm).1
  have hlenR : (3 : ℝ) ≤ es.length := by exact_mod_cast hlen3
  change delta θ ((cycleEdges c).get i) + ((es.length : ℝ) - 1) * η ≤ Real.pi at hu
  rw [hi] at hu
  nlinarith only [hu, hlenR, hη]

lemma extensions_lipschitz_pairing_apply (v h : Fin n → ℝ) :
    coordinatePairing v h = dotProduct v h := by
  simp [coordinatePairing, dotProduct]

lemma extensions_lipschitz_matrix_apply (M : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    matrixCLM M h = M.mulVec h := by
  ext r
  simp [matrixCLM, extensions_lipschitz_pairing_apply, Matrix.mulVec]

/-- Port of the gradient path derivative in L6Slice, retaining the matrix form. -/
lemma extensions_lipschitz_line_deriv (F : LooplessBAP n) (x h : Fin n → ℝ) (t : ℝ)
    (ht : Admissible F (x + t • h)) :
    HasDerivAt (fun t => dotProduct h (necklaceGradient F (x + t • h)))
      (dotProduct h ((hessianMatrix F (x + t • h)).mulVec h)) t := by
  have hp : HasDerivAt (fun t : ℝ => x + t • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hg := (gradient_strict_core F _ ht).hasFDerivAt.comp_hasDerivAt t hp
  have hd := (coordinatePairing h).hasFDerivAt.comp_hasDerivAt t hg
  simpa only [Function.comp_def, extensions_lipschitz_pairing_apply,
    extensions_lipschitz_matrix_apply, extensions_lipschitz_gradient_eq] using hd

lemma extensions_lipschitz_graph_monotone (F : LooplessBAP n)
    (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F))
    (η : ℝ) (hη : 0 < η) (hηZ : ∀ c ∈ cycles, η ≤ Real.pi / c.length)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hδ : ∀ θ ∈ C, ∀ p q, CrossEdge F p q → η ≤ delta θ (p, q))
    (θ θ' : Fin n → ℝ) (hθ : θ ∈ C) (hθ' : θ' ∈ C) :
    kappaStarZ cycles η * dotProduct (θ - θ') ((graphLaplacian F).mulVec (θ - θ')) ≤
      dotProduct (necklaceGradient F θ - necklaceGradient F θ') (θ - θ') := by
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : θ' + t • (θ - θ') ∈ C := by
    have heq : θ' + t • (θ - θ') = (1-t) • θ' + t • θ := by module
    rw [heq]
    exact hC hθ' hθ (by linarith [ht.2]) ht.1 (by ring)
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :=
    extensions_lipschitz_line_deriv F θ' (θ-θ') t
      (extensions_lipschitz_admissible F cycles hc hp _ η hη (hδ _ (hline t ht)))
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope
    (fun t => dotProduct (θ-θ') (necklaceGradient F (θ' + t • (θ-θ'))))
    (fun t => dotProduct (θ-θ') ((hessianMatrix F (θ' + t • (θ-θ'))).mulVec (θ-θ')))
    (show (0 : ℝ) < 1 by norm_num)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le, ht.2.le⟩)
  have hs := (sharp_laplacian_sandwich F cycles hc hp _ η hη
    (hδ _ (hline t ⟨ht.1.le, ht.2.le⟩)) hηZ (θ-θ')).1
  rw [heq] at hs
  simpa only [zero_smul, add_zero, one_smul, add_sub_cancel,
    sub_zero, div_one, dotProduct_sub, sub_dotProduct, dotProduct_comm] using hs

end Conj43
