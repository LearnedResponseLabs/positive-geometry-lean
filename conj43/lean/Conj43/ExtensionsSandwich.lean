/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs
import Conj43.ExtensionsSharp
import Conj43.Hessian

noncomputable section
namespace Conj43
variable {n : ℕ}

lemma extensions_graph_form (F : LooplessBAP n) (h : Fin n → ℝ) :
    dotProduct h ((graphLaplacian F).mulVec h) =
      ((crossEdges F).map fun e => (h e.2 - h e.1) ^ 2).sum := by
  classical
  unfold graphLaplacian
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have ht : (realB F).transpose.mulVec h = Matrix.vecMul h (realB F) := by
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rw [ht]
  simp only [dotProduct, realB_vecMul]
  simp_rw [← pow_two]
  exact l5_sum_get (crossEdges F) (fun e => (h e.2 - h e.1) ^ 2)

lemma extensions_kappa_min_le (cycles : List (List (Fin n))) (η : ℝ)
    (c : List (Fin n)) (hc : c ∈ cycles) : kappaStarZ cycles η ≤ kappaStar c.length η := by
  have hx : kappaStar c.length η ∈ cycles.map (fun c => kappaStar c.length η) :=
    List.mem_map.mpr ⟨c, hc, rfl⟩
  cases he : (cycles.map fun c => kappaStar c.length η).min? with
  | none =>
    have hn := List.min?_eq_none_iff.mp he
    rw [hn] at hx
    simp at hx
  | some a =>
    simpa [kappaStarZ, he] using (List.min?_eq_some_iff.mp he).2 _ hx

lemma extensions_cot_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < Real.pi) :
    Real.cot y ≤ Real.cot x := by
  have hsx := Real.sin_pos_of_pos_of_lt_pi hx (lt_of_le_of_lt hxy hy)
  have hsy := Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hx hxy) hy
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hxy)
    (show y - x ≤ Real.pi by linarith)
  have he : Real.cot x - Real.cot y = Real.sin (y - x) / (Real.sin x * Real.sin y) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
      div_sub_div _ _ hsx.ne' hsy.ne', Real.sin_sub]
    congr 1
    ring
  have hh := div_nonneg hs (mul_pos hsx hsy).le
  rw [← he] at hh
  exact sub_nonneg.mp hh

theorem sharp_laplacian_sandwich (F : LooplessBAP n) (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F))
    (θ : Fin n → ℝ) (η : ℝ) (hη : 0 < η)
    (hδ : ∀ p q, CrossEdge F p q → η ≤ delta θ (p, q))
    (hηZ : ∀ c ∈ cycles, η ≤ Real.pi / c.length) (h : Fin n → ℝ) :
    kappaStarZ cycles η * dotProduct h ((graphLaplacian F).mulVec h) ≤
        dotProduct h ((hessianMatrix F θ).mulVec h) ∧
      dotProduct h ((hessianMatrix F θ).mulVec h) ≤
        Real.cot η * dotProduct h ((graphLaplacian F).mulVec h) := by
  have he (c) (hcm : c ∈ cycles) (e) (hem : e ∈ cycleEdges c) : CrossEdge F e.1 e.2 := by
    apply (l5_mem_crossEdges F e.1 e.2).mp
    exact hp.mem_iff.mp (List.mem_flatMap.mpr ⟨c, hcm, hem⟩)
  have hcycle (c) (hcm : c ∈ cycles) :
      kappaStar c.length η * ((cycleEdges c).map fun e => (h e.2 - h e.1) ^ 2).sum ≤
        ((cycleEdges c).map fun e => Real.cot (delta θ e) * (h e.2 - h e.1) ^ 2).sum := by
    let es := cycleEdges c
    have hlen : es.length = c.length := by simp [es, cycleEdges]
    have hlen3 : 3 ≤ es.length := by rw [hlen]; exact (hc c hcm).1
    have hh := sharp_cot_cycle es.length hlen3 η hη (by rw [hlen]; exact hηZ c hcm)
      (fun i => delta θ (es.get i)) (fun i => h (es.get i).2 - h (es.get i).1)
      (fun i => hδ _ _ (he c hcm _ (List.get_mem _ i)))
      (by rw [l5_sum_get]; exact delta_cycle_sum_core θ c (hc c hcm).1 (hc c hcm).2.1 (hc c hcm).2.2)
      (by rw [l5_sum_get es (fun e => h e.2 - h e.1)]; exact cycle_difference_sum c h)
    rw [l5_sum_get es (fun e => (h e.2 - h e.1) ^ 2),
      l5_sum_get es (fun e => Real.cot (delta θ e) * (h e.2 - h e.1) ^ 2), hlen] at hh
    exact hh
  have hδπ (e : Fin n × Fin n) (hem : e ∈ crossEdges F) : delta θ e < Real.pi := by
    obtain ⟨c, hcm, hec⟩ := List.mem_flatMap.mp (hp.mem_iff.mpr hem)
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
  rw [extensions_graph_form, hessian_matrix_form_core]
  unfold hessianQ
  constructor
  · rw [← (hp.map (fun e => (h e.2 - h e.1) ^ 2)).sum_eq,
      ← (hp.map (fun e => Real.cot (delta θ e) * (h e.2 - h e.1) ^ 2)).sum_eq,
      l5_sum_flatMap, l5_sum_flatMap, ← List.sum_map_mul_left]
    apply List.sum_le_sum
    intro c hcm
    have hnonneg : 0 ≤ ((cycleEdges c).map fun e => (h e.2 - h e.1) ^ 2).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      exact sq_nonneg _
    exact (mul_le_mul_of_nonneg_right (extensions_kappa_min_le cycles η c hcm) hnonneg).trans
      (hcycle c hcm)
  · rw [← List.sum_map_mul_left]
    apply List.sum_le_sum
    intro e hem
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact extensions_cot_antitone hη (hδ _ _ ((l5_mem_crossEdges F _ _).mp hem)) (hδπ e hem)

end Conj43
