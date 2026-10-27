/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.LipschitzDefs
import Conj43.ExtensionsSandwich

noncomputable section
namespace Conj43
variable {n : ℕ}

lemma extensions_lipschitz_euclid_nonneg (x : Fin n → ℝ) : 0 ≤ euclidNorm x :=
  Real.sqrt_nonneg _

lemma extensions_lipschitz_euclid_sq (x : Fin n → ℝ) :
    euclidNorm x ^ 2 = ∑ i, x i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma extensions_lipschitz_euclid_norm (x : Fin n → ℝ) :
    euclidNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 x))]
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma extensions_lipschitz_inner (x y : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = dotProduct x y := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma extensions_lipschitz_cs (x y : Fin n → ℝ) :
    dotProduct x y ≤ euclidNorm x * euclidNorm y := by
  rw [extensions_lipschitz_euclid_norm, extensions_lipschitz_euclid_norm,
    ← extensions_lipschitz_inner]
  exact real_inner_le_norm _ _

lemma extensions_lipschitz_shift_zero (F : LooplessBAP n) : ComponentShift F 0 := by
  intro p q _
  rfl

lemma extensions_lipschitz_quot_nonempty (F : LooplessBAP n) (x : Fin n → ℝ) :
    ((fun c => euclidNorm (x - c)) '' {c | ComponentShift F c}).Nonempty :=
  ⟨_, ⟨0, extensions_lipschitz_shift_zero F, rfl⟩⟩

lemma extensions_lipschitz_quot_bdd (F : LooplessBAP n) (x : Fin n → ℝ) :
    BddBelow ((fun c => euclidNorm (x - c)) '' {c | ComponentShift F c}) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨c, _, rfl⟩
  exact extensions_lipschitz_euclid_nonneg _

lemma extensions_lipschitz_quot_nonneg (F : LooplessBAP n) (x : Fin n → ℝ) :
    0 ≤ quotNorm F x := by
  apply le_csInf (extensions_lipschitz_quot_nonempty F x)
  rintro _ ⟨c, _, rfl⟩
  exact extensions_lipschitz_euclid_nonneg _

lemma extensions_lipschitz_quot_le (F : LooplessBAP n) (x c : Fin n → ℝ)
    (hc : ComponentShift F c) : quotNorm F x ≤ euclidNorm (x - c) :=
  csInf_le (extensions_lipschitz_quot_bdd F x) ⟨c, hc, rfl⟩

lemma extensions_lipschitz_transpose_shift (F : LooplessBAP n) (c : Fin n → ℝ)
    (hc : ComponentShift F c) : (realB F).transpose.mulVec c = 0 := by
  ext j
  rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose, realB_vecMul]
  exact sub_eq_zero.mpr
    (hc _ _ (Relation.ReflTransGen.single
      (Or.inl ((l5_mem_crossEdges F _ _).mp (List.get_mem _ j))))).symm

lemma extensions_lipschitz_graph_kernel (F : LooplessBAP n) (c : Fin n → ℝ) :
    (graphLaplacian F).mulVec c = 0 ↔ ComponentShift F c := by
  constructor
  · intro hz
    have hq : dotProduct c ((graphLaplacian F).mulVec c) = 0 := by
      rw [hz, dotProduct_zero]
    rw [extensions_graph_form, l5_sum_zero_iff _ _ (fun _ _ => sq_nonneg _)] at hq
    apply (edge_constant_iff_component_constant F c).mp
    intro p q he
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp (hq (p,q) ((l5_mem_crossEdges F p q).mpr he)))).symm
  · intro hc
    unfold graphLaplacian
    rw [← Matrix.mulVec_mulVec, extensions_lipschitz_transpose_shift F c hc, Matrix.mulVec_zero]

lemma extensions_lipschitz_gradient_orthogonal (F : LooplessBAP n)
    (θ c : Fin n → ℝ) (hc : ComponentShift F c) :
    dotProduct (necklaceGradient F θ) c = 0 := by
  rw [dotProduct_comm]
  unfold necklaceGradient
  have ht : Matrix.vecMul c (realB F) = (realB F).transpose.mulVec c := by
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rw [Matrix.dotProduct_mulVec, ht,
    extensions_lipschitz_transpose_shift F c hc, zero_dotProduct]

/-- Cauchy--Schwarz holds on the quotient by taking the infimum over every shift. -/
lemma extensions_lipschitz_quot_cs (F : LooplessBAP n) (θ θ' x : Fin n → ℝ) :
    dotProduct (necklaceGradient F θ - necklaceGradient F θ') x ≤
      euclidNorm (necklaceGradient F θ - necklaceGradient F θ') * quotNorm F x := by
  let g := necklaceGradient F θ - necklaceGradient F θ'
  change dotProduct g x ≤ euclidNorm g * quotNorm F x
  have ho (c : Fin n → ℝ) (hc : ComponentShift F c) : dotProduct g c = 0 := by
    dsimp [g]
    rw [sub_dotProduct, extensions_lipschitz_gradient_orthogonal F θ c hc,
      extensions_lipschitz_gradient_orthogonal F θ' c hc, sub_self]
  have hh (c : Fin n → ℝ) (hc : ComponentShift F c) :
      dotProduct g x ≤ euclidNorm g * euclidNorm (x-c) := by
    have hs := extensions_lipschitz_cs g (x-c)
    rwa [dotProduct_sub, ho c hc, sub_zero] at hs
  by_cases hg : euclidNorm g = 0
  · simpa only [hg, zero_mul] using hh 0 (extensions_lipschitz_shift_zero F)
  · have hgp : 0 < euclidNorm g :=
      lt_of_le_of_ne (extensions_lipschitz_euclid_nonneg g) (Ne.symm hg)
    have hi : dotProduct g x / euclidNorm g ≤ quotNorm F x := by
      apply le_csInf (extensions_lipschitz_quot_nonempty F x)
      rintro _ ⟨c, hc, rfl⟩
      exact (div_le_iff₀ hgp).mpr (by simpa only [mul_comm] using hh c hc)
    exact (div_le_iff₀ hgp).mp hi |>.trans_eq (mul_comm _ _)

end Conj43
