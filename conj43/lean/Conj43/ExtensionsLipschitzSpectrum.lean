/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsLipschitzQuotient

noncomputable section
namespace Conj43
variable {n : ℕ}

lemma extensions_lipschitz_graph_psd (F : LooplessBAP n) :
    (graphLaplacian F).PosSemidef := by
  simpa only [graphLaplacian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (realB F)

/-- In an orthonormal eigenbasis, the matrix acts diagonally. -/
lemma extensions_lipschitz_repr_mul (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    hA.eigenvectorBasis.repr (Matrix.toEuclideanLin A x) i =
      hA.eigenvalues i * hA.eigenvectorBasis.repr x i := by
  let b := hA.eigenvectorBasis
  have he (j : Fin n) :
      Matrix.toEuclideanLin A (b j) = hA.eigenvalues j • b j := by
    apply WithLp.ofLp_injective
    exact hA.mulVec_eigenvectorBasis j
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, he]
  simp [b, smul_smul, Pi.single_apply, mul_comm]

/-- The zero-eigenvalue coordinates give a kernel representative; every remaining
eigenvalue is at least the least positive spectral value. -/
lemma extensions_lipschitz_spectral_representative
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (lam : ℝ) (hlam : IsLeast {μ : ℝ | μ ∈ spectrum ℝ A ∧ 0 < μ} lam)
    (x : Fin n → ℝ) :
    ∃ c : Fin n → ℝ, A.mulVec c = 0 ∧
      lam * euclidNorm (x-c) ^ 2 ≤ dotProduct x (A.mulVec x) := by
  classical
  let b := hA.1.eigenvectorBasis
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let a := b.repr v
  let z : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i => if hA.1.eigenvalues i = 0 then a i else 0)
  let c : EuclideanSpace ℝ (Fin n) := b.repr.symm z
  have hc : Matrix.toEuclideanLin A c = 0 := by
    apply b.repr.injective
    rw [map_zero]
    ext i
    rw [extensions_lipschitz_repr_mul]
    change hA.1.eigenvalues i * (b.repr (b.repr.symm z)) i = 0
    rw [b.repr.apply_symm_apply]
    dsimp [z]
    split_ifs with hi <;> simp [hi]
  have henergy : dotProduct x (A.mulVec x) = ∑ i, hA.1.eigenvalues i * (a i)^2 := by
    rw [← extensions_lipschitz_inner]
    change inner ℝ v (Matrix.toEuclideanLin A v) = _
    rw [← b.repr.inner_map_map]
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [extensions_lipschitz_repr_mul]
    simp [b, a, pow_two, mul_comm, mul_assoc]
  have hnorm : euclidNorm (x - WithLp.ofLp c) ^ 2 =
      ∑ i, (a i - z i)^2 := by
    rw [extensions_lipschitz_euclid_norm]
    change ‖v-c‖ ^ 2 = _
    rw [← b.repr.norm_map, map_sub]
    change ‖a - b.repr (b.repr.symm z)‖ ^ 2 = _
    rw [b.repr.apply_symm_apply, EuclideanSpace.real_norm_sq_eq]
    rfl
  refine ⟨WithLp.ofLp c, ?_, ?_⟩
  · exact congrArg WithLp.ofLp hc
  · rw [hnorm, henergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : hA.1.eigenvalues i = 0
    · simp [z, hi]
    · have hpos : 0 < hA.1.eigenvalues i :=
        lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hi)
      have hle := hlam.2 ⟨hA.1.eigenvalues_mem_spectrum_real i, hpos⟩
      simpa [z, hi] using mul_le_mul_of_nonneg_right hle (sq_nonneg (a i))

lemma extensions_lipschitz_spectral_gap (F : LooplessBAP n) (lam : ℝ)
    (hlam : IsLeast {μ : ℝ | μ ∈ spectrum ℝ (graphLaplacian F) ∧ 0 < μ} lam)
    (x : Fin n → ℝ) :
    lam * quotNorm F x ^ 2 ≤ dotProduct x ((graphLaplacian F).mulVec x) := by
  obtain ⟨c, hc, hbound⟩ := extensions_lipschitz_spectral_representative
    (graphLaplacian F) (extensions_lipschitz_graph_psd F) lam hlam x
  have hq := extensions_lipschitz_quot_le F x c ((extensions_lipschitz_graph_kernel F c).mp hc)
  have hq0 := extensions_lipschitz_quot_nonneg F x
  have hn0 := extensions_lipschitz_euclid_nonneg (x-c)
  have hsq : quotNorm F x ^ 2 ≤ euclidNorm (x-c) ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hsq hlam.1.2.le).trans hbound

end Conj43
