/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsLipschitzSpectrum

noncomputable section
namespace Conj43
variable {n : ℕ}

lemma extensions_lipschitz_cycles_nonempty (F : LooplessBAP n)
    (cycles : List (List (Fin n)))
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F))
    (lam : ℝ) (hlam : IsLeast {μ : ℝ | μ ∈ spectrum ℝ (graphLaplacian F) ∧ 0 < μ} lam) :
    cycles ≠ [] := by
  intro hz
  have he : crossEdges F = [] := by simpa [hz] using hp.symm
  have hL : graphLaplacian F = 0 := by
    have hempty : IsEmpty (EdgeIdx F) := by
      change IsEmpty (Fin (crossEdges F).length)
      rw [he, List.length_nil]
      infer_instance
    letI := hempty
    ext p q
    simp [graphLaplacian, Matrix.mul_apply]
  have hH := (extensions_lipschitz_graph_psd F).1
  have hzero := hH.eigenvalues_eq_zero_iff.mpr hL
  have hs := hlam.1.1
  rw [hH.spectrum_real_eq_range_eigenvalues] at hs
  obtain ⟨i, hi⟩ := hs
  have hi0 := congrFun hzero i
  have : lam = 0 := hi.symm.trans hi0
  exact (ne_of_gt hlam.1.2) this

lemma extensions_lipschitz_kappa_pos (F : LooplessBAP n)
    (cycles : List (List (Fin n)))
    (hc : ∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n)
    (hp : (cycles.flatMap cycleEdges).Perm (crossEdges F))
    (η : ℝ) (hη : 0 < η) (hηZ : ∀ c ∈ cycles, η ≤ Real.pi / c.length)
    (lam : ℝ) (hlam : IsLeast {μ : ℝ | μ ∈ spectrum ℝ (graphLaplacian F) ∧ 0 < μ} lam) :
    0 < kappaStarZ cycles η := by
  have hn := extensions_lipschitz_cycles_nonempty F cycles hp lam hlam
  cases he : (cycles.map fun c => kappaStar c.length η).min? with
  | none =>
    have hz := List.min?_eq_none_iff.mp he
    have : cycles = [] := List.map_eq_nil_iff.mp hz
    exact (hn this).elim
  | some a =>
    have hm := (List.min?_eq_some_iff.mp he).1
    obtain ⟨c, hcm, hca⟩ := List.mem_map.mp hm
    simpa [kappaStarZ, he, ← hca] using kappaStar_pos c.length (hc c hcm).1 η hη (hηZ c hcm)

end Conj43
