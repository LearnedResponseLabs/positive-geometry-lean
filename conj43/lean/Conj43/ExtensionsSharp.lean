/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.ExtensionsDefs
import Conj43.CotCycle
import Conj43.ExtensionsDiagonal
import Conj43.ExtensionsShiftedCot
import Conj43.ExtensionsSharpSupport

noncomputable section
namespace Conj43

lemma extensions_sum_last (m : ℕ) (hm : 0 < m) (a b : ℝ) :
    (∑ i : Fin m, if (i : ℕ) + 1 = m then b else a) = ((m : ℝ) - 1) * a + b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [Fin.sum_univ_castSucc]
  have he (i : Fin k) : ¬ (i.castSucc : ℕ) + 1 = k + 1 := by
    simp only [Fin.val_castSucc]
    omega
  simp only [he, ↓reduceIte, Fin.val_last]
  simp

theorem sharp_cot_extremizer (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (hη : 0 < η) (hηm : η ≤ Real.pi / m) :
    (∀ i, η ≤ sharpAngles m η i) ∧ ∑ i, sharpAngles m η i = Real.pi ∧ ∑ i, sharpVelocity m i = 0 ∧
      ∑ i, Real.cot (sharpAngles m η i) * sharpVelocity m i ^ 2 =
        kappaStar m η * ∑ i, sharpVelocity m i ^ 2 := by
  have hm0 : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hprod : η * (m : ℝ) ≤ Real.pi := (le_div_iff₀ hmr).mp hηm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    unfold sharpAngles
    split_ifs <;> linarith
  · unfold sharpAngles
    rw [extensions_sum_last m hm0]
    ring
  · unfold sharpVelocity
    rw [extensions_sum_last m hm0]
    ring
  · have hterm (i : Fin m) :
        Real.cot (sharpAngles m η i) * sharpVelocity m i ^ 2 =
          if (i : ℕ) + 1 = m then
            Real.cot (Real.pi - ((m : ℝ) - 1) * η) * (-((m : ℝ) - 1)) ^ 2
          else Real.cot η := by
      unfold sharpAngles sharpVelocity
      split_ifs <;> simp
    have hsq (i : Fin m) : sharpVelocity m i ^ 2 =
        if (i : ℕ) + 1 = m then (-((m : ℝ) - 1)) ^ 2 else 1 := by
      unfold sharpVelocity
      split_ifs <;> simp
    simp_rw [hterm, hsq]
    rw [extensions_sum_last m hm0, extensions_sum_last m hm0, cot_pi_sub]
    unfold kappaStar
    field_simp
    <;> ring

theorem kappaStar_pos (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (hη : 0 < η) (hηm : η ≤ Real.pi / m) :
    0 < kappaStar m η := by
  obtain ⟨ha, hsum, hd, heq⟩ := sharp_cot_extremizer m hm η hη hηm
  have hne : ∃ k, sharpVelocity m k ≠ 0 := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [sharpVelocity, show ¬ 0 + 1 = m by omega]
  have hp := cot_cycle_pos hm (fun i => lt_of_lt_of_le hη (ha i)) hsum hd hne
  rw [heq] at hp
  exact pos_of_mul_pos_left hp (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma extensions_sin_add_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y < Real.pi) : Real.sin (x + y) < Real.sin x + Real.sin y := by
  have hsx := Real.sin_pos_of_pos_of_lt_pi hx (by linarith : x < Real.pi)
  have hsy := Real.sin_pos_of_pos_of_lt_pi hy (by linarith : y < Real.pi)
  have hcy : Real.cos y < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (by rfl : (0 : ℝ) ≤ 0)
      (by linarith : y ≤ Real.pi) hy
  have h1 := mul_lt_mul_of_pos_left hcy hsx
  have h2 := mul_le_mul_of_nonneg_right (Real.cos_le_one x) hsy.le
  rw [Real.sin_add]
  nlinarith

lemma extensions_sin_mul_le (k : ℕ) (x : ℝ) (hx : 0 < x)
    (hbound : (k : ℝ) * x < Real.pi) : Real.sin ((k : ℝ) * x) ≤ k * Real.sin x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hb : (k : ℝ) * x < Real.pi := by
      push_cast at hbound
      nlinarith
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hk hx.le) hb.le
    have hsx := Real.sin_pos_of_pos_of_lt_pi hx (by
      push_cast at hbound
      nlinarith [mul_nonneg hk hx.le] : x < Real.pi)
    have h1 := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hsin
    have h2 := mul_le_mul_of_nonneg_right (Real.cos_le_one ((k : ℝ) * x)) hsx.le
    have hi := ih hb
    push_cast
    rw [add_mul, one_mul, Real.sin_add]
    nlinarith

lemma extensions_sin_mul_lt (k : ℕ) (hk : 2 ≤ k) (x : ℝ) (hx : 0 < x)
    (hbound : (k : ℝ) * x < Real.pi) : Real.sin ((k : ℝ) * x) < k * Real.sin x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hj : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjb : (j : ℝ) * x < Real.pi := by push_cast at hbound; nlinarith
  have h1 := extensions_sin_mul_le j x hx hjb
  have h2 := extensions_sin_add_lt (mul_pos hj hx) hx (by
    push_cast at hbound
    nlinarith : (j : ℝ) * x + x < Real.pi)
  push_cast
  rw [add_mul, one_mul]
  nlinarith

theorem kappaStar_lt_tan (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (hη : 0 < η) (hηm : η < Real.pi / m) :
    kappaStar m η < Real.tan (((m : ℝ) - 2) * η / 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hbound : (m : ℝ) * η < Real.pi := by
    have := (lt_div_iff₀ hm0).mp hηm
    nlinarith
  let r : ℝ := (m : ℝ) - 1
  let u : ℝ := ((m : ℝ) - 2) * η / 2
  let a : ℝ := (m : ℝ) * η / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hb0 : 0 < r * η := mul_pos hr hη
  have hbπ : r * η < Real.pi := by dsimp [r]; nlinarith
  have hηπ : η < Real.pi := by nlinarith
  have hu0 : 0 < u := by dsimp [u]; nlinarith
  have huπ : u < Real.pi / 2 := by dsimp [u]; nlinarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have haπ : a < Real.pi / 2 := by dsimp [a]; linarith
  have hsη := Real.sin_pos_of_pos_of_lt_pi hη hηπ
  have hsb := Real.sin_pos_of_pos_of_lt_pi hb0 hbπ
  have hcu := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], huπ⟩
  have hca := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], haπ⟩
  have hslt : Real.sin (r * η) < r * Real.sin η := by
    have hh := extensions_sin_mul_lt (m - 1) (by omega) η hη
      (by simpa [Nat.cast_sub (by omega : 1 ≤ m), r] using hbπ)
    simpa [Nat.cast_sub (by omega : 1 ≤ m), r] using hh
  have hratio : 1 / Real.sin η < r / Real.sin (r * η) := by
    apply (div_lt_div_iff₀ hsη hsb).mpr
    simpa using hslt
  have hleft : Real.cot η - Real.tan u =
      (Real.cos a / Real.cos u) * (1 / Real.sin η) := by
    have ha : a = η + u := by dsimp [a, u]; ring
    rw [ha, Real.cos_add, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
    field_simp
    <;> ring
  have hright : Real.cot (r * η) + Real.tan u =
      (Real.cos a / Real.cos u) * (1 / Real.sin (r * η)) := by
    have ha : a = r * η - u := by dsimp [a, r, u]; ring
    rw [ha, Real.cos_sub, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
    field_simp
    <;> ring
  have hi : Real.cot η - Real.tan u < r * (Real.cot (r * η) + Real.tan u) := by
    rw [hleft, hright]
    calc
      _ < (Real.cos a / Real.cos u) * (r / Real.sin (r * η)) :=
        mul_lt_mul_of_pos_left hratio (div_pos hca hcu)
      _ = _ := by ring
  change (Real.cot η - r * Real.cot (r * η)) / (m : ℝ) < Real.tan u
  apply (div_lt_iff₀ hm0).mpr
  dsimp only [r] at hi ⊢
  nlinarith

theorem sharp_cot_cycle (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (hη : 0 < η) (hηm : η ≤ Real.pi / m)
    (α d : Fin m → ℝ) (hα : ∀ i, η ≤ α i) (hsum : ∑ i, α i = Real.pi) (hd : ∑ i, d i = 0) :
    kappaStar m η * ∑ i, d i ^ 2 ≤ ∑ i, Real.cot (α i) * d i ^ 2 := by
  classical
  have hm0 : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hend : η = Real.pi / m
  · have hs : ∑ i, (α i - η) = 0 := by
      rw [Finset.sum_sub_distrib, hsum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hend]
      field_simp
      ring
    have he (i : Fin m) : α i = η := by
      have hh := Finset.single_le_sum (s := Finset.univ)
        (f := fun j => α j - η) (fun j _ => sub_nonneg.mpr (hα j)) (Finset.mem_univ i)
      rw [hs] at hh
      linarith [hα i]
    simp_rw [he]
    rw [hend, extensions_kappa_endpoint m hm0, Finset.mul_sum]
  have hstrict : η < Real.pi / m := lt_of_le_of_ne hηm hend
  have hmη : (m : ℝ) * η < Real.pi := by
    have hh := (lt_div_iff₀ hmr).mp hstrict
    nlinarith
  let c := kappaStar m η
  let φ := Real.arctan c
  have hc : 0 < c := kappaStar_pos m hm η hη hηm
  have hφ : 0 < φ := Real.arctan_pos.mpr hc
  have hφπ : φ < Real.pi / 2 := Real.arctan_lt_pi_div_two c
  have htanφ : Real.tan φ = c := Real.tan_arctan c
  have hcosφ : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφπ⟩
  have hlocal : 2 * φ < ((m : ℝ) - 2) * η := by
    have hu0 : 0 < ((m : ℝ) - 2) * η / 2 := by nlinarith
    have huπ : ((m : ℝ) - 2) * η / 2 < Real.pi / 2 := by nlinarith
    have hh := Real.arctan_strictMono (kappaStar_lt_tan m hm η hη hstrict)
    rw [Real.arctan_tan (by linarith [Real.pi_pos]) huπ] at hh
    change φ < _ at hh
    linarith
  have hupper (i : Fin m) := extensions_angle_upper m η α hα hsum i
  have hapos (i : Fin m) : 0 < α i := lt_of_lt_of_le hη (hα i)
  have hapi (i : Fin m) : α i < Real.pi := by nlinarith only [hupper i, hm3, hη]
  have hsin (i : Fin m) : 0 < Real.sin (α i) :=
    Real.sin_pos_of_pos_of_lt_pi (hapos i) (hapi i)
  have hrepr (i : Fin m) : Real.cot (α i) - c =
      Real.cos (α i + φ) / (Real.sin (α i) * Real.cos φ) := by
    rw [← htanφ]
    exact extensions_cot_shift (α i) φ (hsin i).ne' hcosφ.ne'
  have hshifted : 0 ≤ ∑ i, (Real.cot (α i) - c) * d i ^ 2 := by
    by_cases hall : ∀ i, 0 ≤ Real.cot (α i) - c
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hall i) (sq_nonneg _))
    push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hbig : Real.pi / 2 < α j + φ := by
      by_contra hh
      have hcos : 0 ≤ Real.cos (α j + φ) := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hapos j, Real.pi_pos], by linarith⟩
      have hn : 0 ≤ Real.cot (α j) - c := by
        rw [hrepr]
        exact div_nonneg hcos (mul_pos (hsin j) hcosφ).le
      linarith
    have hjcos : Real.cos (α j + φ) < 0 := by
      have hh := mul_neg_of_neg_of_pos hj (mul_pos (hsin j) hcosφ)
      rw [hrepr, div_mul_cancel₀ _ (mul_pos (hsin j) hcosφ).ne'] at hh
      exact hh
    have hacute (i : Fin m) (hij : i ≠ j) : α i + φ < Real.pi / 2 := by
      have hh := extensions_angle_pair m η α hα hsum i j hij
      linarith
    have hother (i : Fin m) (hij : i ≠ j) : 0 < Real.cot (α i) - c := by
      rw [hrepr]
      exact div_pos (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hapos i, Real.pi_pos], hacute i hij⟩) (mul_pos (hsin i) hcosφ)
    let s : Finset (Fin m) := Finset.univ.erase j
    have hcard : s.card = m - 1 := by simp [s]
    have hcardR : (s.card : ℝ) = (m : ℝ) - 1 := by
      rw [hcard, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hS : α j + ∑ i ∈ s, α i = Real.pi := by
      simpa only [hsum] using Finset.add_sum_erase Finset.univ α (Finset.mem_univ j)
    have hSlo : ((m : ℝ) - 1) * η ≤ ∑ i ∈ s, α i := by
      simpa only [Finset.sum_const, nsmul_eq_mul, hcardR] using
        Finset.sum_le_sum (fun i (_ : i ∈ s) => hα i)
    have hSacute : (∑ i ∈ s, α i) - φ < Real.pi / 2 := by linarith
    have hpath := extensions_reciprocal_path s α η φ hη hφ (by rw [hcard]; omega)
      (by rw [hcardR]; linarith) (fun i _ => hα i)
      (fun i hi => hacute i (Finset.mem_erase.mp hi).1) hSacute
    rw [hcardR] at hpath
    have hzeroSmall : 0 < η + φ ∧ η + φ < Real.pi / 2 := by
      constructor <;> nlinarith only [hη, hφ, hlocal, hmη]
    have hzeroS : 0 < ((m : ℝ) - 1) * η - φ ∧
        ((m : ℝ) - 1) * η - φ < Real.pi / 2 := by
      constructor <;> nlinarith only [hSlo, hSacute, hlocal, hm3, hη, hφ]
    let A := Real.pi - ((m : ℝ) - 1) * η
    have hApos : 0 < A := by dsimp [A]; nlinarith only [hmη, hη]
    have hApi : A < Real.pi := by dsimp [A]; nlinarith only [hm3, hη]
    have hsinA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi hApos hApi
    have hsinη : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη
      (by nlinarith only [hmη, hm3, hη])
    have hcosη : 0 < Real.cos (η + φ) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hzeroSmall.1], hzeroSmall.2⟩
    have hAeq : A + φ = Real.pi - (((m : ℝ) - 1) * η - φ) := by dsimp [A]; ring
    have hcosA : Real.cos (A + φ) < 0 := by
      rw [hAeq, Real.cos_pi_sub]
      have hh := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hzeroS.1], hzeroS.2⟩
      linarith
    have hcoefη : Real.cot η - c ≠ 0 := by
      rw [← htanφ, extensions_cot_shift η φ hsinη.ne' hcosφ.ne']
      exact (div_pos hcosη (mul_pos hsinη hcosφ)).ne'
    have hcoefA : Real.cot A - c ≠ 0 := by
      rw [← htanφ, extensions_cot_shift A φ hsinA.ne' hcosφ.ne']
      exact div_ne_zero hcosA.ne (mul_ne_zero hsinA.ne' hcosφ.ne')
    have hboundary := extensions_boundary_reciprocal m hm0 η hcoefη hcoefA
    have hinv (i : Fin m) : (Real.cot (α i) - c)⁻¹ =
        (Real.tan (α i + φ) - c) * Real.cos φ ^ 2 := by
      have hcos : Real.cos (α i + φ) ≠ 0 := by
        by_cases hij : i = j
        · subst i; exact hjcos.ne
        · exact (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hapos i, Real.pi_pos], hacute i hij⟩).ne'
      simpa only [htanφ] using extensions_cot_shift_inv (α i) φ (hsin i).ne' hcosφ.ne' hcos
    have hinvη : (Real.cot η - c)⁻¹ =
        (Real.tan (η + φ) - c) * Real.cos φ ^ 2 := by
      simpa only [htanφ] using extensions_cot_shift_inv η φ hsinη.ne' hcosφ.ne' hcosη.ne'
    have hinvA : (Real.cot A - c)⁻¹ =
        (-Real.tan (((m : ℝ) - 1) * η - φ) - c) * Real.cos φ ^ 2 := by
      have hh := extensions_cot_shift_inv A φ hsinA.ne' hcosφ.ne' hcosA.ne
      rw [hAeq, Real.tan_pi_sub, htanφ] at hh
      exact hh
    change ((m : ℝ) - 1) * (Real.cot η - c)⁻¹ + (Real.cot A - c)⁻¹ = 0 at hboundary
    rw [hinvη, hinvA] at hboundary
    have hjtan : Real.tan (α j + φ) = -Real.tan ((∑ i ∈ s, α i) - φ) := by
      rw [show α j + φ = Real.pi - ((∑ i ∈ s, α i) - φ) by linarith, Real.tan_pi_sub]
    have hrec : ∑ i, (Real.cot (α i) - c)⁻¹ ≤ 0 := by
      rw [← Finset.add_sum_erase Finset.univ (fun i => (Real.cot (α i) - c)⁻¹) (Finset.mem_univ j)]
      change (Real.cot (α j) - c)⁻¹ + ∑ i ∈ s, (Real.cot (α i) - c)⁻¹ ≤ 0
      simp_rw [hinv]
      rw [hjtan, ← Finset.sum_mul, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, hcardR]
      have hh := mul_le_mul_of_nonneg_right hpath (sq_nonneg (Real.cos φ))
      nlinarith only [hh, hboundary]
    exact extensions_diagonal_psd (fun i => Real.cot (α i) - c) d j
      (by simp; omega) hj hother hd hrec
  have he : (∑ i, (Real.cot (α i) - c) * d i ^ 2) =
      (∑ i, Real.cot (α i) * d i ^ 2) - c * ∑ i, d i ^ 2 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [he] at hshifted
  exact sub_nonneg.mp hshifted

end Conj43
