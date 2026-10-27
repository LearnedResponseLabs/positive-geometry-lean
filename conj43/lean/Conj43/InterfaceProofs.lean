/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceDefs
namespace Conj43

def residue {n : ℕ} (hn : 0 < n) (i : ℤ) : Fin n :=
  ⟨(i % (n : ℤ)).toNat, by
    have := Int.emod_nonneg i (by omega : (n : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos i (by omega : (0 : ℤ) < n)
    omega⟩

theorem residue_val {n : ℕ} (hn : 0 < n) (i : ℤ) :
    ((residue hn i : Fin n) : ℤ) = i % (n : ℤ) := by
  simp only [residue, Fin.val_mk]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

theorem residue_fin {n : ℕ} (hn : 0 < n) (i : Fin n) :
    residue hn (i : ℤ) = i := by
  apply Fin.ext
  simp [residue, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ i) (by exact_mod_cast i.isLt : (i : ℤ) < (n : ℤ))]

private theorem f_formula {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (i : ℤ) :
    F.f i = i + 1 + (((F.σ (residue hn i) : ℕ) : ℤ) - i - 1) % n := by
  simp [LooplessBAP.f, hn, residue]

 theorem f_bounds {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (i : ℤ) :
    i < F.f i ∧ F.f i ≤ i + n := by
  rw [f_formula hn]
  have := Int.emod_nonneg (((F.σ (residue hn i) : ℕ) : ℤ) - i - 1) (by omega : (n : ℤ) ≠ 0)
  have := Int.emod_lt_of_pos (((F.σ (residue hn i) : ℕ) : ℤ) - i - 1) (by omega : (0 : ℤ) < n)
  omega

theorem f_mod {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (i : ℤ) :
    F.f i % (n : ℤ) = (F.σ (residue hn i) : ℕ) := by
  rw [f_formula hn]
  have h : (0 : ℤ) ≤ (F.σ (residue hn i) : ℕ) := by omega
  have h' : ((F.σ (residue hn i) : ℕ) : ℤ) < n := by exact_mod_cast (F.σ (residue hn i)).isLt
  calc
    _ = (i + 1 + (((F.σ (residue hn i) : ℕ) : ℤ) - i - 1)) % n := by
      simp only [Int.add_emod, Int.emod_emod]
    _ = (((F.σ (residue hn i) : ℕ) : ℤ)) % n := by congr 1; omega
    _ = _ := Int.emod_eq_of_lt h h'

 theorem galashin_residues {n : ℕ} (hn : 0 < n) (F : LooplessBAP n)
    (p : ℤ) (hp : 1 ≤ p) (hpn : p ≤ n) :
    Int.ModEq (n : ℤ) (galashinOf F p)
      ((F.σ ⟨(p - 1).toNat, by omega⟩ : ℕ) + 1) := by
  have hr : residue hn (p - 1) = (⟨(p - 1).toNat, by omega⟩ : Fin n) := by
    apply Fin.ext
    simp [residue, Int.emod_eq_of_lt (by omega : 0 ≤ p-1) (by omega : p-1 < (n : ℤ))]
  have hm := f_mod hn F (p-1)
  rw [hr] at hm
  have he : Int.ModEq (n : ℤ) (F.f (p-1)) ((F.σ ⟨(p-1).toNat, by omega⟩ : ℕ) : ℤ) := by
    change _ = _ % _
    rw [hm, Int.emod_eq_of_lt (by omega) (by exact_mod_cast (F.σ ⟨(p-1).toNat, by omega⟩).isLt)]
  exact he.add_right 1

 theorem galashin_no_loops {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p : ℤ) :
    galashinOf F p ≠ p := by
  have := f_bounds hn F (p-1)
  unfold galashinOf
  omega

theorem interval_unique {n a b l : ℤ} (ha : l < a ∧ a ≤ l+n)
    (hb : l < b ∧ b ≤ l+n) (h : Int.ModEq n a b) : a = b := by
  have hh := h.sub_right (l+1)
  change (a-(l+1)) % n = (b-(l+1)) % n at hh
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hh
  omega

 theorem galashin_coloop {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p : Fin n) :
    F.σ p = p ↔ galashinOf F ((p : ℤ) + 1) = ((p : ℤ) + 1) + n := by
  have hm := f_mod hn F (p : ℤ)
  rw [residue_fin hn] at hm
  have hb := f_bounds hn F (p : ℤ)
  simp only [galashinOf, add_sub_cancel_right]
  constructor
  · intro h
    rw [h] at hm
    have he : Int.ModEq (n : ℤ) (F.f (p : ℤ)) ((p : ℤ)+n) := by
      change _ = _ % _
      simpa only [Int.add_emod_right, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ p) (by exact_mod_cast p.isLt : (p : ℤ) < (n : ℤ))] using hm
    have := interval_unique hb (show (p : ℤ) < (p : ℤ)+(n : ℤ) ∧ (p : ℤ)+(n : ℤ) ≤ (p : ℤ)+(n : ℤ) by omega) he
    omega
  · intro h
    have he : F.f (p : ℤ) = (p : ℤ)+n := by omega
    rw [he] at hm
    simp only [Int.add_emod_right] at hm
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast p.isLt)] at hm
    apply Fin.ext
    exact_mod_cast hm.symm

 theorem galashin_injective {n : ℕ} (hn : 0 < n) (F G : LooplessBAP n) :
    galashinOf F = galashinOf G → F = G := by
  intro h
  have hs : F.σ = G.σ := by
    apply Equiv.ext
    intro i
    have hf := congrFun h ((i : ℤ)+1)
    simp only [galashinOf, add_sub_cancel_right] at hf
    have hF := f_mod hn F (i : ℤ)
    have hG := f_mod hn G (i : ℤ)
    rw [residue_fin hn] at hF hG
    have he : F.f (i : ℤ) = G.f (i : ℤ) := by omega
    rw [he, hG] at hF
    apply Fin.ext
    exact_mod_cast hF.symm
  cases F; cases G; cases hs; rfl

 theorem galashin_rank_range {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) :
    1 ≤ rank F ∧ rank F ≤ n := by
  classical
  constructor
  · have hi : F.σ ⟨n-1, by omega⟩ ≤ (⟨n-1, by omega⟩ : Fin n) := by
      have := (F.σ ⟨n-1, by omega⟩).isLt
      change (F.σ ⟨n-1, by omega⟩).val ≤ n-1
      omega
    exact Finset.card_pos.mpr ⟨⟨n-1, by omega⟩, by simp [hi]⟩
  · exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem f_window {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (i : Fin n) :
    F.f (i : ℤ) = (F.σ i : ℤ) + if F.σ i ≤ i then (n : ℤ) else 0 := by
  have hm := f_mod hn F (i : ℤ)
  rw [residue_fin hn] at hm
  apply interval_unique (f_bounds hn F (i : ℤ))
  · have hi := i.isLt
    have hs := (F.σ i).isLt
    split_ifs <;> simp only [Fin.le_def] at * <;> omega
  · change _ = _ % _
    split_ifs <;> simp only [Int.add_emod_right, add_zero]
    all_goals rw [hm, Int.emod_eq_of_lt (by omega) (by exact_mod_cast (F.σ i).isLt)]

theorem f_translate {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (i k : ℤ) :
    F.f (i + k*n) = F.f i + k*n := by
  have hr : residue hn (i+k*n) = residue hn i := by
    apply Fin.ext
    simp [residue, Int.add_mul_emod_self_right]
  rw [f_formula hn, f_formula hn, hr]
  have he : (((F.σ (residue hn i) : ℕ) : ℤ) - (i+k*n) - 1) % n =
      (((F.σ (residue hn i) : ℕ) : ℤ) - i - 1) % n := by
    have hh : (((F.σ (residue hn i) : ℕ) : ℤ) - (i+k*n) - 1) =
        (((F.σ (residue hn i) : ℕ) : ℤ) - i - 1) - k*n := by ring
    rw [hh]
    simp
  rw [he]
  ring

theorem f_bijective {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) :
    Function.Bijective F.f := by
  constructor
  · intro x y h
    have hm : F.σ (residue hn x) = F.σ (residue hn y) := by
      apply Fin.ext
      have hx := f_mod hn F x
      have hy := f_mod hn F y
      rw [h, hy] at hx
      exact_mod_cast hx.symm
    have hr := F.σ.injective hm
    have hv := congrArg (fun a : Fin n => (a : ℤ)) hr
    simp only [residue_val] at hv
    have he : (((F.σ (residue hn y) : ℕ) : ℤ)-x-1) % n =
        (((F.σ (residue hn y) : ℕ) : ℤ)-y-1) % n := by
      exact ((Int.ModEq.refl (((F.σ (residue hn y) : ℕ) : ℤ))).sub hv).sub_right 1
    rw [f_formula hn, f_formula hn, hr, he] at h
    omega
  · intro z
    let i : Fin n := F.σ.symm (residue hn z)
    have hm : Int.ModEq (n : ℤ) (F.f (i : ℤ)) z := by
      change _ = _
      rw [f_mod hn, residue_fin hn]
      simp only [i, Equiv.apply_symm_apply, residue_val]
    obtain ⟨k,hk⟩ := Int.modEq_iff_add_fac.mp hm
    refine ⟨(i : ℤ)+k*n, ?_⟩
    rw [f_translate hn]
    nlinarith [hk]

theorem galashin_sum {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), (galashinOf F j - j)) = (rank F : ℤ)*n := by
  classical
  have hw : (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), (galashinOf F j - j)) =
      ∑ i : Fin n, (F.f (i : ℤ) - (i : ℤ)) := by
    symm
    apply Finset.sum_bij (fun (i : Fin n) _ => (i : ℤ)+1)
    · intro i hi
      simp only [Finset.mem_Icc]
      have := i.isLt
      omega
    · intro i hi j hj h
      apply Fin.ext
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      refine ⟨⟨(j-1).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
      change ((j-1).toNat : ℤ)+1=j
      omega
    · intro i hi
      simp [galashinOf]
  rw [hw]
  simp_rw [f_window hn]
  have hs : (∑ i : Fin n, (F.σ i : ℤ)) = ∑ i : Fin n, (i : ℤ) :=
    Equiv.sum_comp F.σ (fun i : Fin n => (i : ℤ))
  have hc : (∑ i : Fin n, if F.σ i ≤ i then (n : ℤ) else 0) = (rank F : ℤ)*n := by
    rw [← Finset.sum_filter]
    simp [rank]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hs, hc]
  ring

 theorem galashin_isLooplessBAP {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) :
    IsLooplessBAP (rank F) n (galashinOf F) := by
  refine ⟨⟨?_, ?_, galashin_sum hn F, ?_⟩, ?_⟩
  · constructor
    · intro x y h
      have he : F.f (x-1) = F.f (y-1) := by simpa only [galashinOf, add_left_inj] using h
      have := (f_bijective hn F).1 he
      omega
    · intro z
      obtain ⟨x,hx⟩ := (f_bijective hn F).2 (z-1)
      refine ⟨x+1, ?_⟩
      simp [galashinOf, hx]
  · intro j
    have h := f_translate hn F (j-1) 1
    simp only [one_mul] at h
    unfold galashinOf
    rw [show j+(n : ℤ)-1 = j-1+n by ring, h]
    ring
  · intro j
    have := f_bounds hn F (j-1)
    dsimp [galashinOf]
    omega
  · intro j
    have := f_bounds hn F (j-1)
    dsimp [galashinOf]
    omega

private theorem periodic_translate {n : ℕ} {g : ℤ → ℤ}
    (h : ∀ j, g (j+n) = g j+n) (j k : ℤ) : g (j+k*n) = g j+k*n := by
  have hp : Function.Periodic (fun j => g j-j) (n : ℤ) := by
    intro x
    dsimp
    rw [h]
    ring
  have := hp.int_mul k j
  dsimp at this
  omega

 theorem galashin_surjective {k n : ℕ} (hn : 0 < n) (g : ℤ → ℤ)
    (hg : IsLooplessBAP k n g) :
    ∃ F : LooplessBAP n, galashinOf F = g ∧ rank F = k := by
  classical
  let σ₀ : Fin n → Fin n := fun i => residue hn (g ((i : ℤ)+1)-1)
  have hinj : Function.Injective σ₀ := by
    intro i j h
    have he := congrArg (fun a : Fin n => (a : ℤ)) h
    simp only [σ₀, residue_val] at he
    obtain ⟨t,ht⟩ := Int.modEq_iff_add_fac.mp he
    have htrans := periodic_translate hg.1.2.1 ((i : ℤ)+1) t
    have harg : g ((j : ℤ)+1) = g ((i : ℤ)+1+t*n) := by nlinarith [ht]
    have hx := hg.1.1.1 harg
    have hmod := congrArg (fun x : ℤ => (x-1) % (n : ℤ)) hx
    have hh : (↑↑i+1+t*(n : ℤ)-1) = (i : ℤ)+t*n := by ring
    rw [add_sub_cancel_right, hh, Int.add_mul_emod_self_right] at hmod
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt),
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)] at hmod
    apply Fin.ext
    exact_mod_cast hmod.symm
  let F : LooplessBAP n := ⟨Equiv.ofBijective σ₀ ((Finite.injective_iff_bijective).mp hinj)⟩
  have heq : galashinOf F = g := by
    funext p
    have hp := f_bounds hn F (p-1)
    have hg' := hg.1.2.2.2 p
    have hg'' := hg.2 p
    apply interval_unique (l := p) (n := n)
    · dsimp [galashinOf]; omega
    · omega
    · have hm := f_mod hn F (p-1)
      change F.f (p-1) % (n : ℤ) = (σ₀ (residue hn (p-1)) : ℤ) at hm
      rw [residue_val] at hm
      have hi : ((residue hn (p-1) : Fin n) : ℤ)+1+(p-1)/(n : ℤ)*n = p := by
        rw [residue_val]
        have := Int.emod_add_mul_ediv (p-1) (n : ℤ)
        nlinarith
      have ht := periodic_translate hg.1.2.1 (((residue hn (p-1) : Fin n) : ℤ)+1) ((p-1)/(n : ℤ))
      rw [hi] at ht
      have hm' : Int.ModEq (n : ℤ) (g (((residue hn (p-1) : Fin n) : ℤ)+1)-1) (g p-1) := by
        rw [ht]
        change _ % _ = _ % _
        have hh : g (((residue hn (p-1) : Fin n) : ℤ)+1)+(p-1)/(n : ℤ)*n-1 =
          (g (((residue hn (p-1) : Fin n) : ℤ)+1)-1)+(p-1)/(n : ℤ)*n := by ring
        rw [hh, Int.add_mul_emod_self_right]
      have hres : Int.ModEq (n : ℤ) (F.f (p-1)) (g p-1) := hm.trans hm'
      simpa [galashinOf] using hres.add_right 1
  refine ⟨F, heq, ?_⟩
  have hs := galashin_sum hn F
  rw [heq, hg.1.2.2.1] at hs
  have : (rank F : ℤ) = k := by nlinarith
  exact_mod_cast this

private def rowCondition {n : ℕ} (F : LooplessBAP n) (r : ℕ) (x : Fin n) : Prop :=
  if F.σ.symm x < x then (F.σ.symm x : ℕ) < r ∧ r ≤ (x : ℕ)
  else (F.σ.symm x : ℕ) < r ∨ r ≤ (x : ℕ)

private theorem necklaceAux_mem {n : ℕ} (F : LooplessBAP n) (r : ℕ) (hr : r ≤ n)
    (x : Fin n) : x ∈ necklaceAux F r ↔ rowCondition F r x := by
  classical
  induction r generalizing x with
  | zero =>
    simp only [necklaceAux, necklaceFirst, Finset.mem_filter, Finset.mem_univ, true_and,
      rowCondition, Fin.lt_def]
    change (x : ℕ) ≤ (F.σ.symm x : ℕ) ↔ _
    split_ifs <;> omega
  | succ r ih =>
    have hri : r < n := by omega
    have hi := ih (by omega) x
    have hl : (⟨r,hri⟩ : Fin n) ∈ necklaceAux F r := by
      rw [ih (by omega) ⟨r,hri⟩]
      dsimp [rowCondition]
      split_ifs <;> simp only [Fin.lt_def] at * <;> omega
    simp only [necklaceAux, dif_pos hri, if_pos hl, Finset.mem_insert,
      Finset.mem_erase, hi]
    have hs : x = F.σ ⟨r,hri⟩ ↔ F.σ.symm x = ⟨r,hri⟩ := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [← h]; simp
    rw [hs]
    simp only [rowCondition, Fin.lt_def, ne_eq, Fin.ext_iff]
    split_ifs <;> omega

def inverseLift {n : ℕ} (F : LooplessBAP n) (x : Fin n) : ℤ :=
  (F.σ.symm x : ℤ) - if x ≤ F.σ.symm x then (n : ℤ) else 0

theorem f_inverseLift {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (x : Fin n) :
    F.f (inverseLift F x) = (x : ℤ) := by
  have hw := f_window hn F (F.σ.symm x)
  simp only [Equiv.apply_symm_apply] at hw
  unfold inverseLift
  by_cases hx : x ≤ F.σ.symm x
  · rw [if_pos hx]
    have ht := f_translate hn F (F.σ.symm x : ℤ) (-1)
    simp only [neg_one_mul, ← sub_eq_add_neg] at ht
    rw [ht, hw, if_pos hx]
    omega
  · rw [if_neg hx, sub_zero, hw, if_neg hx, add_zero]

private theorem rowCondition_affine {n : ℕ} (hn : 0 < n) (F : LooplessBAP n)
    (r x : Fin n) : rowCondition F r x ↔
      ∃ a : ℤ, a < (r : ℤ) ∧ (r : ℤ) ≤ F.f a ∧ F.f a % n = (x : ℤ) := by
  have hb := f_inverseLift hn F x
  have ht := f_translate hn F (inverseLift F x) 1
  simp only [one_mul, hb] at ht
  have hx := x.isLt
  have hr := r.isLt
  have hs := (F.σ.symm x).isLt
  constructor
  · intro h
    by_cases hxr : (r : ℕ) ≤ x
    · refine ⟨inverseLift F x, ?_, ?_, ?_⟩
      · dsimp [rowCondition] at h
        dsimp [inverseLift]
        split_ifs at * <;> simp only [Fin.le_def, Fin.lt_def] at * <;> omega
      · rw [hb]; exact_mod_cast hxr
      · rw [hb]; exact Int.emod_eq_of_lt (by omega) (by omega)
    · refine ⟨inverseLift F x+n, ?_, ?_, ?_⟩
      · dsimp [rowCondition] at h
        dsimp [inverseLift]
        split_ifs at * <;> simp only [Fin.le_def, Fin.lt_def] at * <;> omega
      · rw [ht]; omega
      · rw [ht, Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
  · rintro ⟨a,ha,har,hm⟩
    have hab := f_bounds hn F a
    have hcases : F.f a = (x : ℤ) ∨ F.f a = (x : ℤ)+n := by
      by_cases hlt : F.f a < n
      · left
        rwa [Int.emod_eq_of_lt (by omega) hlt] at hm
      · right
        have hm' : (F.f a-(n : ℤ)) % n = (x : ℤ) := by simpa using hm
        rw [Int.emod_eq_of_lt (by omega) (by omega)] at hm'
        omega
    rcases hcases with he | he
    · have ha' := (f_bijective hn F).1 (he.trans hb.symm)
      rw [ha'] at ha
      dsimp [rowCondition, inverseLift] at *
      split_ifs at * <;> simp only [Fin.le_def, Fin.lt_def] at * <;> omega
    · have ha' := (f_bijective hn F).1 (he.trans ht.symm)
      rw [ha'] at ha
      dsimp [rowCondition, inverseLift] at *
      split_ifs at * <;> simp only [Fin.le_def, Fin.lt_def] at * <;> omega

 theorem galashin_necklace {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (r : Fin n) :
    necklace F r = galashinNecklace (galashinOf F) ((r : ℤ) + 1) := by
  classical
  ext x
  rw [necklace, necklaceAux_mem F r (Nat.le_of_lt r.isLt), rowCondition_affine hn]
  simp only [galashinNecklace, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a,ha,hr,hm⟩
    refine ⟨a+1, by omega, ?_, ?_⟩
    · simpa [galashinOf] using hr
    · simpa [galashinOf] using hm.symm
  · rintro ⟨p,hp,hr,hm⟩
    refine ⟨p-1, by omega, ?_, ?_⟩
    · dsimp [galashinOf] at hr; omega
    · simpa [galashinOf] using hm.symm
end Conj43
