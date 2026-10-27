/- Apache-2.0. Item 6 (stretch): bounded affine permutations (Knutson–Lam–Speyer;
   Galashin, arXiv:2102.13339, §2.1) are in bijection with decorated permutations:
   `π(i) ≡ f(i) mod n`, `f(i) = i + n` is a white and `f(i) = i` a black fixed point. -/
import TP.DecPerm

namespace TP

variable {n : ℕ}

/-! ### Integer helpers -/

theorem int_emod_eq_of_bounds {x m c : ℤ} (h1 : 0 ≤ x - c * m) (h2 : x - c * m < m) :
    x % m = x - c * m := by
  have : x = (x - c * m) + c * m := by ring
  rw [this, Int.add_mul_emod_self_right, Int.emod_eq_of_lt h1 h2]
  ring

theorem int_decomp (z : ℤ) (m : ℕ) : z = z % (m : ℤ) + (m : ℤ) * (z / (m : ℤ)) := by
  exact (Int.emod_add_mul_ediv z (m : ℤ)).symm

theorem int_emod_bounds (z : ℤ) {m : ℕ} (hm : 0 < m) :
    0 ≤ z % (m : ℤ) ∧ z % (m : ℤ) < m :=
  ⟨Int.emod_nonneg _ (by exact_mod_cast hm.ne'), Int.emod_lt_of_pos _ (by exact_mod_cast hm)⟩

/-! ### Bounded affine permutations -/

theorem BddAffPerm.ext' {g g' : BddAffPerm n} (h : g.f = g'.f) : g = g' := by
  cases g; cases g'; cases h; rfl

theorem BddAffPerm.periodic_mul (g : BddAffPerm n) (j q : ℤ) :
    g.f (j + q * n) = g.f j + q * n := by
  induction q using Int.induction_on with
  | zero => simp
  | succ q ih =>
    have := g.periodic (j + q * n)
    rw [show j + ((q : ℤ) + 1) * n = j + q * n + n by ring, this, ih]
    ring
  | pred q ih =>
    have := g.periodic (j + (-(q : ℤ) - 1) * n)
    rw [show j + (-(q : ℤ) - 1) * n + n = j + -(q : ℤ) * n by ring, ih] at this
    linarith

theorem BddAffPerm.val_toFun (g : BddAffPerm n) (i : Fin n) :
    ((g.toFun i : ℕ) : ℤ) = g.f ((i : ℕ) : ℤ) % n := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have := (int_emod_bounds (g.f ((i : ℕ) : ℤ)) hn).1
  unfold BddAffPerm.toFun
  simp only
  omega

theorem BddAffPerm.toFun_injective (g : BddAffPerm n) : Function.Injective g.toFun := by
  intro i j hij
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h1 := g.val_toFun i
  have h2 := g.val_toFun j
  rw [hij] at h1
  have hmod : (g.f ((i : ℕ) : ℤ) - g.f ((j : ℕ) : ℤ)) % n = 0 :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (h1.symm.trans h2)
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero hmod
  have hf : g.f ((i : ℕ) : ℤ) = g.f (((j : ℕ) : ℤ) + c * n) := by
    rw [g.periodic_mul]; linarith
  have hij' := g.bijective.1 hf
  have hi := i.isLt
  have hj := j.isLt
  have hc0 : c = 0 := by
    rcases lt_trichotomy c 0 with h | h | h
    · have : c * (n : ℤ) ≤ -(n : ℤ) := by nlinarith
      omega
    · exact h
    · have : (n : ℤ) ≤ c * (n : ℤ) := by nlinarith
      omega
  rw [hc0] at hij'
  apply Fin.ext
  simp at hij'
  exact_mod_cast hij'

/-- The decorated permutation of a bounded affine permutation. -/
noncomputable def BddAffPerm.decPerm (g : BddAffPerm n) : DecPerm n where
  perm := Equiv.ofBijective g.toFun (Finite.injective_iff_bijective.mp g.toFun_injective)
  white := Finset.univ.filter fun i : Fin n => g.f ((i : ℕ) : ℤ) = ((i : ℕ) : ℤ) + n
  white_fixed := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    apply Fin.ext
    show (g.toFun i : ℕ) = i
    have h := g.val_toFun i
    rw [hi'] at h
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    rw [int_emod_eq_of_bounds (c := 1) (by have := i.isLt; omega) (by have := i.isLt; omega)] at h
    omega

/-! ### The affine lift of a decorated permutation -/

theorem DecPerm.windowLift_bounds (π : DecPerm n) (i : Fin n) :
    ((i : ℕ) : ℤ) ≤ π.windowLift i ∧ π.windowLift i ≤ ((i : ℕ) : ℤ) + n := by
  have h1 := (π.perm i).isLt
  have h2 := i.isLt
  unfold DecPerm.windowLift
  split_ifs <;> omega

theorem DecPerm.windowLift_emod (π : DecPerm n) (i : Fin n) :
    π.windowLift i % n = ((π.perm i : ℕ) : ℤ) := by
  have h1 := (π.perm i).isLt
  have h2 := i.isLt
  unfold DecPerm.windowLift
  split_ifs with ha hb hc
  · exact int_emod_eq_of_bounds (c := 0) (by omega) (by omega) |>.trans (by ring)
  · rw [int_emod_eq_of_bounds (c := 1) (by omega) (by omega)]; ring
  · have : (π.perm i : ℕ) = i := by omega
    rw [int_emod_eq_of_bounds (c := 1) (by omega) (by omega), this]; ring
  · have : (π.perm i : ℕ) = i := by omega
    rw [int_emod_eq_of_bounds (c := 0) (by omega) (by omega), this]; ring

/-- The affine lift: the window values extended by `f(z + n) = f(z) + n`. -/
noncomputable def DecPerm.affine (π : DecPerm n) (z : ℤ) : ℤ :=
  if h : 0 < n then
    π.windowLift ⟨(z % (n : ℤ)).toNat, by
      have := int_emod_bounds z h
      omega⟩ + n * (z / n)
  else z

theorem DecPerm.affine_eq (π : DecPerm n) (hn : 0 < n) (z : ℤ) (r : Fin n) (q : ℤ)
    (hz : z = ((r : ℕ) : ℤ) + n * q) : π.affine z = π.windowLift r + n * q := by
  unfold DecPerm.affine
  rw [dif_pos hn]
  have hr := r.isLt
  have hmod : z % (n : ℤ) = ((r : ℕ) : ℤ) := by
    rw [hz, int_emod_eq_of_bounds (c := q) (by linarith) (by linarith)]; ring
  have hdiv : z / (n : ℤ) = q := by
    have := int_decomp z n
    rw [hmod] at this
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have : (n : ℤ) * (z / n) = n * q := by linarith
    exact mul_left_cancel₀ hn'.ne' this
  have hfin : (⟨(z % (n : ℤ)).toNat, by have := int_emod_bounds z hn; omega⟩ : Fin n) = r := by
    apply Fin.ext; simp only; rw [hmod]; simp
  rw [hfin, hdiv]

theorem DecPerm.affine_window (π : DecPerm n) (i : Fin n) :
    π.affine ((i : ℕ) : ℤ) = π.windowLift i := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rw [π.affine_eq hn _ i 0 (by ring)]; ring

/-- Every integer is a window label plus a multiple of `n`. -/
theorem exists_window (hn : 0 < n) (z : ℤ) : ∃ (r : Fin n) (q : ℤ), z = ((r : ℕ) : ℤ) + n * q := by
  have hb := int_emod_bounds z hn
  refine ⟨⟨(z % (n : ℤ)).toNat, by omega⟩, z / n, ?_⟩
  simp only
  have := int_decomp z n
  rw [Int.toNat_of_nonneg hb.1]
  exact this

theorem DecPerm.affine_injective (π : DecPerm n) : Function.Injective π.affine := by
  intro z w h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · unfold DecPerm.affine at h; rw [dif_neg (by omega), dif_neg (by omega)] at h; exact h
  obtain ⟨r, q, hz⟩ := exists_window hn z
  obtain ⟨s, p, hw⟩ := exists_window hn w
  rw [π.affine_eq hn z r q hz, π.affine_eq hn w s p hw] at h
  have hm1 := π.windowLift_emod r
  have hm2 := π.windowLift_emod s
  have e1 : (π.windowLift r + n * q) % n = ((π.perm r : ℕ) : ℤ) := by
    rw [Int.add_mul_emod_self_left, hm1]
  have e2 : (π.windowLift s + n * p) % n = ((π.perm s : ℕ) : ℤ) := by
    rw [Int.add_mul_emod_self_left, hm2]
  rw [h] at e1
  have hrs : r = s := by
    apply π.perm.injective
    apply Fin.ext
    have := e1.symm.trans e2
    exact_mod_cast this
  subst hrs
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have : (n : ℤ) * q = n * p := by linarith
  have := mul_left_cancel₀ hn'.ne' this
  rw [hz, hw, this]

theorem DecPerm.affine_surjective (π : DecPerm n) : Function.Surjective π.affine := by
  intro y
  rcases Nat.eq_zero_or_pos n with hn | hn
  · refine ⟨y, ?_⟩; unfold DecPerm.affine; rw [dif_neg (by omega)]
  obtain ⟨s, p, hy⟩ := exists_window hn y
  set t := π.perm⁻¹ s with ht
  have hpt : π.perm t = s := perm_apply_inv_self π.perm s
  have hm := π.windowLift_emod t
  rw [hpt] at hm
  -- windowLift t = s + n * c
  have hdec := int_decomp (π.windowLift t) n
  rw [hm] at hdec
  refine ⟨((t : ℕ) : ℤ) + n * (p - π.windowLift t / n), ?_⟩
  rw [π.affine_eq hn _ t _ rfl, hy]
  linarith

theorem DecPerm.affine_bounds (π : DecPerm n) (z : ℤ) : z ≤ π.affine z ∧ π.affine z ≤ z + n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · unfold DecPerm.affine; rw [dif_neg (by omega)]; omega
  obtain ⟨r, q, hz⟩ := exists_window hn z
  rw [π.affine_eq hn z r q hz]
  have := π.windowLift_bounds r
  constructor <;> linarith [this.1, this.2]

theorem DecPerm.affine_periodic (π : DecPerm n) (z : ℤ) : π.affine (z + n) = π.affine z + n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · unfold DecPerm.affine; rw [dif_neg (by omega), dif_neg (by omega)]
  obtain ⟨r, q, hz⟩ := exists_window hn z
  rw [π.affine_eq hn z r q hz, π.affine_eq hn (z + n) r (q + 1) (by rw [hz]; ring)]
  ring

/-- The bounded affine permutation of a decorated permutation. -/
noncomputable def DecPerm.toBddAffPerm (π : DecPerm n) : BddAffPerm n where
  f := π.affine
  bijective := ⟨π.affine_injective, π.affine_surjective⟩
  periodic := π.affine_periodic
  self_le := fun z => (π.affine_bounds z).1
  le_add := fun z => (π.affine_bounds z).2

/-! ### The two round trips -/

theorem BddAffPerm.decPerm_perm (g : BddAffPerm n) (i : Fin n) :
    (g.decPerm.perm i : Fin n) = g.toFun i := rfl

theorem BddAffPerm.windowLift_decPerm (g : BddAffPerm n) (i : Fin n) :
    g.decPerm.windowLift i = g.f ((i : ℕ) : ℤ) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hi := i.isLt
  have hlo := g.self_le ((i : ℕ) : ℤ)
  have hhi := g.le_add ((i : ℕ) : ℤ)
  have hp := g.val_toFun i
  have hw : i ∈ g.decPerm.white ↔ g.f ((i : ℕ) : ℤ) = ((i : ℕ) : ℤ) + n := by
    show i ∈ Finset.univ.filter _ ↔ _
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  unfold DecPerm.windowLift
  rw [g.decPerm_perm]
  set a := g.f ((i : ℕ) : ℤ) with ha
  by_cases hlt : a < n
  · rw [int_emod_eq_of_bounds (c := 0) (by omega) (by omega)] at hp
    split_ifs with h1 h2 h3 <;> (try rw [hw] at h3) <;> omega
  · rw [int_emod_eq_of_bounds (c := 1) (by omega) (by omega)] at hp
    split_ifs with h1 h2 h3 <;> (try rw [hw] at h3) <;> omega

theorem BddAffPerm.toBddAffPerm_decPerm (g : BddAffPerm n) : g.decPerm.toBddAffPerm = g := by
  apply BddAffPerm.ext'
  funext z
  show g.decPerm.affine z = g.f z
  rcases Nat.eq_zero_or_pos n with hn | hn
  · unfold DecPerm.affine; rw [dif_neg (by omega)]
    have := g.self_le z; have := g.le_add z; omega
  obtain ⟨r, q, hz⟩ := exists_window hn z
  rw [g.decPerm.affine_eq hn z r q hz, g.windowLift_decPerm, hz,
    show ((r : ℕ) : ℤ) + n * q = ((r : ℕ) : ℤ) + q * n by ring, g.periodic_mul]
  ring

theorem DecPerm.decPerm_toBddAffPerm (π : DecPerm n) : π.toBddAffPerm.decPerm = π := by
  apply DecPerm.ext'
  · funext i
    apply Fin.ext
    show (π.toBddAffPerm.toFun i : ℕ) = π.perm i
    have h := π.toBddAffPerm.val_toFun i
    have h2 : π.toBddAffPerm.f ((i : ℕ) : ℤ) = π.windowLift i := π.affine_window i
    rw [h2, π.windowLift_emod] at h
    exact_mod_cast h
  · ext i
    show i ∈ Finset.univ.filter _ ↔ _
    rw [Finset.mem_filter]
    have h2 : π.toBddAffPerm.f ((i : ℕ) : ℤ) = π.windowLift i := π.affine_window i
    rw [h2]
    have hi := i.isLt
    have hp := (π.perm i).isLt
    have hn : 0 < n := by omega
    unfold DecPerm.windowLift
    constructor
    · rintro ⟨-, h⟩
      split_ifs at h with ha hb hc
      · omega
      · omega
      · exact hc
      · omega
    · intro hw
      have hfix := π.white_fixed i hw
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hfix, if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_pos hw]

/-- The bijection between bounded affine permutations and decorated permutations. -/
noncomputable def bddAffPermEquiv : BddAffPerm n ≃ DecPerm n where
  toFun := BddAffPerm.decPerm
  invFun := DecPerm.toBddAffPerm
  left_inv := BddAffPerm.toBddAffPerm_decPerm
  right_inv := DecPerm.decPerm_toBddAffPerm

theorem bddAffPerm_equiv :
    ∃ e : BddAffPerm n ≃ DecPerm n,
      (∀ g i, (e g).perm i = g.toFun i) ∧
      (∀ g, (e g).white =
        Finset.univ.filter fun i : Fin n => g.f ((i : ℕ) : ℤ) = ((i : ℕ) : ℤ) + n) ∧
      (∀ π (i : Fin n), (e.symm π).f ((i : ℕ) : ℤ) = π.windowLift i) :=
  ⟨bddAffPermEquiv, fun _ _ => rfl, fun _ => rfl, fun π i => π.affine_window i⟩

end TP
