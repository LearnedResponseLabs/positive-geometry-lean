/- Apache-2.0. Item 2: decorated permutations and Grassmann necklaces (Postnikov,
   Lemma 16.2, whose source proof is left to the reader). The forward map is the
   shifted anti-exceedance construction; the inverse map reads `π(r)` off
   `I_{r+1} \ I_r` and the colours off the stationary steps. -/
import TP.NecklaceBasic

namespace TP

variable {n : ℕ}

theorem DecPerm.ext' {π π' : DecPerm n} (hp : ⇑π.perm = ⇑π'.perm) (hw : π.white = π'.white) :
    π = π' := by
  obtain ⟨p, w, hpw⟩ := π
  obtain ⟨p', w', hpw'⟩ := π'
  simp only at hp hw
  subst hw
  have : p = p' := Equiv.ext (congrFun hp)
  subst this
  rfl

theorem perm_apply_inv_self (σ : Equiv.Perm (Fin n)) (x : Fin n) : σ (σ⁻¹ x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem perm_inv_apply_self (σ : Equiv.Perm (Fin n)) (x : Fin n) : σ⁻¹ (σ x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

theorem mem_necklaceOf {π : DecPerm n} {r i : Fin n} :
    i ∈ necklaceOf π r ↔ cycPos r i < cycPos r (π.perm⁻¹ i) ∨ i ∈ π.white := by
  unfold necklaceOf
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem DecPerm.inv_eq_self_iff (π : DecPerm n) (i : Fin n) :
    π.perm⁻¹ i = i ↔ π.perm i = i := by
  constructor
  · intro h
    have := perm_apply_inv_self π.perm i
    rw [h] at this
    exact this
  · intro h
    have := perm_inv_apply_self π.perm i
    rw [h] at this
    exact this

theorem DecPerm.inv_eq_iff (π : DecPerm n) (i j : Fin n) :
    π.perm⁻¹ i = j ↔ π.perm j = i := by
  constructor
  · intro h; rw [← h]; exact perm_apply_inv_self π.perm i
  · intro h; rw [← h]; exact perm_inv_apply_self π.perm j

theorem DecPerm.fixed_of_white (π : DecPerm n) {i : Fin n} (hi : i ∈ π.white) :
    π.perm i = i := π.white_fixed i hi

/-- The anti-exceedance necklace moves one step by removing `r` and adding `π(r)`. -/
theorem necklaceOf_succ (π : DecPerm n) (r : Fin n) :
    necklaceOf π (finRotate n r) =
      if π.perm r = r then necklaceOf π r
      else insert (π.perm r) ((necklaceOf π r).erase r) := by
  ext x
  rw [mem_necklaceOf]
  by_cases hxr : x = r
  · rw [hxr]
    have hmax := cycPos_finRotate_self_max r (π.perm⁻¹ r)
    by_cases hfix : π.perm r = r
    · rw [if_pos hfix, mem_necklaceOf, (π.inv_eq_self_iff r).mpr hfix, cycPos_self]
      constructor
      · rintro (h | h)
        · exact absurd h (by omega)
        · exact Or.inr h
      · rintro (h | h)
        · exact absurd h (Nat.lt_irrefl 0)
        · exact Or.inr h
    · rw [if_neg hfix, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (h | h)
        · exact absurd h (by omega)
        · exact absurd (π.fixed_of_white h) hfix
      · rintro (h | ⟨h, -⟩)
        · exact absurd h.symm hfix
        · exact absurd rfl h
  · by_cases hsr : π.perm⁻¹ x = r
    · have hx : π.perm r = x := (π.inv_eq_iff x r).mp hsr
      have hfix : π.perm r ≠ r := by rw [hx]; exact hxr
      rw [if_neg hfix, Finset.mem_insert, hsr]
      have h1 := cycPos_lt r x
      have h2 : cycPos r x ≠ 0 := fun h => hxr (cycPos_eq_zero_iff.mp h)
      rw [cycPos_finRotate r x, if_neg hxr, cycPos_finRotate r r, if_pos rfl]
      exact ⟨fun _ => Or.inl hx.symm, fun _ => Or.inl (by omega)⟩
    · rw [cycPos_finRotate_lt hxr hsr]
      by_cases hfix : π.perm r = r
      · rw [if_pos hfix, mem_necklaceOf]
      · rw [if_neg hfix, Finset.mem_insert, Finset.mem_erase, mem_necklaceOf]
        have hne : x ≠ π.perm r := fun h => hsr ((π.inv_eq_iff x r).mpr h.symm)
        constructor
        · intro h; exact Or.inr ⟨hxr, h⟩
        · rintro (h | ⟨-, h⟩)
          · exact absurd h hne
          · exact h

theorem self_mem_necklaceOf_of_ne (π : DecPerm n) {r : Fin n} (h : π.perm r ≠ r) :
    r ∈ necklaceOf π r := by
  rw [mem_necklaceOf, cycPos_self]
  left
  apply Nat.pos_of_ne_zero
  intro h0
  exact h ((π.inv_eq_self_iff r).mp (cycPos_eq_zero_iff.mp h0))

theorem perm_notMem_necklaceOf (π : DecPerm n) {r : Fin n} (h : π.perm r ≠ r) :
    π.perm r ∉ necklaceOf π r := by
  rw [mem_necklaceOf, perm_inv_apply_self, cycPos_self]
  rintro (h1 | h1)
  · exact Nat.not_lt_zero _ h1
  · have := π.fixed_of_white h1
    exact h (π.perm.injective this)

theorem necklaceOf_isNecklace (π : DecPerm n) : IsNecklace (necklaceOf π) := by
  intro r
  rw [necklaceOf_succ]
  constructor
  · intro hr
    split_ifs with h
    · exact ⟨r, (Finset.insert_erase hr).symm⟩
    · exact ⟨π.perm r, rfl⟩
  · intro hr
    split_ifs with h
    · rfl
    · exact absurd (self_mem_necklaceOf_of_ne π h) hr

theorem necklaceOf_zero (π : DecPerm n) (h : 0 < n) : necklaceOf π ⟨0, h⟩ = π.antiExc := by
  ext i
  rw [mem_necklaceOf, cycPos_eq, cycPos_eq]
  unfold DecPerm.antiExc
  rw [Finset.mem_filter]
  simp only [Nat.zero_le, if_true, Nat.sub_zero, Finset.mem_univ, true_and]

theorem necklaceOf_card (π : DecPerm n) (r : Fin n) :
    (necklaceOf π r).card = π.antiExc.card := by
  have h : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) r.isLt
  rw [necklace_card_eq (necklaceOf_isNecklace π) r ⟨0, h⟩, necklaceOf_zero π h]

/-- White fixed points belong to every term. -/
theorem white_mem_necklaceOf (π : DecPerm n) {i : Fin n} (hi : i ∈ π.white) (r : Fin n) :
    i ∈ necklaceOf π r := mem_necklaceOf.mpr (Or.inr hi)

/-- Black fixed points belong to no term. -/
theorem black_notMem_necklaceOf (π : DecPerm n) {i : Fin n} (hfix : π.perm i = i)
    (hb : i ∉ π.white) (r : Fin n) : i ∉ necklaceOf π r := by
  rw [mem_necklaceOf, (π.inv_eq_self_iff i).mpr hfix]
  rintro (h | h)
  · exact Nat.lt_irrefl _ h
  · exact hb h

/-! ### The inverse map on an arbitrary necklace -/

theorem necklacePerm_of_eq {I : Fin n → Finset (Fin n)} {r : Fin n}
    (h : I (finRotate n r) = I r) : necklacePerm I r = r := by
  unfold necklacePerm
  rw [h, Finset.sdiff_self, dif_neg Finset.not_nonempty_empty]

theorem necklacePerm_of_singleton {I : Fin n → Finset (Fin n)} {r j : Fin n}
    (h : I (finRotate n r) \ I r = {j}) : necklacePerm I r = j := by
  unfold necklacePerm
  rw [h, dif_pos (Finset.singleton_nonempty j), Finset.min'_singleton]

/-- One step of a necklace: either stationary (and `π(r) = r`), or `r` is removed and
`π(r) ∉ I_r` is added. -/
theorem IsNecklace.step {I : Fin n → Finset (Fin n)} (hI : IsNecklace I) (r : Fin n) :
    (necklacePerm I r = r ∧ I (finRotate n r) = I r) ∨
      (necklacePerm I r ≠ r ∧ r ∈ I r ∧ necklacePerm I r ∉ I r ∧
        I (finRotate n r) = insert (necklacePerm I r) ((I r).erase r)) := by
  by_cases hr : r ∈ I r
  · obtain ⟨j, hj⟩ := (hI r).1 hr
    have hcard := hI.card_succ r
    have hjn : j ∉ (I r).erase r := by
      intro hm
      rw [hj, Finset.insert_eq_of_mem hm, Finset.card_erase_of_mem hr] at hcard
      have : 0 < (I r).card := Finset.card_pos.mpr ⟨r, hr⟩
      omega
    by_cases hjr : j = r
    · subst hjr
      have hst : I (finRotate n j) = I j := by rw [hj, Finset.insert_erase hr]
      exact Or.inl ⟨necklacePerm_of_eq hst, hst⟩
    · have hjI : j ∉ I r := fun hm => hjn (Finset.mem_erase.mpr ⟨hjr, hm⟩)
      have hD : I (finRotate n r) \ I r = {j} := by
        ext x
        rw [Finset.mem_sdiff, hj, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro ⟨h1 | ⟨-, h1⟩, h2⟩
          · exact h1
          · exact absurd h1 h2
        · rintro rfl; exact ⟨Or.inl rfl, hjI⟩
      have hp := necklacePerm_of_singleton hD
      refine Or.inr ⟨by rw [hp]; exact hjr, hr, by rw [hp]; exact hjI, by rw [hp, hj]⟩
  · have hst := (hI r).2 hr
    exact Or.inl ⟨necklacePerm_of_eq hst, hst⟩

theorem IsNecklace.succ_eq {I : Fin n → Finset (Fin n)} (hI : IsNecklace I) (r : Fin n) :
    I (finRotate n r) =
      if necklacePerm I r = r then I r else insert (necklacePerm I r) ((I r).erase r) := by
  rcases hI.step r with ⟨h1, h2⟩ | ⟨h1, -, -, h2⟩
  · rw [if_pos h1, h2]
  · rw [if_neg h1, h2]

theorem necklaceWhite_fixed {I : Fin n → Finset (Fin n)} (_hI : IsNecklace I) {i : Fin n}
    (hi : i ∈ necklaceWhite I) : necklacePerm I i = i := by
  unfold necklaceWhite at hi
  rw [Finset.mem_filter] at hi
  exact necklacePerm_of_eq hi.2.2

theorem necklacePerm_injective {I : Fin n → Finset (Fin n)} (hI : IsNecklace I) :
    Function.Injective (necklacePerm I) := by
  intro a b hab
  by_contra hne
  set x := necklacePerm I a with hx
  have rise : ∀ t, necklacePerm I t = x → t ≠ x → (x ∉ I t ∧ x ∈ I (finRotate n t)) := by
    intro t ht htx
    rcases hI.step t with ⟨h1, -⟩ | ⟨-, -, h3, h4⟩
    · exact absurd (h1.symm.trans ht) htx
    · rw [ht] at h3 h4
      rw [h4]
      exact ⟨h3, Finset.mem_insert_self _ _⟩
  have fall : ∀ t, (x ∈ I t ∧ x ∉ I (finRotate n t)) → t = x ∧ necklacePerm I t ≠ t := by
    rintro t ⟨h1, h2⟩
    rcases hI.step t with ⟨-, h4⟩ | ⟨h3, -, -, h4⟩
    · rw [h4] at h2; exact absurd h1 h2
    · rw [h4, Finset.mem_insert, Finset.mem_erase] at h2
      push Not at h2
      exact ⟨by_contra fun hne' => h2.2 (Ne.symm hne') h1, h3⟩
  have hcount := card_rise_eq_card_fall (fun t => x ∈ I t)
  set rises := Finset.univ.filter fun t => ¬ x ∈ I t ∧ x ∈ I (finRotate n t)
  set falls := Finset.univ.filter fun t => x ∈ I t ∧ ¬ x ∈ I (finRotate n t)
  have hfalls : falls ⊆ {x} := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [Finset.mem_singleton]
    exact (fall t ht.2).1
  have hrise : ∀ t, necklacePerm I t = x → t ≠ x → t ∈ rises := by
    intro t ht htx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rise t ht htx⟩
  by_cases hax : a = x
  · -- `x` is a fixed point of the map, so `x` never leaves; but it enters at `b`
    have hbx : b ≠ x := fun h => hne (hax.trans h.symm)
    have hpx : necklacePerm I x = x := by
      have := hx.symm; rw [hax] at this; exact this
    have hf : falls = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro t ht
      have := fall t (Finset.mem_filter.mp ht).2
      rw [this.1] at this
      exact this.2 hpx
    have hb : b ∈ rises := hrise b hab.symm hbx
    rw [hf, Finset.card_empty] at hcount
    exact absurd hcount (Finset.card_ne_zero_of_mem hb)
  · by_cases hbx : b = x
    · have hpx : necklacePerm I x = x := by
        have := hab.symm; rw [hbx] at this; exact this
      have hf : falls = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro t ht
        have := fall t (Finset.mem_filter.mp ht).2
        rw [this.1] at this
        exact this.2 hpx
      have ha : a ∈ rises := hrise a rfl hax
      rw [hf, Finset.card_empty] at hcount
      exact absurd hcount (Finset.card_ne_zero_of_mem ha)
    · have h2 : ({a, b} : Finset (Fin n)) ⊆ rises := by
        intro t ht
        rw [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact hrise t rfl hax
        · exact hrise t hab.symm hbx
      have c1 := Finset.card_le_card h2
      rw [Finset.card_pair hne] at c1
      have c2 := Finset.card_le_card hfalls
      rw [Finset.card_singleton] at c2
      omega

theorem necklacePerm_bijective {I : Fin n → Finset (Fin n)} (hI : IsNecklace I) :
    Function.Bijective (necklacePerm I) :=
  Finite.injective_iff_bijective.mp (necklacePerm_injective hI)

theorem necklacePerm_necklaceOf (π : DecPerm n) :
    necklacePerm (necklaceOf π) = ⇑π.perm := by
  funext r
  by_cases hfix : π.perm r = r
  · rw [hfix]
    apply necklacePerm_of_eq
    rw [necklaceOf_succ, if_pos hfix]
  · apply necklacePerm_of_singleton
    rw [necklaceOf_succ, if_neg hfix]
    have hn := perm_notMem_necklaceOf π hfix
    ext x
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨h1 | ⟨-, h1⟩, h2⟩
      · exact h1
      · exact absurd h1 h2
    · rintro rfl; exact ⟨Or.inl rfl, hn⟩

theorem necklaceWhite_necklaceOf (π : DecPerm n) :
    necklaceWhite (necklaceOf π) = π.white := by
  ext r
  unfold necklaceWhite
  rw [Finset.mem_filter, necklaceOf_succ]
  by_cases hfix : π.perm r = r
  · rw [if_pos hfix, mem_necklaceOf, (π.inv_eq_self_iff r).mpr hfix]
    constructor
    · rintro ⟨-, h | h, -⟩
      · exact absurd h (Nat.lt_irrefl _)
      · exact h
    · intro h; exact ⟨Finset.mem_univ _, Or.inr h, rfl⟩
  · rw [if_neg hfix]
    constructor
    · rintro ⟨-, -, h⟩
      have hm : π.perm r ∈ insert (π.perm r) ((necklaceOf π r).erase r) :=
        Finset.mem_insert_self _ _
      rw [h] at hm
      exact absurd hm (perm_notMem_necklaceOf π hfix)
    · intro h; exact absurd (π.fixed_of_white h) hfix

/-- A necklace is the anti-exceedance necklace of the decorated permutation read off it. -/
theorem necklace_eq_necklaceOf {I : Fin n → Finset (Fin n)} (hI : IsNecklace I)
    (π : DecPerm n) (hp : ⇑π.perm = necklacePerm I) (hw : π.white = necklaceWhite I) :
    necklaceOf π = I := by
  funext t
  ext x
  have hstepN : ∀ s, necklaceOf π (finRotate n s) =
      if necklacePerm I s = s then necklaceOf π s
      else insert (necklacePerm I s) ((necklaceOf π s).erase s) := by
    intro s; rw [necklaceOf_succ, show π.perm s = necklacePerm I s from congrFun hp s]
  have pres : ∀ s, (x ∈ necklaceOf π s ↔ x ∈ I s) →
      (x ∈ necklaceOf π (finRotate n s) ↔ x ∈ I (finRotate n s)) := by
    intro s hs
    rw [hstepN s, hI.succ_eq s]
    split_ifs with h
    · exact hs
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase, hs]
  by_cases hxfix : necklacePerm I x = x
  · refine cyc_induction (P := fun s => x ∈ necklaceOf π s ↔ x ∈ I s) x ?_ pres t
    have hpx : π.perm x = x := by rw [congrFun hp x]; exact hxfix
    rw [mem_necklaceOf, (π.inv_eq_self_iff x).mpr hpx, hw]
    unfold necklaceWhite
    rw [Finset.mem_filter]
    rcases hI.step x with ⟨-, h2⟩ | ⟨h1, -⟩
    · constructor
      · rintro (h | ⟨-, h, -⟩)
        · exact absurd h (Nat.lt_irrefl _)
        · exact h
      · intro h; exact Or.inr ⟨Finset.mem_univ _, h, h2⟩
    · exact absurd hxfix h1
  · refine cyc_induction (P := fun s => x ∈ necklaceOf π s ↔ x ∈ I s) (finRotate n x) ?_ pres t
    rw [hstepN x, hI.succ_eq x, if_neg hxfix, if_neg hxfix, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_erase, Finset.mem_erase]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact absurd h.symm hxfix
      · exact absurd rfl h
    · rintro (h | ⟨h, -⟩)
      · exact absurd h.symm hxfix
      · exact absurd rfl h

theorem necklaceOf_injective :
    Function.Injective (necklaceOf : DecPerm n → Fin n → Finset (Fin n)) := by
  intro π π' h
  apply DecPerm.ext'
  · rw [← necklacePerm_necklaceOf π, ← necklacePerm_necklaceOf π', h]
  · rw [← necklaceWhite_necklaceOf π, ← necklaceWhite_necklaceOf π', h]

/-- The bijection of Lemma 16.2. -/
noncomputable def necklaceEquiv : DecPerm n ≃ {I : Fin n → Finset (Fin n) // IsNecklace I} where
  toFun π := ⟨necklaceOf π, necklaceOf_isNecklace π⟩
  invFun I := ⟨Equiv.ofBijective _ (necklacePerm_bijective I.2), necklaceWhite I.1,
    fun _ hi => necklaceWhite_fixed I.2 hi⟩
  left_inv π := DecPerm.ext' (by
      show necklacePerm (necklaceOf π) = ⇑π.perm
      exact necklacePerm_necklaceOf π) (necklaceWhite_necklaceOf π)
  right_inv I := Subtype.ext (necklace_eq_necklaceOf I.2 _ rfl rfl)

/-- Lemma 16.2: decorated permutations ↔ necklaces, with both maps explicit. -/
theorem lemma_16_2 :
    ∃ e : DecPerm n ≃ {I : Fin n → Finset (Fin n) // IsNecklace I},
      (∀ π, (e π : Fin n → Finset (Fin n)) = necklaceOf π) ∧
      (∀ I, ⇑(e.symm I).perm = necklacePerm I.1 ∧ (e.symm I).white = necklaceWhite I.1) :=
  ⟨necklaceEquiv, fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem antiExc_card_of_forall {π : DecPerm n} {k : ℕ} (hk : k ≤ n)
    (h : ∀ r, (necklaceOf π r).card = k) : π.antiExc.card = k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : k = 0 := by omega
    subst this
    rw [Finset.card_eq_zero]
    exact Finset.eq_empty_of_forall_notMem fun i => i.elim0
  · rw [← necklaceOf_card π ⟨0, hn⟩]; exact h _

/-- Lemma 16.2 refined by type (k, n). -/
theorem lemma_16_2_type (k : ℕ) (hk : k ≤ n) :
    ∃ e : {π : DecPerm n // π.antiExc.card = k} ≃
        {I : Fin n → Finset (Fin n) // IsNecklace I ∧ ∀ r, (I r).card = k},
      ∀ π, (e π : Fin n → Finset (Fin n)) = necklaceOf π.1 := by
  refine ⟨{ toFun := fun π => ⟨necklaceOf π.1, necklaceOf_isNecklace π.1,
                fun r => (necklaceOf_card π.1 r).trans π.2⟩
            invFun := fun I => ⟨necklaceEquiv.symm ⟨I.1, I.2.1⟩, ?_⟩
            left_inv := ?_
            right_inv := ?_ }, fun _ => rfl⟩
  · apply antiExc_card_of_forall hk
    intro r
    have h := congrArg Subtype.val (necklaceEquiv.apply_symm_apply ⟨I.1, I.2.1⟩)
    have h' : necklaceOf (necklaceEquiv.symm ⟨I.1, I.2.1⟩) = I.1 := h
    rw [h']
    exact I.2.2 r
  · intro π
    apply Subtype.ext
    exact necklaceEquiv.symm_apply_apply π.1
  · intro I
    apply Subtype.ext
    show necklaceOf (necklaceEquiv.symm ⟨I.1, I.2.1⟩) = I.1
    exact congrArg Subtype.val (necklaceEquiv.apply_symm_apply ⟨I.1, I.2.1⟩)

end TP
