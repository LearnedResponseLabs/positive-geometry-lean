/-
Conj43/SeedTableMaster.lean — the four edge-set masters of the §5 transition
(PAPER_SECTION.tex Lemma "Exact local transition"): identity (A = b) and the
three A > b regimes (left subdivision / triangle / right subdivision), each as a
full ordered-pair classification of `GEdgeSet W.σ` against
`GEdgeSet (W.σ * swap a b)`.
-/
import Conj43.SeedTableLocal

namespace Conj43

variable {n : ℕ}

/-- The label at an active-or-fixed position decomposes its lift. -/
theorem lift_decomp (W : Window n) (i : Fin n) :
    ((W.σ i : Fin n) : ℕ) = W.w i ∨ ((W.σ i : Fin n) : ℕ) + n = W.w i := by
  have hres := W.hres i
  have hub := W.hub i
  have hi := i.isLt
  rcases Nat.lt_or_ge (W.w i) n with h2 | h2
  · left; rw [← hres, Nat.mod_eq_of_lt h2]
  · right; rw [← hres, Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)]; omega

namespace Window

variable {W : Window n} {a b : Fin n}

/-- **Identity master (`A = b`, eq 8.9).** The swap does not change the edge set. -/
theorem master_identity (hab : a < b) (haact : W.Active a) (hbact : W.Active b)
    (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x)
    (hBan : W.w b ≤ (a : ℕ) + n) (hAb : W.w a = (b : ℕ)) :
    ∀ e : Fin n × Fin n,
      e ∈ GEdgeSet W.σ ↔ e ∈ GEdgeSet (W.σ * Equiv.swap a b) := by
  have habn : (a : ℕ) < (b : ℕ) := hab
  have hbn := b.isLt
  have hαb : W.σ a = b := by
    have hres := W.hres a
    rw [hAb, Nat.mod_eq_of_lt hbn] at hres
    exact Fin.ext hres.symm
  have hβb : W.σ b ≠ b := hbact
  have hgb_fix : (W.σ * Equiv.swap a b) b = b := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαb]
  have hbB : (b : ℕ) < W.w b := (W.active_strict hbact).1
  have hβd := lift_decomp W b
  have hswb_val : ((W.σ⁻¹ b : Fin n) : ℕ) = (a : ℕ) := by
    rw [← hαb, perm_inv_apply']
  have hswβ_val : ((W.σ⁻¹ (W.σ b) : Fin n) : ℕ) = (b : ℕ) := by rw [perm_inv_apply']
  have hVbβ : ¬ GCross W.σ b (W.σ b) := fun h =>
    id_w_bbe habn hbn hbB hBan (W.σ b).isLt hβd ((gcross_points hswb_val hswβ_val).mp h)
  have hVβb : ¬ GCross W.σ (W.σ b) b := fun h =>
    id_w_beb habn hbn hbB hBan (W.σ b).isLt hβd ((gcross_points hswβ_val hswb_val).mp h)
  intro e
  obtain ⟨p, q⟩ := e
  simp only [mem_GEdgeSet]
  by_cases hpq : p = q
  · subst hpq
    exact iff_of_false (not_gcross_self _ _) (not_gcross_self _ _)
  by_cases hpb : p = b
  · subst p
    by_cases hqβ : q = W.σ b
    · subst hqβ
      exact iff_of_false hVbβ (not_gcross_fixed_fst hgb_fix _)
    · refine iff_of_false ?_ (not_gcross_fixed_fst hgb_fix _)
      by_cases hqfix : W.σ q = q
      · exact not_gcross_fixed_snd hqfix _
      · intro hcw
        have hqact : W.Active q := hqfix
        have hqb : q ≠ b := fun h => hpq h.symm
        have hsact := inv_active hqact
        have hsa : W.σ⁻¹ q ≠ a := fun h =>
          hqb (by rw [← perm_apply_inv' W.σ q, h, hαb])
        have hsb : W.σ⁻¹ q ≠ b := fun h =>
          hqβ (by rw [← perm_apply_inv' W.σ q, h])
        have hspos := pos_avoid hadj hsact hsb
        have hsane : ((W.σ⁻¹ q : Fin n) : ℕ) ≠ (a : ℕ) := fun h => hsa (Fin.ext h)
        have hqpos := pos_avoid hadj hqact hqb
        exact id_w_bq habn hbn (W.σ⁻¹ q).isLt q.isLt (by omega) (by omega)
          ((gcross_points hswb_val rfl).mp hcw)
  by_cases hqb : q = b
  · subst q
    by_cases hpβ : p = W.σ b
    · subst hpβ
      exact iff_of_false hVβb (not_gcross_fixed_snd hgb_fix _)
    · refine iff_of_false ?_ (not_gcross_fixed_snd hgb_fix _)
      by_cases hpfix : W.σ p = p
      · exact not_gcross_fixed_fst hpfix _
      · intro hcw
        have hpact : W.Active p := hpfix
        have hsact := inv_active hpact
        have hsa : W.σ⁻¹ p ≠ a := fun h =>
          hpb (by rw [← perm_apply_inv' W.σ p, h, hαb])
        have hsb : W.σ⁻¹ p ≠ b := fun h =>
          hpβ (by rw [← perm_apply_inv' W.σ p, h])
        have hspos := pos_avoid hadj hsact hsb
        have hsane : ((W.σ⁻¹ p : Fin n) : ℕ) ≠ (a : ℕ) := fun h => hsa (Fin.ext h)
        have hppos := pos_avoid hadj hpact hpb
        exact id_w_qb habn hbn (W.σ⁻¹ p).isLt p.isLt (by omega) (by omega)
          ((gcross_points rfl hswb_val).mp hcw)
  by_cases hpβ : p = W.σ b
  · subst hpβ
    exact mixed_beta_fst hab haact hbact hadj q (by rw [hαb]; exact hqb)
      (fun h => hpq h.symm) hqb
  by_cases hqβ : q = W.σ b
  · subst hqβ
    exact mixed_beta_snd hab haact hbact hadj p (by rw [hαb]; exact hpb) hpβ hpb
  · exact triv_pair (by rw [hαb]; exact hpb) hpβ (by rw [hαb]; exact hqb) hqβ

set_option maxHeartbeats 1000000 in
/-- **Left-subdivision master (`S < A`, eq 8.11).**
`E(w) = (E(g) \ {α→b}) ∪ {α→β, β→b}`. -/
theorem master_left {c : Fin n} {S : ℕ} (hab : a < b) (haact : W.Active a)
    (hbact : W.Active b) (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x)
    (hasc : W.w a < W.w b) (hBan : W.w b ≤ (a : ℕ) + n) (hbA : (b : ℕ) < W.w a)
    (hc : W.σ⁻¹ b = c)
    (hS : ((c : ℕ) < (a : ℕ) ∧ S = (c : ℕ) + n) ∨ ((b : ℕ) < (c : ℕ) ∧ S = (c : ℕ)))
    (hSA : S < W.w a) :
    (W.σ a, b) ∈ GEdgeSet (W.σ * Equiv.swap a b) ∧
    (W.σ a, W.σ b) ∉ GEdgeSet (W.σ * Equiv.swap a b) ∧
    (W.σ b, b) ∉ GEdgeSet (W.σ * Equiv.swap a b) ∧
    ∀ e : Fin n × Fin n, e ∈ GEdgeSet W.σ ↔
      ((e ∈ GEdgeSet (W.σ * Equiv.swap a b) ∧ e ≠ (W.σ a, b)) ∨
        e = (W.σ a, W.σ b) ∨ e = (W.σ b, b)) := by
  have habn : (a : ℕ) < (b : ℕ) := hab
  have hTab : Tab n ↑a ↑b (W.w a) (W.w b) ↑(W.σ a) ↑(W.σ b) :=
    ⟨habn, b.isLt, hbA, hasc, (W.active_strict haact).2, (W.active_strict hbact).2,
      hBan, (W.σ a).isLt, (W.σ b).isLt, lift_decomp W a, lift_decomp W b⟩
  have hTabC : TabC ↑a ↑b n ↑c S := ⟨c.isLt, hS⟩
  have hSB : S < W.w b := lt_trans hSA hasc
  have hαb : W.σ a ≠ b := alpha_ne_b haact hab hbA
  have hβb : W.σ b ≠ b := hbact
  have hαβ : W.σ a ≠ W.σ b := fun h => (ne_of_lt hab) (W.σ.injective h)
  have hca : c ≠ a := by
    intro h; rw [h] at hc
    exact hαb (by rw [← hc, perm_apply_inv'])
  have hcb : c ≠ b := by
    intro h; rw [h] at hc
    have h2 : W.σ (W.σ⁻¹ b) = W.σ b := congrArg W.σ hc
    rw [perm_apply_inv'] at h2
    exact hβb h2.symm
  have hswa : ((W.σ⁻¹ (W.σ a) : Fin n) : ℕ) = (a : ℕ) := by rw [perm_inv_apply']
  have hswb : ((W.σ⁻¹ (W.σ b) : Fin n) : ℕ) = (b : ℕ) := by rw [perm_inv_apply']
  have hswc : ((W.σ⁻¹ b : Fin n) : ℕ) = (c : ℕ) := congrArg Fin.val hc
  have hgswa : (((W.σ * Equiv.swap a b)⁻¹ (W.σ a) : Fin n) : ℕ) = (b : ℕ) := by
    rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_left]
  have hgswb : (((W.σ * Equiv.swap a b)⁻¹ (W.σ b) : Fin n) : ℕ) = (a : ℕ) := by
    rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_right]
  have hgswc : (((W.σ * Equiv.swap a b)⁻¹ b : Fin n) : ℕ) = (c : ℕ) := by
    rw [mul_swap_inv_apply, hc, Equiv.swap_apply_of_ne_of_ne hca hcb]
  have hVw_αβ : GCross W.σ (W.σ a) (W.σ b) :=
    (gcross_points hswa hswb).mpr (vs_w_ab hTab)
  have hVw_βα : ¬ GCross W.σ (W.σ b) (W.σ a) := fun h =>
    vs_w_ba hTab ((gcross_points hswb hswa).mp h)
  have hVg_βα : ¬ GCross (W.σ * Equiv.swap a b) (W.σ b) (W.σ a) := fun h =>
    vs_g_ba hTab ((gcross_points hgswb hgswa).mp h)
  have hVw_αb : ¬ GCross W.σ (W.σ a) b := fun h =>
    v_w_alb hTab hTabC ((gcross_points hswa hswc).mp h)
  have hVw_bα : ¬ GCross W.σ b (W.σ a) := fun h =>
    v_w_bal_lt hTab hTabC hSA ((gcross_points hswc hswa).mp h)
  have hVg_bα : ¬ GCross (W.σ * Equiv.swap a b) b (W.σ a) := fun h =>
    v_g_bal hTab hTabC ((gcross_points hgswc hgswa).mp h)
  have hVw_βb : GCross W.σ (W.σ b) b :=
    (gcross_points hswb hswc).mpr (v_w_beb_lt hTab hTabC hSB)
  have hVw_bβ : ¬ GCross W.σ b (W.σ b) := fun h =>
    v_w_bbe hTab hTabC ((gcross_points hswc hswb).mp h)
  have hVg_bβ : ¬ GCross (W.σ * Equiv.swap a b) b (W.σ b) := fun h =>
    v_g_bbe_lt hTab hTabC hSB ((gcross_points hgswc hgswb).mp h)
  have hVg_αb : GCross (W.σ * Equiv.swap a b) (W.σ a) b :=
    (gcross_points hgswa hgswc).mpr (v_g_alb_lt hTab hTabC hSA)
  have hVg_αβ : ¬ GCross (W.σ * Equiv.swap a b) (W.σ a) (W.σ b) := fun h =>
    vs_g_ab hTab ((gcross_points hgswa hgswb).mp h)
  have hVg_βb : ¬ GCross (W.σ * Equiv.swap a b) (W.σ b) b := fun h =>
    v_g_beb hTab hTabC ((gcross_points hgswb hgswc).mp h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_GEdgeSet]; exact hVg_αb
  · rw [mem_GEdgeSet]; exact hVg_αβ
  · rw [mem_GEdgeSet]; exact hVg_βb
  intro e
  obtain ⟨p, q⟩ := e
  simp only [mem_GEdgeSet]
  by_cases h1 : (p, q) = (W.σ a, W.σ b)
  · injection h1 with hp hq
    subst hp; subst hq
    exact iff_of_true hVw_αβ (Or.inr (Or.inl rfl))
  by_cases h2 : (p, q) = (W.σ b, W.σ a)
  · injection h2 with hp hq
    subst hp; subst hq
    refine iff_of_false hVw_βα ?_
    rintro (⟨hg, -⟩ | he | he)
    · exact hVg_βα hg
    · injection he with he1 he2
      exact hαβ he1.symm
    · injection he with he1 he2
      exact hαb he2
  by_cases h3 : (p, q) = (W.σ a, b)
  · injection h3 with hp hq
    subst hp; subst q
    refine iff_of_false hVw_αb ?_
    rintro (⟨-, hne⟩ | he | he)
    · exact hne rfl
    · injection he with he1 he2
      exact hβb he2.symm
    · injection he with he1 he2
      exact hαβ he1
  by_cases h4 : (p, q) = (b, W.σ a)
  · injection h4 with hp hq
    subst p; subst hq
    refine iff_of_false hVw_bα ?_
    rintro (⟨hg, -⟩ | he | he)
    · exact hVg_bα hg
    · injection he with he1 he2
      exact hαb he1.symm
    · injection he with he1 he2
      exact hβb he1.symm
  by_cases h5 : (p, q) = (W.σ b, b)
  · injection h5 with hp hq
    subst hp; subst q
    exact iff_of_true hVw_βb (Or.inr (Or.inr rfl))
  by_cases h6 : (p, q) = (b, W.σ b)
  · injection h6 with hp hq
    subst p; subst hq
    refine iff_of_false hVw_bβ ?_
    rintro (⟨hg, -⟩ | he | he)
    · exact hVg_bβ hg
    · injection he with he1 he2
      exact hαb he1.symm
    · injection he with he1 he2
      exact hβb he1.symm
  have key := nonspecial hab haact hbact hadj hbA p q h1 h2 h3 h4 h5 h6
  rw [key]
  constructor
  · intro hg
    exact Or.inl ⟨hg, h3⟩
  · rintro (⟨hg, -⟩ | he | he)
    · exact hg
    · exact absurd he h1
    · exact absurd he h5

set_option maxHeartbeats 1000000 in
/-- **Triangle master (`A ≤ S < B`, eq 8.12).** `E(w) = E(g) ∪ {b→α, α→β, β→b}`. -/
theorem master_triangle {c : Fin n} {S : ℕ} (hab : a < b) (haact : W.Active a)
    (hbact : W.Active b) (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x)
    (hasc : W.w a < W.w b) (hBan : W.w b ≤ (a : ℕ) + n) (hbA : (b : ℕ) < W.w a)
    (hc : W.σ⁻¹ b = c)
    (hS : ((c : ℕ) < (a : ℕ) ∧ S = (c : ℕ) + n) ∨ ((b : ℕ) < (c : ℕ) ∧ S = (c : ℕ)))
    (hAS : W.w a ≤ S) (hSB : S < W.w b) :
    (b, W.σ a) ∉ GEdgeSet (W.σ * Equiv.swap a b) ∧
    (W.σ a, W.σ b) ∉ GEdgeSet (W.σ * Equiv.swap a b) ∧
    (W.σ b, b) ∉ GEdgeSet (W.σ * Equiv.swap a b) ∧
    ∀ e : Fin n × Fin n, e ∈ GEdgeSet W.σ ↔
      (e ∈ GEdgeSet (W.σ * Equiv.swap a b) ∨
        e = (b, W.σ a) ∨ e = (W.σ a, W.σ b) ∨ e = (W.σ b, b)) := by
  have habn : (a : ℕ) < (b : ℕ) := hab
  have hTab : Tab n ↑a ↑b (W.w a) (W.w b) ↑(W.σ a) ↑(W.σ b) :=
    ⟨habn, b.isLt, hbA, hasc, (W.active_strict haact).2, (W.active_strict hbact).2,
      hBan, (W.σ a).isLt, (W.σ b).isLt, lift_decomp W a, lift_decomp W b⟩
  have hTabC : TabC ↑a ↑b n ↑c S := ⟨c.isLt, hS⟩
  have hαb : W.σ a ≠ b := alpha_ne_b haact hab hbA
  have hβb : W.σ b ≠ b := hbact
  have hαβ : W.σ a ≠ W.σ b := fun h => (ne_of_lt hab) (W.σ.injective h)
  have hca : c ≠ a := by
    intro h; rw [h] at hc
    exact hαb (by rw [← hc, perm_apply_inv'])
  have hcb : c ≠ b := by
    intro h; rw [h] at hc
    have h2 : W.σ (W.σ⁻¹ b) = W.σ b := congrArg W.σ hc
    rw [perm_apply_inv'] at h2
    exact hβb h2.symm
  have hswa : ((W.σ⁻¹ (W.σ a) : Fin n) : ℕ) = (a : ℕ) := by rw [perm_inv_apply']
  have hswb : ((W.σ⁻¹ (W.σ b) : Fin n) : ℕ) = (b : ℕ) := by rw [perm_inv_apply']
  have hswc : ((W.σ⁻¹ b : Fin n) : ℕ) = (c : ℕ) := congrArg Fin.val hc
  have hgswa : (((W.σ * Equiv.swap a b)⁻¹ (W.σ a) : Fin n) : ℕ) = (b : ℕ) := by
    rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_left]
  have hgswb : (((W.σ * Equiv.swap a b)⁻¹ (W.σ b) : Fin n) : ℕ) = (a : ℕ) := by
    rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_right]
  have hgswc : (((W.σ * Equiv.swap a b)⁻¹ b : Fin n) : ℕ) = (c : ℕ) := by
    rw [mul_swap_inv_apply, hc, Equiv.swap_apply_of_ne_of_ne hca hcb]
  have hVw_αβ : GCross W.σ (W.σ a) (W.σ b) :=
    (gcross_points hswa hswb).mpr (vs_w_ab hTab)
  have hVw_βα : ¬ GCross W.σ (W.σ b) (W.σ a) := fun h =>
    vs_w_ba hTab ((gcross_points hswb hswa).mp h)
  have hVg_αβ : ¬ GCross (W.σ * Equiv.swap a b) (W.σ a) (W.σ b) := fun h =>
    vs_g_ab hTab ((gcross_points hgswa hgswb).mp h)
  have hVg_βα : ¬ GCross (W.σ * Equiv.swap a b) (W.σ b) (W.σ a) := fun h =>
    vs_g_ba hTab ((gcross_points hgswb hgswa).mp h)
  have hVw_αb : ¬ GCross W.σ (W.σ a) b := fun h =>
    v_w_alb hTab hTabC ((gcross_points hswa hswc).mp h)
  have hVg_αb : ¬ GCross (W.σ * Equiv.swap a b) (W.σ a) b := fun h =>
    v_g_alb_ge hTab hTabC hAS ((gcross_points hgswa hgswc).mp h)
  have hVw_bα : GCross W.σ b (W.σ a) :=
    (gcross_points hswc hswa).mpr (v_w_bal_ge hTab hTabC hAS)
  have hVg_bα : ¬ GCross (W.σ * Equiv.swap a b) b (W.σ a) := fun h =>
    v_g_bal hTab hTabC ((gcross_points hgswc hgswa).mp h)
  have hVw_βb : GCross W.σ (W.σ b) b :=
    (gcross_points hswb hswc).mpr (v_w_beb_lt hTab hTabC hSB)
  have hVg_βb : ¬ GCross (W.σ * Equiv.swap a b) (W.σ b) b := fun h =>
    v_g_beb hTab hTabC ((gcross_points hgswb hgswc).mp h)
  have hVw_bβ : ¬ GCross W.σ b (W.σ b) := fun h =>
    v_w_bbe hTab hTabC ((gcross_points hswc hswb).mp h)
  have hVg_bβ : ¬ GCross (W.σ * Equiv.swap a b) b (W.σ b) := fun h =>
    v_g_bbe_lt hTab hTabC hSB ((gcross_points hgswc hgswb).mp h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_GEdgeSet]; exact hVg_bα
  · rw [mem_GEdgeSet]; exact hVg_αβ
  · rw [mem_GEdgeSet]; exact hVg_βb
  intro e
  obtain ⟨p, q⟩ := e
  simp only [mem_GEdgeSet]
  by_cases h1 : (p, q) = (W.σ a, W.σ b)
  · injection h1 with hp hq
    subst hp; subst hq
    exact iff_of_true hVw_αβ (Or.inr (Or.inr (Or.inl rfl)))
  by_cases h2 : (p, q) = (W.σ b, W.σ a)
  · injection h2 with hp hq
    subst hp; subst hq
    refine iff_of_false hVw_βα ?_
    rintro (hg | he | he | he)
    · exact hVg_βα hg
    · injection he with he1 he2
      exact hβb he1
    · injection he with he1 he2
      exact hαβ he1.symm
    · injection he with he1 he2
      exact hαb he2
  by_cases h3 : (p, q) = (W.σ a, b)
  · injection h3 with hp hq
    subst hp; subst q
    refine iff_of_false hVw_αb ?_
    rintro (hg | he | he | he)
    · exact hVg_αb hg
    · injection he with he1 he2
      exact hαb he1
    · injection he with he1 he2
      exact hβb he2.symm
    · injection he with he1 he2
      exact hαβ he1
  by_cases h4 : (p, q) = (b, W.σ a)
  · injection h4 with hp hq
    subst p; subst hq
    exact iff_of_true hVw_bα (Or.inr (Or.inl rfl))
  by_cases h5 : (p, q) = (W.σ b, b)
  · injection h5 with hp hq
    subst hp; subst q
    exact iff_of_true hVw_βb (Or.inr (Or.inr (Or.inr rfl)))
  by_cases h6 : (p, q) = (b, W.σ b)
  · injection h6 with hp hq
    subst p; subst hq
    refine iff_of_false hVw_bβ ?_
    rintro (hg | he | he | he)
    · exact hVg_bβ hg
    · injection he with he1 he2
      exact hαβ he2.symm
    · injection he with he1 he2
      exact hαb he1.symm
    · injection he with he1 he2
      exact hβb he1.symm
  have key := nonspecial hab haact hbact hadj hbA p q h1 h2 h3 h4 h5 h6
  rw [key]
  constructor
  · intro hg
    exact Or.inl hg
  · rintro (hg | he | he | he)
    · exact hg
    · exact absurd he h4
    · exact absurd he h1
    · exact absurd he h5

set_option maxHeartbeats 1000000 in
/-- **Right-subdivision master (`B ≤ S`, eq 8.13).**
`E(w) = (E(g) \ {b→β}) ∪ {b→α, α→β}`. -/
theorem master_right {c : Fin n} {S : ℕ} (hab : a < b) (haact : W.Active a)
    (hbact : W.Active b) (hadj : ∀ x : Fin n, a < x → x < b → ¬ W.Active x)
    (hasc : W.w a < W.w b) (hBan : W.w b ≤ (a : ℕ) + n) (hbA : (b : ℕ) < W.w a)
    (hc : W.σ⁻¹ b = c)
    (hS : ((c : ℕ) < (a : ℕ) ∧ S = (c : ℕ) + n) ∨ ((b : ℕ) < (c : ℕ) ∧ S = (c : ℕ)))
    (hBS : W.w b ≤ S) :
    (b, W.σ b) ∈ GEdgeSet (W.σ * Equiv.swap a b) ∧
    (b, W.σ a) ∉ GEdgeSet (W.σ * Equiv.swap a b) ∧
    (W.σ a, W.σ b) ∉ GEdgeSet (W.σ * Equiv.swap a b) ∧
    ∀ e : Fin n × Fin n, e ∈ GEdgeSet W.σ ↔
      ((e ∈ GEdgeSet (W.σ * Equiv.swap a b) ∧ e ≠ (b, W.σ b)) ∨
        e = (b, W.σ a) ∨ e = (W.σ a, W.σ b)) := by
  have habn : (a : ℕ) < (b : ℕ) := hab
  have hAS : W.w a ≤ S := le_of_lt (lt_of_lt_of_le hasc hBS)
  have hTab : Tab n ↑a ↑b (W.w a) (W.w b) ↑(W.σ a) ↑(W.σ b) :=
    ⟨habn, b.isLt, hbA, hasc, (W.active_strict haact).2, (W.active_strict hbact).2,
      hBan, (W.σ a).isLt, (W.σ b).isLt, lift_decomp W a, lift_decomp W b⟩
  have hTabC : TabC ↑a ↑b n ↑c S := ⟨c.isLt, hS⟩
  have hαb : W.σ a ≠ b := alpha_ne_b haact hab hbA
  have hβb : W.σ b ≠ b := hbact
  have hαβ : W.σ a ≠ W.σ b := fun h => (ne_of_lt hab) (W.σ.injective h)
  have hca : c ≠ a := by
    intro h; rw [h] at hc
    exact hαb (by rw [← hc, perm_apply_inv'])
  have hcb : c ≠ b := by
    intro h; rw [h] at hc
    have h2 : W.σ (W.σ⁻¹ b) = W.σ b := congrArg W.σ hc
    rw [perm_apply_inv'] at h2
    exact hβb h2.symm
  have hswa : ((W.σ⁻¹ (W.σ a) : Fin n) : ℕ) = (a : ℕ) := by rw [perm_inv_apply']
  have hswb : ((W.σ⁻¹ (W.σ b) : Fin n) : ℕ) = (b : ℕ) := by rw [perm_inv_apply']
  have hswc : ((W.σ⁻¹ b : Fin n) : ℕ) = (c : ℕ) := congrArg Fin.val hc
  have hgswa : (((W.σ * Equiv.swap a b)⁻¹ (W.σ a) : Fin n) : ℕ) = (b : ℕ) := by
    rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_left]
  have hgswb : (((W.σ * Equiv.swap a b)⁻¹ (W.σ b) : Fin n) : ℕ) = (a : ℕ) := by
    rw [mul_swap_inv_apply, perm_inv_apply', Equiv.swap_apply_right]
  have hgswc : (((W.σ * Equiv.swap a b)⁻¹ b : Fin n) : ℕ) = (c : ℕ) := by
    rw [mul_swap_inv_apply, hc, Equiv.swap_apply_of_ne_of_ne hca hcb]
  have hVw_αβ : GCross W.σ (W.σ a) (W.σ b) :=
    (gcross_points hswa hswb).mpr (vs_w_ab hTab)
  have hVw_βα : ¬ GCross W.σ (W.σ b) (W.σ a) := fun h =>
    vs_w_ba hTab ((gcross_points hswb hswa).mp h)
  have hVg_αβ : ¬ GCross (W.σ * Equiv.swap a b) (W.σ a) (W.σ b) := fun h =>
    vs_g_ab hTab ((gcross_points hgswa hgswb).mp h)
  have hVg_βα : ¬ GCross (W.σ * Equiv.swap a b) (W.σ b) (W.σ a) := fun h =>
    vs_g_ba hTab ((gcross_points hgswb hgswa).mp h)
  have hVw_αb : ¬ GCross W.σ (W.σ a) b := fun h =>
    v_w_alb hTab hTabC ((gcross_points hswa hswc).mp h)
  have hVg_αb : ¬ GCross (W.σ * Equiv.swap a b) (W.σ a) b := fun h =>
    v_g_alb_ge hTab hTabC hAS ((gcross_points hgswa hgswc).mp h)
  have hVw_bα : GCross W.σ b (W.σ a) :=
    (gcross_points hswc hswa).mpr (v_w_bal_ge hTab hTabC hAS)
  have hVg_bα : ¬ GCross (W.σ * Equiv.swap a b) b (W.σ a) := fun h =>
    v_g_bal hTab hTabC ((gcross_points hgswc hgswa).mp h)
  have hVw_βb : ¬ GCross W.σ (W.σ b) b := fun h =>
    v_w_beb_ge hTab hTabC hBS ((gcross_points hswb hswc).mp h)
  have hVg_βb : ¬ GCross (W.σ * Equiv.swap a b) (W.σ b) b := fun h =>
    v_g_beb hTab hTabC ((gcross_points hgswb hgswc).mp h)
  have hVw_bβ : ¬ GCross W.σ b (W.σ b) := fun h =>
    v_w_bbe hTab hTabC ((gcross_points hswc hswb).mp h)
  have hVg_bβ : GCross (W.σ * Equiv.swap a b) b (W.σ b) :=
    (gcross_points hgswc hgswb).mpr (v_g_bbe_ge hTab hTabC hBS)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_GEdgeSet]; exact hVg_bβ
  · rw [mem_GEdgeSet]; exact hVg_bα
  · rw [mem_GEdgeSet]; exact hVg_αβ
  intro e
  obtain ⟨p, q⟩ := e
  simp only [mem_GEdgeSet]
  by_cases h1 : (p, q) = (W.σ a, W.σ b)
  · injection h1 with hp hq
    subst hp; subst hq
    exact iff_of_true hVw_αβ (Or.inr (Or.inr rfl))
  by_cases h2 : (p, q) = (W.σ b, W.σ a)
  · injection h2 with hp hq
    subst hp; subst hq
    refine iff_of_false hVw_βα ?_
    rintro (⟨hg, -⟩ | he | he)
    · exact hVg_βα hg
    · injection he with he1 he2
      exact hβb he1
    · injection he with he1 he2
      exact hαβ he1.symm
  by_cases h3 : (p, q) = (W.σ a, b)
  · injection h3 with hp hq
    subst hp; subst q
    refine iff_of_false hVw_αb ?_
    rintro (⟨hg, -⟩ | he | he)
    · exact hVg_αb hg
    · injection he with he1 he2
      exact hαb he1
    · injection he with he1 he2
      exact hβb he2.symm
  by_cases h4 : (p, q) = (b, W.σ a)
  · injection h4 with hp hq
    subst p; subst hq
    exact iff_of_true hVw_bα (Or.inr (Or.inl rfl))
  by_cases h5 : (p, q) = (W.σ b, b)
  · injection h5 with hp hq
    subst hp; subst q
    refine iff_of_false hVw_βb ?_
    rintro (⟨hg, -⟩ | he | he)
    · exact hVg_βb hg
    · injection he with he1 he2
      exact hβb he1
    · injection he with he1 he2
      exact hαβ he1.symm
  by_cases h6 : (p, q) = (b, W.σ b)
  · injection h6 with hp hq
    subst p; subst hq
    refine iff_of_false hVw_bβ ?_
    rintro (⟨-, hne⟩ | he | he)
    · exact hne rfl
    · injection he with he1 he2
      exact hαβ he2.symm
    · injection he with he1 he2
      exact hαb he1.symm
  have key := nonspecial hab haact hbact hadj hbA p q h1 h2 h3 h4 h5 h6
  rw [key]
  constructor
  · intro hg
    exact Or.inl ⟨hg, h6⟩
  · rintro (⟨hg, -⟩ | he | he)
    · exact hg
    · exact absurd he h4
    · exact absurd he h1

end Window

end Conj43
