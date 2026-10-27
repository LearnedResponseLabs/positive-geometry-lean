/-
Conj43/SeedTableVerdicts.lean — the §5 transition-table verdicts as pure-ℕ
`Clockwise4` facts under the κ-lift (PAPER_SECTION.tex eqs 8.15–8.32).
Hypothesis pools validated EXHAUSTIVELY as abstract tuples (not just windows) in
checks/scripts/validate_table_abstractions.py: n ≤ 8, 2772 A>b tuples + 336 identity tuples, 0 fails.
Points: entry of a label with entry position `r` at `2r+1`, exit of label `ℓ` at
`2ℓ`; `w`-state entries: α at `a`, β at `b`, b at `c`; `g`-state: α at `b`, β at
`a`, b at `c`. `A,B` are the lifts of `α,β`; `S` the lift of `c`.
-/
import Conj43.SeedTableCore

namespace Conj43

/-- Hypothesis pool for the `A > b` transition table. -/
structure Tab (n a b A B α β : ℕ) : Prop where
  hab : a < b
  hbn : b < n
  hbA : b < A
  hAB : A < B
  hAan : A < a + n
  hBbn : B < b + n
  hBan : B ≤ a + n
  hα : α < n
  hβ : β < n
  hαd : α = A ∨ α + n = A
  hβd : β = B ∨ β + n = B

/-- Entry position `c` of label `b` and its lift `S`. -/
structure TabC (a b n c S : ℕ) : Prop where
  hc : c < n
  hcS : (c < a ∧ S = c + n) ∨ (b < c ∧ S = c)

variable {n a b c S A B α β : ℕ}

/-! ### Shared verdicts: the pair `{α, β}` (eqs 8.19, 8.20) -/

theorem vs_w_ab (h : Tab n a b A B α β) :
    Clockwise4 (2 * n) (2 * a + 1) (2 * b + 1) (2 * α) (2 * β) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem vs_w_ba (h : Tab n a b A B α β) :
    ¬ Clockwise4 (2 * n) (2 * b + 1) (2 * a + 1) (2 * β) (2 * α) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem vs_g_ab (h : Tab n a b A B α β) :
    ¬ Clockwise4 (2 * n) (2 * b + 1) (2 * a + 1) (2 * α) (2 * β) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem vs_g_ba (h : Tab n a b A B α β) :
    ¬ Clockwise4 (2 * n) (2 * a + 1) (2 * b + 1) (2 * β) (2 * α) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

/-! ### Regime-free `b`-pair verdicts (false in all three regimes) -/

theorem v_w_alb (h : Tab n a b A B α β) (hC : TabC a b n c S) :
    ¬ Clockwise4 (2 * n) (2 * a + 1) (2 * c + 1) (2 * α) (2 * b) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_w_bbe (h : Tab n a b A B α β) (hC : TabC a b n c S) :
    ¬ Clockwise4 (2 * n) (2 * c + 1) (2 * b + 1) (2 * b) (2 * β) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_g_bal (h : Tab n a b A B α β) (hC : TabC a b n c S) :
    ¬ Clockwise4 (2 * n) (2 * c + 1) (2 * b + 1) (2 * b) (2 * α) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_g_beb (h : Tab n a b A B α β) (hC : TabC a b n c S) :
    ¬ Clockwise4 (2 * n) (2 * a + 1) (2 * c + 1) (2 * β) (2 * b) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

/-! ### Regime-conditioned `b`-pair verdicts (eqs 8.21–8.32) -/

theorem v_w_beb_lt (h : Tab n a b A B α β) (hC : TabC a b n c S) (hreg : S < B) :
    Clockwise4 (2 * n) (2 * b + 1) (2 * c + 1) (2 * β) (2 * b) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_w_beb_ge (h : Tab n a b A B α β) (hC : TabC a b n c S) (hreg : B ≤ S) :
    ¬ Clockwise4 (2 * n) (2 * b + 1) (2 * c + 1) (2 * β) (2 * b) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_g_alb_lt (h : Tab n a b A B α β) (hC : TabC a b n c S) (hreg : S < A) :
    Clockwise4 (2 * n) (2 * b + 1) (2 * c + 1) (2 * α) (2 * b) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_g_alb_ge (h : Tab n a b A B α β) (hC : TabC a b n c S) (hreg : A ≤ S) :
    ¬ Clockwise4 (2 * n) (2 * b + 1) (2 * c + 1) (2 * α) (2 * b) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_w_bal_lt (h : Tab n a b A B α β) (hC : TabC a b n c S) (hreg : S < A) :
    ¬ Clockwise4 (2 * n) (2 * c + 1) (2 * a + 1) (2 * b) (2 * α) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_w_bal_ge (h : Tab n a b A B α β) (hC : TabC a b n c S) (hreg : A ≤ S) :
    Clockwise4 (2 * n) (2 * c + 1) (2 * a + 1) (2 * b) (2 * α) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_g_bbe_lt (h : Tab n a b A B α β) (hC : TabC a b n c S) (hreg : S < B) :
    ¬ Clockwise4 (2 * n) (2 * c + 1) (2 * a + 1) (2 * b) (2 * β) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem v_g_bbe_ge (h : Tab n a b A B α β) (hC : TabC a b n c S) (hreg : B ≤ S) :
    Clockwise4 (2 * n) (2 * c + 1) (2 * a + 1) (2 * b) (2 * β) := by
  obtain ⟨hab, hbn, hbA, hAB, hAan, hBbn, hBan, hα, hβ, hαd, hβd⟩ := h
  obtain ⟨hc, hcS⟩ := hC
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

/-! ### Identity-case verdicts (`A = b`, eqs 8.15/8.16 and the `b`-pair kills) -/

theorem id_w_bbe (hab : a < b) (hbn : b < n) (hbB : b < B) (hBan : B ≤ a + n)
    (hβ : β < n) (hβd : β = B ∨ β + n = B) :
    ¬ Clockwise4 (2 * n) (2 * a + 1) (2 * b + 1) (2 * b) (2 * β) := by
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem id_w_beb (hab : a < b) (hbn : b < n) (hbB : b < B) (hBan : B ≤ a + n)
    (hβ : β < n) (hβd : β = B ∨ β + n = B) :
    ¬ Clockwise4 (2 * n) (2 * b + 1) (2 * a + 1) (2 * β) (2 * b) := by
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem id_w_bq {s q : ℕ} (hab : a < b) (hbn : b < n) (hs : s < n) (hq : q < n)
    (hsav : s < a ∨ b < s) (hqav : q ≤ a ∨ b < q) :
    ¬ Clockwise4 (2 * n) (2 * a + 1) (2 * s + 1) (2 * b) (2 * q) := by
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

theorem id_w_qb {s q : ℕ} (hab : a < b) (hbn : b < n) (hs : s < n) (hq : q < n)
    (hsav : s < a ∨ b < s) (hqav : q ≤ a ∨ b < q) :
    ¬ Clockwise4 (2 * n) (2 * s + 1) (2 * a + 1) (2 * q) (2 * b) := by
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

end Conj43
