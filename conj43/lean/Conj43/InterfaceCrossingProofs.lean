/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceProofs
import Conj43.InterfaceCrossingDefs
namespace Conj43

private theorem step_formula {m a b : ℕ} (ha : a < m) (hb : b < m) :
    step m a b = if a ≤ b then b-a else b+m-a := by
  unfold step
  split_ifs with h
  · have he : b+m-a = (b-a)+m := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem clockwise_cases {m a b c d : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m) :
    Clockwise4 m a b c d ↔
      (a < b ∧ b < c ∧ c < d) ∨ (b < c ∧ c < d ∧ d < a) ∨
      (c < d ∧ d < a ∧ a < b) ∨ (d < a ∧ a < b ∧ b < c) := by
  unfold Clockwise4
  rw [step_formula ha hb, step_formula hb hc, step_formula hc hd, step_formula hd ha]
  split_ifs <;> omega

private theorem crossing_cases {n : ℕ} (F : LooplessBAP n) (p q : Fin n) :
    CrossEdge F p q ↔
      ((F.σ.symm p : ℕ) < (F.σ.symm q : ℕ) ∧ (F.σ.symm q : ℕ) < p ∧ p < q) ∨
      ((F.σ.symm q : ℕ) < p ∧ p < q ∧ (q : ℕ) ≤ (F.σ.symm p : ℕ)) ∨
      (p < q ∧ (q : ℕ) ≤ (F.σ.symm p : ℕ) ∧ (F.σ.symm p : ℕ) < (F.σ.symm q : ℕ)) ∨
      ((q : ℕ) ≤ (F.σ.symm p : ℕ) ∧ (F.σ.symm p : ℕ) < (F.σ.symm q : ℕ) ∧ (F.σ.symm q : ℕ) < p) := by
  have hs := (F.σ.symm p).isLt
  have ht := (F.σ.symm q).isLt
  have hp := p.isLt
  have hq := q.isLt
  change Clockwise4 (5*n) ((5*(F.σ.symm p : ℕ)+4) % (5*n))
    ((5*(F.σ.symm q : ℕ)+4) % (5*n)) (5*(p : ℕ)+1) (5*(q : ℕ)+1) ↔ _
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    clockwise_cases (by omega) (by omega) (by omega) (by omega)]
  simp only [Fin.lt_def]
  omega

theorem galashin_translate {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p k : ℤ) :
    galashinOf F (p+k*n) = galashinOf F p+k*n := by
  unfold galashinOf
  rw [show p+k*(n : ℤ)-1 = (p-1)+k*n by ring, f_translate hn]
  ring

private def upperLift {n : ℕ} (p q : Fin n) : ℤ :=
  (q : ℤ)+1+if q ≤ p then (n : ℤ) else 0

private def upperInput {n : ℕ} (F : LooplessBAP n) (p q : Fin n) : ℤ :=
  inverseLift F q+1+if q ≤ p then (n : ℤ) else 0

private theorem upper_image {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    galashinOf F (upperInput F p q) = upperLift p q := by
  unfold upperInput upperLift
  split_ifs
  · have ht := galashin_translate hn F (inverseLift F q+1) 1
    simp only [one_mul, galashinOf, add_sub_cancel_right, f_inverseLift hn] at ht
    exact ht
  · simp [galashinOf, f_inverseLift hn]

private theorem crossing_canonical {n : ℕ} (_hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    CrossEdge F p q ↔
      inverseLift F p+1 < upperInput F p q ∧
      upperInput F p q < (p : ℤ)+1 ∧
      (p : ℤ)+1 < upperLift p q ∧ upperLift p q ≤ inverseLift F p+1+n := by
  rw [crossing_cases]
  dsimp [upperLift, upperInput, inverseLift]
  have hp := p.isLt
  have hq := q.isLt
  have hs := (F.σ.symm p).isLt
  have ht := (F.σ.symm q).isLt
  simp only [Fin.lt_def, Fin.le_def]
  split_ifs <;> omega

 theorem crossEdge_iff_affine {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    CrossEdge F p q ↔ ∃ P Q : ℤ,
      Int.ModEq (n : ℤ) P ((p : ℤ) + 1) ∧
      Int.ModEq (n : ℤ) Q ((q : ℤ) + 1) ∧ affineCrossing (galashinOf F) n P Q := by
  constructor
  · intro h
    obtain ⟨hst,htp,hpq,hqs⟩ := (crossing_canonical hn F p q).mp h
    refine ⟨(p : ℤ)+1, upperLift p q, Int.ModEq.refl _, ?_,
      inverseLift F p+1, upperInput F p q, ?_, upper_image hn F p q, hst,htp,hpq,hqs⟩
    · unfold upperLift
      split_ifs <;> simp
    · simp [galashinOf, f_inverseLift hn]
  · rintro ⟨P,Q,hP,hQ,s,t,hs,ht,hst,htP,hPQ,hQs⟩
    obtain ⟨k,hk⟩ := Int.modEq_iff_add_fac.mp hP.symm
    have hsp : galashinOf F (inverseLift F p+1+k*n) = P := by
      rw [galashin_translate hn]
      simp only [galashinOf, add_sub_cancel_right, f_inverseLift hn]
      nlinarith [hk]
    have hse : s = inverseLift F p+1+k*n := (galashin_isLooplessBAP hn F).1.1.1 (hs.trans hsp.symm)
    have hbp := (galashin_isLooplessBAP hn F).2 s
    rw [hs] at hbp
    have hu : (p : ℤ)+1 < upperLift p q ∧ upperLift p q ≤ (p : ℤ)+1+n := by
      have hp := p.isLt
      have hq := q.isLt
      dsimp [upperLift]
      split_ifs <;> simp only [Fin.le_def] at * <;> omega
    have hqe : Q = upperLift p q+k*n := by
      apply interval_unique (l := P) (n := n) ⟨hPQ, by omega⟩
      · constructor <;> nlinarith [hu.1, hu.2, hk]
      · have hmod : Int.ModEq (n : ℤ) (upperLift p q+k*n) ((q : ℤ)+1) := by
          unfold upperLift
          split_ifs <;> simp
        exact hQ.trans hmod.symm
    have hti : galashinOf F (upperInput F p q+k*n) = Q := by
      rw [galashin_translate hn, upper_image hn, hqe]
    have hte : t = upperInput F p q+k*n := (galashin_isLooplessBAP hn F).1.1.1 (ht.trans hti.symm)
    apply (crossing_canonical hn F p q).mpr
    rw [hse,hte] at hst
    rw [hte] at htP
    rw [hqe] at hPQ
    rw [hqe,hse] at hQs
    constructor
    · linarith
    constructor
    · nlinarith [hk]
    constructor
    · nlinarith [hk]
    · linarith
private theorem input_residue {n : ℕ} (hn : 0 < n) (F : LooplessBAP n)
    (a : ℤ) (x : Fin n) (h : (galashinOf F a-1) % (n : ℤ) = (x : ℤ)) :
    (a-1) % (n : ℤ) = (F.σ.symm x : ℤ) := by
  have hm := f_mod hn F (a-1)
  have he : F.σ (residue hn (a-1)) = x := by
    apply Fin.ext
    simp only [galashinOf, add_sub_cancel_right] at h
    rw [hm] at h
    exact_mod_cast h
  have hi := congrArg F.σ.symm he
  simp only [Equiv.symm_apply_apply] at hi
  have hv := congrArg (fun i : Fin n => (i : ℤ)) hi
  rwa [residue_val] at hv

private def windowValue {n : ℕ} (F : LooplessBAP n) (x : Fin n) : ℤ :=
  F.f (F.σ.symm x : ℤ)

private theorem windowValue_eq {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (x : Fin n) :
    windowValue F x = (x : ℤ) + if x ≤ F.σ.symm x then (n : ℤ) else 0 := by
  simp [windowValue, f_window hn]

private theorem windowValue_mod {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (x : Fin n) :
    windowValue F x % (n : ℤ) = (x : ℤ) := by
  simp [windowValue, f_mod hn, residue_fin hn]

private def orientedAlignment {n : ℕ} (g : ℤ → ℤ) (p q : Fin n) : Prop :=
  ∃ s t : ℤ, (1 ≤ s ∧ s ≤ n) ∧ s < t ∧ g t < g s ∧
    (g s-1) % (n : ℤ) = (p : ℤ) ∧ (g t-1) % (n : ℤ) = (q : ℤ)

private theorem oriented_iff {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    orientedAlignment (galashinOf F) p q ↔
      ((F.σ.symm p : ℕ) < (F.σ.symm q : ℕ) ∧ windowValue F q < windowValue F p) ∨
      windowValue F q+n < windowValue F p := by
  have hs := (F.σ.symm p).isLt
  have ht := (F.σ.symm q).isLt
  have hgp : galashinOf F ((F.σ.symm p : ℤ)+1) = windowValue F p+1 := by
    simp [galashinOf, windowValue]
  have hgq : galashinOf F ((F.σ.symm q : ℤ)+1) = windowValue F q+1 := by
    simp [galashinOf, windowValue]
  have hgqn : galashinOf F ((F.σ.symm q : ℤ)+1+n) = windowValue F q+1+n := by
    simpa [hgq] using galashin_translate hn F ((F.σ.symm q : ℤ)+1) 1
  constructor
  · rintro ⟨s,t,hwin,hst,hout,hp,hq⟩
    have hsi := input_residue hn F s p hp
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at hsi
    have hse : s = (F.σ.symm p : ℤ)+1 := by omega
    have hsb := (galashin_isLooplessBAP hn F).1.2.2.2 s
    have htb := (galashin_isLooplessBAP hn F).2 t
    have hti := input_residue hn F t q hq
    have hte : t = (F.σ.symm q : ℤ)+1 ∨ t = (F.σ.symm q : ℤ)+1+n := by
      by_cases hh : t-1 < n
      · left
        rw [Int.emod_eq_of_lt (by omega) hh] at hti
        omega
      · right
        have hi : (t-1-(n : ℤ)) % n = (F.σ.symm q : ℤ) := by simpa using hti
        rw [Int.emod_eq_of_lt (by omega) (by omega)] at hi
        omega
    rcases hte with he | he
    · left
      rw [hse,he] at hst
      rw [hse,he,hgp,hgq] at hout
      constructor <;> omega
    · right
      rw [hse,he,hgp,hgqn] at hout
      omega
  · intro h
    rcases h with ⟨horder,hval⟩ | hval
    · refine ⟨(F.σ.symm p : ℤ)+1,(F.σ.symm q : ℤ)+1, ⟨by omega,by omega⟩,
        by omega, ?_, ?_, ?_⟩
      · rw [hgp,hgq]; omega
      · rw [hgp,add_sub_cancel_right,windowValue_mod hn]
      · rw [hgq,add_sub_cancel_right,windowValue_mod hn]
    · refine ⟨(F.σ.symm p : ℤ)+1,(F.σ.symm q : ℤ)+1+n, ⟨by omega,by omega⟩,
        by omega, ?_, ?_, ?_⟩
      · rw [hgp,hgqn]; omega
      · rw [hgp,add_sub_cancel_right,windowValue_mod hn]
      · rw [hgqn]
        have he : windowValue F q+1+(n : ℤ)-1 = windowValue F q+n := by ring
        rw [he, Int.add_emod_right, windowValue_mod hn]

private theorem alignment_canonical {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    affineAlignment (galashinOf F) p q ↔
      (((F.σ.symm p : ℕ) < (F.σ.symm q : ℕ) ∧ windowValue F q < windowValue F p) ∨
        windowValue F q+n < windowValue F p) ∨
      (((F.σ.symm q : ℕ) < (F.σ.symm p : ℕ) ∧ windowValue F p < windowValue F q) ∨
        windowValue F p+n < windowValue F q) := by
  rw [← oriented_iff hn, ← oriented_iff hn]
  unfold affineAlignment orientedAlignment
  constructor
  · rintro ⟨s,t,hw,ho,hv,h⟩
    rcases h with h | h
    · exact Or.inl ⟨s,t,hw,ho,hv,h⟩
    · exact Or.inr ⟨s,t,hw,ho,hv,h⟩
  · rintro (⟨s,t,hw,ho,hv,h⟩ | ⟨s,t,hw,ho,hv,h⟩)
    · exact ⟨s,t,hw,ho,hv,Or.inl h⟩
    · exact ⟨s,t,hw,ho,hv,Or.inr h⟩

private theorem misUD_cases {n : ℕ} (F : LooplessBAP n) (p q : Fin n) :
    MisUD F p q ↔
      ((F.σ.symm p : ℕ) < p ∧ (p : ℕ) ≤ (F.σ.symm q : ℕ) ∧ (F.σ.symm q : ℕ) < q) ∨
      ((p : ℕ) ≤ (F.σ.symm q : ℕ) ∧ (F.σ.symm q : ℕ) < q ∧ (q : ℕ) ≤ (F.σ.symm p : ℕ)) ∨
      ((F.σ.symm q : ℕ) < q ∧ (q : ℕ) ≤ (F.σ.symm p : ℕ) ∧ (F.σ.symm p : ℕ) < p) ∨
      ((q : ℕ) ≤ (F.σ.symm p : ℕ) ∧ (F.σ.symm p : ℕ) < p ∧ (p : ℕ) ≤ (F.σ.symm q : ℕ)) := by
  have hs := (F.σ.symm p).isLt
  have ht := (F.σ.symm q).isLt
  have hp := p.isLt
  have hq := q.isLt
  change Clockwise4 (5*n) ((5*(F.σ.symm p : ℕ)+4) % (5*n))
    (5*(p : ℕ)+1) ((5*(F.σ.symm q : ℕ)+4) % (5*n)) (5*(q : ℕ)+1) ↔ _
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    clockwise_cases (by omega) (by omega) (by omega) (by omega)]
  omega

private theorem misDU_cases {n : ℕ} (F : LooplessBAP n) (p q : Fin n) :
    MisDU F p q ↔
      ((p : ℕ) ≤ (F.σ.symm p : ℕ) ∧ (F.σ.symm q : ℕ) < p ∧ (q : ℕ) ≤ (F.σ.symm q : ℕ)) ∨
      ((F.σ.symm q : ℕ) < p ∧ (q : ℕ) ≤ (F.σ.symm q : ℕ) ∧ (F.σ.symm p : ℕ) < q) ∨
      ((q : ℕ) ≤ (F.σ.symm q : ℕ) ∧ (F.σ.symm p : ℕ) < q ∧ (p : ℕ) ≤ (F.σ.symm p : ℕ)) ∨
      ((F.σ.symm p : ℕ) < q ∧ (p : ℕ) ≤ (F.σ.symm p : ℕ) ∧ (F.σ.symm q : ℕ) < p) := by
  have hs := (F.σ.symm p).isLt
  have ht := (F.σ.symm q).isLt
  have hp := p.isLt
  have hq := q.isLt
  change Clockwise4 (5*n) (negPos (5*n) ((5*(F.σ.symm p : ℕ)+4) % (5*n)))
    (negPos (5*n) (5*(p : ℕ)+1)) (negPos (5*n) ((5*(F.σ.symm q : ℕ)+4) % (5*n)))
    (negPos (5*n) (5*(q : ℕ)+1)) ↔ _
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold negPos
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    clockwise_cases (by omega) (by omega) (by omega) (by omega)]
  omega

set_option maxHeartbeats 600000 in
 theorem alignment_iff_affine {n : ℕ} (hn : 0 < n) (F : LooplessBAP n)
    (p q : Fin n) (hpq : p ≠ q) :
    (¬ CrossEdge F p q ∧ ¬ CrossEdge F q p ∧ ¬ MisUD F p q ∧ ¬ MisDU F p q) ↔
      affineAlignment (galashinOf F) p q := by
  have hs := (F.σ.symm p).isLt
  have ht := (F.σ.symm q).isLt
  have hp := p.isLt
  have hq := q.isLt
  have hst : F.σ.symm p ≠ F.σ.symm q := fun h => hpq (F.σ.symm.injective h)
  simp only [ne_eq, Fin.ext_iff] at hpq hst
  rw [crossing_cases, crossing_cases, misUD_cases, misDU_cases, alignment_canonical hn]
  rw [windowValue_eq hn, windowValue_eq hn]
  simp only [Fin.lt_def, Fin.le_def]
  by_cases h1 : (p : ℕ) < q <;>
    by_cases h2 : (F.σ.symm p : ℕ) < (F.σ.symm q : ℕ) <;>
    by_cases h3 : (p : ℕ) ≤ (F.σ.symm p : ℕ) <;>
    by_cases h4 : (q : ℕ) ≤ (F.σ.symm q : ℕ) <;>
    by_cases h5 : (q : ℕ) ≤ (F.σ.symm p : ℕ) <;>
    by_cases h6 : (F.σ.symm q : ℕ) < p <;>
    simp only [h1,h2,h3,h4,h5,h6, if_pos, if_neg, and_true, and_false,
      true_and, false_and, or_true, or_false, true_or, false_or, not_true_eq_false,
      not_false_eq_true] <;> first | omega | (simp only [false_iff, not_or, not_and]; omega)

end Conj43
