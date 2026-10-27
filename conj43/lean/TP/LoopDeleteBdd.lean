/- SPDX-License-Identifier: Apache-2.0 -/
import TP.LoopDeleteBasic

/-! # Deleting a loop leaves a bounded affine permutation -/

namespace TP
namespace LoopDelete

/-- A function with `g (i + N) = g i + N` commutes with every integer multiple of `N`. -/
lemma per_int {N : ℤ} {g : ℤ → ℤ} (h : ∀ i, g (i + N) = g i + N) (i t : ℤ) :
    g (i + N * t) = g i + N * t := by
  induction t using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : i + N * ((k : ℤ) + 1) = (i + N * k) + N := by ring
    rw [this, h, ih]; ring
  | pred k ih =>
    have h1 := h (i + N * (-(k : ℤ) - 1))
    have : i + N * (-(k : ℤ) - 1) + N = i + N * (-(k : ℤ)) := by ring
    rw [this, ih] at h1
    linarith

/-- The shifted form of periodicity of a `BddAffPerm (n + 1)`. -/
lemma BddAffPerm.perSucc {n : ℕ} (g : BddAffPerm (n + 1)) (i : ℤ) : g.f (i + ((n : ℤ) + 1)) = g.f i + ((n : ℤ) + 1) := by
  have := g.periodic i
  push_cast at this
  exact this

/-- A loop fixes its whole residue class. -/
lemma loop_class {n : ℕ} (g : BddAffPerm (n + 1)) {p : ℕ} (hp : g.f (p : ℕ) = (p : ℕ)) (x : ℤ)
    (hx : x % ((n : ℤ) + 1) = p) : g.f x = x := by
  have hx' := Int.mul_ediv_add_emod x ((n : ℤ) + 1)
  have := per_int (BddAffPerm.perSucc g) (p : ℤ) (x / ((n : ℤ) + 1))
  rw [hp] at this
  rw [hx] at hx'
  have e : x = (p : ℤ) + ((n : ℤ) + 1) * (x / ((n : ℤ) + 1)) := by linarith
  rw [e]; exact this

/-- An integer lies in the loop's class iff its image does. -/
lemma loop_mod_iff {n : ℕ} (g : BddAffPerm (n + 1)) {p : ℕ} (hpn : p < n + 1) (hp : g.f (p : ℕ) = (p : ℕ))
    (x : ℤ) : g.f x % ((n : ℤ) + 1) = p ↔ x % ((n : ℤ) + 1) = p := by
  have hN : (0 : ℤ) < (n : ℤ) + 1 := by omega
  have hpn' : (p : ℤ) < (n : ℤ) + 1 := by exact_mod_cast hpn
  constructor
  · intro h
    have h1 := Int.mul_ediv_add_emod (g.f x) ((n : ℤ) + 1)
    rw [h] at h1
    have h2 := per_int (BddAffPerm.perSucc g) (p : ℤ) (g.f x / ((n : ℤ) + 1))
    rw [hp] at h2
    have h3 : g.f x = g.f ((p : ℤ) + ((n : ℤ) + 1) * (g.f x / ((n : ℤ) + 1))) := by rw [h2]; linarith
    have h4 := g.bijective.1 h3
    rw [h4]
    have := (divmod_of (N := (n : ℤ) + 1) (q := g.f x / ((n : ℤ) + 1)) (t := p) hN
      (x := (p : ℤ) + ((n : ℤ) + 1) * (g.f x / ((n : ℤ) + 1))) (by ring) (by omega) hpn')
    exact this.2
  · intro h
    rw [loop_class g hp x h]; exact h

end LoopDelete

open LoopDelete

/-- **Deleting a loop leaves a bounded affine permutation** of period `n`. -/
theorem deleteLoop_bdd {n : ℕ} (hn : 0 < n) (g : BddAffPerm (n + 1)) (p : Fin (n + 1))
    (hp : g.f (p : ℕ) = (p : ℕ)) :
    Function.Bijective (deleteLoopFun n p g.f) ∧
      (∀ i, deleteLoopFun n p g.f (i + n) = deleteLoopFun n p g.f i + n) ∧
      (∀ i, i ≤ deleteLoopFun n p g.f i) ∧ (∀ i, deleteLoopFun n p g.f i ≤ i + n) := by
  have hpn : (p : ℕ) < n + 1 := p.isLt
  have hiff := loop_mod_iff g hpn hp
  have key : ∀ y, deleteLoopFun n p g.f y = dropPos n p (g.f (liftPos n p y)) := fun y => rfl
  have nonp : ∀ y, g.f (liftPos n p y) % ((n : ℤ) + 1) ≠ p := fun y h =>
    liftPos_mod_ne hn y ((hiff _).1 h)
  have onback : ∀ x, x % ((n : ℤ) + 1) ≠ p → deleteLoopFun n p g.f (dropPos n p x) = dropPos n p (g.f x) := by
    intro x hx
    rw [key, liftPos_dropPos hn hpn hx]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a b hab
    rw [key, key] at hab
    have h1 := dropPos_injOn hn hpn (nonp a) (nonp b) hab
    have h2 := g.bijective.1 h1
    exact (show StrictMono (liftPos n (p : ℕ)) from fun _ _ h => liftPos_strictMono hn h).injective h2
  · intro y
    obtain ⟨x, hx⟩ := g.bijective.2 (liftPos n p y)
    have hxn : x % ((n : ℤ) + 1) ≠ p := fun h => liftPos_mod_ne hn y (by rw [← hx]; exact (hiff x).2 h)
    refine ⟨dropPos n p x, ?_⟩
    rw [onback x hxn, hx, dropPos_liftPos hn]
  · intro i
    rw [key, key, liftPos_add hn, BddAffPerm.perSucc, dropPos_add hn]
  · intro y
    have hx := nonp y
    have h1 := g.self_le (liftPos n p y)
    have hy : y = dropPos n p (liftPos n p y) := (dropPos_liftPos hn y).symm
    rw [key]
    conv_lhs => rw [hy]
    exact (dropPos_le_iff hn hpn (liftPos_mod_ne hn y) hx).2 h1
  · intro y
    have hx := nonp y
    have h1 := g.le_add (liftPos n p y)
    have hy : dropPos n p (liftPos n p y) = y := dropPos_liftPos hn y
    have hxN : (liftPos n p y + ((n : ℤ) + 1)) % ((n : ℤ) + 1) ≠ p := by
      rw [Int.add_emod_right]; exact liftPos_mod_ne hn y
    have h2 : g.f (liftPos n p y) ≤ liftPos n p y + ((n : ℤ) + 1) := by exact_mod_cast (by push_cast at h1; exact h1)
    rw [key]
    have := (dropPos_le_iff hn hpn hx hxN).2 h2
    rw [dropPos_add hn, hy] at this
    exact this

end TP
