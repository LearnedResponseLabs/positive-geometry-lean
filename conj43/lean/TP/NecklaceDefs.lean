/- Apache-2.0. Positroid combinatorics: frozen definitions only.
   Sources: Postnikov, arXiv:math/0609764 (v1), Definition 16.1, Lemmas 16.2 and 16.3,
   Remark 3.3; Galashin, arXiv:2102.13339 (v2), Section 2.1 (bounded affine permutations).
   Labels are zero-based: row `r` of a necklace is the source's `I_{r+1}`, and the
   cyclic successor of `r` is `finRotate n r`. -/
import Mathlib
import TP.Defs

namespace TP

variable {n : ℕ}

/-- Position of `i` in the cyclic order `r <_r r+1 <_r ⋯ <_r r-1` (zero-based). -/
def cycPos (r i : Fin n) : ℕ := ((i : ℕ) + n - (r : ℕ)) % n

/-! ### Grassmann necklaces (Definition 16.1) -/

/-- Definition 16.1: if `r ∈ I r` then `I (r+1) = (I r \ {r}) ∪ {j}` for some `j`;
if `r ∉ I r` then `I (r+1) = I r`. -/
def IsNecklace (I : Fin n → Finset (Fin n)) : Prop :=
  ∀ r : Fin n,
    (r ∈ I r → ∃ j : Fin n, I (finRotate n r) = insert j ((I r).erase r)) ∧
    (r ∉ I r → I (finRotate n r) = I r)

/-! ### Decorated permutations (Definition 13.3, Lemma 16.2) -/

/-- A decorated permutation. Fixed points in `white` are white (colour −1, coloops);
the other fixed points are black (colour 1, loops). -/
structure DecPerm (n : ℕ) where
  perm : Equiv.Perm (Fin n)
  white : Finset (Fin n)
  white_fixed : ∀ i ∈ white, perm i = i

/-- No black fixed point: every fixed point is white. -/
def DecPerm.LoopFree (π : DecPerm n) : Prop :=
  ∀ i, π.perm i = i → i ∈ π.white

/-- Anti-exceedances in the usual order: `π⁻¹(i) > i`, or `i` a white fixed point. -/
def DecPerm.antiExc (π : DecPerm n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (i : ℕ) < (π.perm⁻¹ i : ℕ) ∨ i ∈ π.white

/-- Shifted anti-exceedance sets: `necklaceOf π r` is the source's `I_{r+1}(π)`,
the set of `i` with `i <_r π⁻¹(i)` or `i` a white fixed point. -/
def necklaceOf (π : DecPerm n) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => cycPos r i < cycPos r (π.perm⁻¹ i) ∨ i ∈ π.white

/-- Inverse map, permutation part: `π(r) = j` when `I (r+1) \ I r = {j}`, and `π(r) = r`
when `I (r+1) \ I r` is empty. -/
def necklacePerm (I : Fin n → Finset (Fin n)) (r : Fin n) : Fin n :=
  if h : (I (finRotate n r) \ I r).Nonempty then (I (finRotate n r) \ I r).min' h else r

/-- Inverse map, colour part: `r` is a white fixed point when `r ∈ I r` and
`I (r+1) = I r`. -/
def necklaceWhite (I : Fin n → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun r => r ∈ I r ∧ I (finRotate n r) = I r

/-! ### Lexicographic minima, matroid necklaces, Gale order (Lemma 16.3) -/

/-- `L` is lexicographically minimal in the family `F` for `<_r`: whenever a member `B`
has an element `x ∉ L`, some `y ∈ L \ B` comes before `x`. (Equivalently, the
`<_r`-first element of `L ∆ B` lies in `L`; on sets of equal size this is the
lexicographic order of the `<_r`-sorted sequences.) -/
def IsLexMin (F : Finset (Fin n) → Prop) (r : Fin n) (L : Finset (Fin n)) : Prop :=
  F L ∧ ∀ B, F B → ∀ x ∈ B, x ∉ L → ∃ y ∈ L, y ∉ B ∧ cycPos r y < cycPos r x

/-- The lexicographically minimal member of `F` for `<_r` (`∅` if there is none). -/
noncomputable def lexMin (F : Finset (Fin n) → Prop) (r : Fin n) : Finset (Fin n) :=
  open Classical in if h : ∃ L, IsLexMin F r L then h.choose else ∅

/-- The lexicographically minimal base of `M` for `<_r`. -/
noncomputable def lexMinBase (M : Matroid (Fin n)) (r : Fin n) : Finset (Fin n) :=
  lexMin (fun B => M.IsBase (B : Set (Fin n))) r

/-- Gale order for `<_r`: the two sets, sorted in `<_r`, compare componentwise. -/
def GaleLE (r : Fin n) (A B : Finset (Fin n)) : Prop :=
  List.Forall₂ (· ≤ ·) ((A.image (cycPos r)).sort (· ≤ ·)) ((B.image (cycPos r)).sort (· ≤ ·))

/-! ### Cyclic symmetry (Remark 3.3) -/

/-- Twisted cyclic shift: new column `i` is old column `i+1`; new column `n-1` is
`(-1)^(k-1)` times old column `0`. -/
def twShift {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin n) R) :
    Matrix (Fin k) (Fin n) R :=
  Matrix.of fun a i => (if (i : ℕ) + 1 = n then (-1 : R) ^ (k - 1) else 1) * A a (finRotate n i)

/-- Rotation of a column set, `J ↦ J + 1`. -/
def rotateSet (J : Finset (Fin n)) : Finset (Fin n) := J.map (finRotate n).toEmbedding

/-- The necklace of a matrix: for each `r`, the lexicographically minimal column set
with nonzero maximal minor. -/
noncomputable def matrixNecklace {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (r : Fin n) : Finset (Fin n) :=
  lexMin (fun J => maxMinor A J ≠ 0) r

/-! ### Bounded affine permutations (Galashin §2.1; stretch) -/

/-- A bounded affine permutation of period `n` (KLS): a bijection `f : ℤ → ℤ` with
`f(i+n) = f(i)+n` and `i ≤ f(i) ≤ i+n`. -/
structure BddAffPerm (n : ℕ) where
  f : ℤ → ℤ
  bijective : Function.Bijective f
  periodic : ∀ i, f (i + n) = f i + n
  self_le : ∀ i, i ≤ f i
  le_add : ∀ i, f i ≤ i + n

/-- The decorated permutation of a bounded affine permutation: `π(i) ≡ f(i) mod n`;
`f(i) = i + n` is a white fixed point, `f(i) = i` a black one. -/
def BddAffPerm.toFun (g : BddAffPerm n) (i : Fin n) : Fin n :=
  ⟨(g.f ((i : ℕ) : ℤ) % (n : ℤ)).toNat, by
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have h1 : 0 ≤ g.f ((i : ℕ) : ℤ) % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    have h2 : g.f ((i : ℕ) : ℤ) % (n : ℤ) < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
    omega⟩

/-- The affine lift of a decorated permutation on the window `[0, n)`:
`π(i)` if `π(i) > i`, `π(i) + n` if `π(i) < i`, `i + n` at a white and `i` at a black
fixed point. -/
def DecPerm.windowLift (π : DecPerm n) (i : Fin n) : ℤ :=
  if (i : ℕ) < (π.perm i : ℕ) then ((π.perm i : ℕ) : ℤ)
  else if (π.perm i : ℕ) < (i : ℕ) then ((π.perm i : ℕ) : ℤ) + n
  else if i ∈ π.white then ((i : ℕ) : ℤ) + n else ((i : ℕ) : ℤ)

end TP
