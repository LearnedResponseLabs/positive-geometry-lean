/- SPDX-License-Identifier: Apache-2.0 -/
import TP.NecklaceDefs

/-! # Deleting a loop of a bounded affine permutation: definitions (to be frozen in `TP/LoopDeleteDefs.lean`)

Conventions of `BddAffPerm`: period `N`, window `[0, N)`, `i ≤ f i ≤ i + N`. A loop is a window position `p` with
`f p = p` (a black fixed point of the decorated permutation). Deleting the loop at `p` from a period-`n + 1`
permutation leaves a period-`n` one, whose window is the old window without `p`. -/

namespace TP

/-- The KLS length of a period-`n` function: pairs `0 ≤ i < n`, `1 ≤ d < n` with `f (i + d) < f i`. For a bounded
affine permutation every inversion `i < j`, `f j < f i` with `0 ≤ i < n` has `j < i + n`, so this is `ℓ(f)`. -/
def affLength (n : ℕ) (f : ℤ → ℤ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter fun x => 0 < x.2 ∧ f ((x.1 : ℤ) + x.2) < f x.1).card

/-- The rank `k = (1 / n) ∑_{i < n} (f i - i)` of a period-`n` bounded affine permutation. -/
def affRank (n : ℕ) (f : ℤ → ℤ) : ℤ :=
  (∑ i ∈ Finset.range n, (f i - i)) / n

/-- Closing the gap left by the residue class of `p` modulo `n + 1`, in order: `q (n + 1) + r ↦ q n + r` for `r < p`,
and `q n + (r - 1)` for `r > p`. -/
def dropPos (n p : ℕ) (x : ℤ) : ℤ :=
  x / (n + 1) * n + (if x % (n + 1) < p then x % (n + 1) else x % (n + 1) - 1)

/-- Its inverse: `q n + s ↦ q (n + 1) + s` for `s < p`, and `q (n + 1) + s + 1` for `s ≥ p`. -/
def liftPos (n p : ℕ) (y : ℤ) : ℤ :=
  y / n * (n + 1) + (if y % n < p then y % n else y % n + 1)

/-- The function of period `n` left by deleting the loop at window position `p` of a period-`n + 1` function `f`:
`y ↦ dropPos (f (liftPos y))`. -/
def deleteLoopFun (n p : ℕ) (f : ℤ → ℤ) : ℤ → ℤ :=
  fun y => dropPos n p (f (liftPos n p y))

end TP
