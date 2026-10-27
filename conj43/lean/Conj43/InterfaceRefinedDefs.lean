/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceCrossingDefs
namespace Conj43

/-! ### Definitions (to be frozen in `Conj43/InterfaceRefinedDefs.lean`) -/

/-- Galashin's refined boundary (Def. 1.5), 0-based, on a circle of `2n` points: the exit point `x⁻` at `2x`,
followed clockwise by the entry point `x⁺` at `2x + 1`. -/
def refinedExit (x : ℕ) : ℕ := 2 * x

/-- The entry point `x⁺` of label `x` on the refined circle. -/
def refinedEntry (x : ℕ) : ℕ := 2 * x + 1

/-- `pt ∈ J(u⁺, v⁻)`: the refined points met moving clockwise from `u⁺`, excluding `u⁺` and including `v⁻`. -/
def InRefinedArc (n u v pt : ℕ) : Prop :=
  0 < step (2 * n) (refinedEntry u) pt ∧
    step (2 * n) (refinedEntry u) pt ≤ step (2 * n) (refinedEntry u) (refinedExit v)

/-- `r ∈ (u, v]`, the cyclic half-open integer arc of `[n]`, with `(u, u]` the whole of `[n]`. -/
def InHalfOpen (n u v r : ℕ) : Prop :=
  u = v ∨ (0 < step n u r ∧ step n u r ≤ step n u v)

/-- A refined point as a label with a flag (`true` for its entry point), in the `5n` position encoding of
`Defs.lean` (`exitPos x = 5x + 1`, `entryPos = 5s + 4`). -/
def pos5 {n : ℕ} (x : Fin n × Bool) : ℕ := 5 * (x.1 : ℕ) + (if x.2 then 4 else 1)

/-- The same refined point on the `2n`-point circle. -/
def pos2 {n : ℕ} (x : Fin n × Bool) : ℕ := 2 * (x.1 : ℕ) + (if x.2 then 1 else 0)

/-- Galashin's `{p, q} ∈ Mis↑↓_f` (§5.4, before Prop. 5.12): with `s = f̄⁻¹(p)` and `t = f̄⁻¹(q)`, the points
`b⁺_s, b⁻_p, b⁺_t, b⁻_q` occur clockwise. `g` is his 1-based affine permutation; for the 0-based label `s`,
`f̄(s)` is read off as `(g (s + 1) − 1) mod n`. -/
def galashinMisUD {n : ℕ} (g : ℤ → ℤ) (p q : Fin n) : Prop :=
  ∃ s t : Fin n, (g ((s : ℤ) + 1) - 1) % (n : ℤ) = (p : ℤ) ∧ (g ((t : ℤ) + 1) - 1) % (n : ℤ) = (q : ℤ) ∧
    Clockwise4 (2 * n) (refinedEntry s) (refinedExit p) (refinedEntry t) (refinedExit q)

/-- Galashin's `{p, q} ∈ Mis↓↑_f`: the same four points occur counterclockwise. -/
def galashinMisDU {n : ℕ} (g : ℤ → ℤ) (p q : Fin n) : Prop :=
  ∃ s t : Fin n, (g ((s : ℤ) + 1) - 1) % (n : ℤ) = (p : ℤ) ∧ (g ((t : ℤ) + 1) - 1) % (n : ℤ) = (q : ℤ) ∧
    Clockwise4 (2 * n) (refinedExit q) (refinedEntry t) (refinedExit p) (refinedEntry s)

/-- `(p, q) ∈ E(G^×_f)`, Galashin's (5.7): `p` and `q` form a positive f-crossing, on residues. -/
def galashinCross {n : ℕ} (g : ℤ → ℤ) (p q : Fin n) : Prop :=
  ∃ P Q : ℤ, Int.ModEq (n : ℤ) P ((p : ℤ) + 1) ∧ Int.ModEq (n : ℤ) Q ((q : ℤ) + 1) ∧
    affineCrossing g n P Q

/-- The exponent of `[[t_q, t_p]]₊` on the face label `I` in Galashin's (5.8): `+1` from the `Mis↑↓` product
when `p, q ∈ I`, `+1` from the `Mis↓↑` product when `p, q ∉ I`, and `−1` from the inverted product over
directed crossings with tail in `I` and head out, in either orientation. -/
noncomputable def galashinExponent {n : ℕ} (g : ℤ → ℤ) (I : Finset (Fin n)) (p q : Fin n) : ℤ := by
  classical
  exact (if galashinMisUD g p q ∧ p ∈ I ∧ q ∈ I then 1 else 0)
    + (if galashinMisDU g p q ∧ p ∉ I ∧ q ∉ I then 1 else 0)
    - (if galashinCross g p q ∧ p ∈ I ∧ q ∉ I then 1 else 0)
    - (if galashinCross g q p ∧ q ∈ I ∧ p ∉ I then 1 else 0)


end Conj43
