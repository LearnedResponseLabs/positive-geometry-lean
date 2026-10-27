/-
Conj43/Defs.lean — L0 definitional layer for the Conj 4.3 interior spine.

Semantics arbiter: an exact-ℚ census of the crossing and necklace construction (a script not included in this archive).
Paper: main.tex of the accompanying paper (sec:setup, prop:rowdiff).

Pinned index conventions:
* Lean labels are 0-based `Fin n`; census labels are 1-based: label_py = label_lean + 1.
* Necklace row r : Fin n is the paper's I_{r+1} (row 0 = I_1).
* "Clockwise" (paper) = strictly increasing position order on the ε-resolved
  circle ℤ/5n, census-verbatim: exit b⁻_x at 5x+1, entry b⁺_{s_x} at 5·s_x+4
  (0-based x, s_x = σ⁻¹ x); within a boundary block the exit precedes the entry.
* Edge columns are restricted to crossing pairs and sorted lexicographically by
  (tail, head) — census `sorted(directed)`. (The paper's M_N nominally has all
  unordered-pair columns; non-crossing columns are zero, census drops them. In
  particular every pair meeting a coloop is dropped: a coloop carries no
  crossing, `not_crossEdge_of_coloop`.)
* L4 (2026-09-15) widening: `LooplessBAP` is LOOP-free only. A fixed point of σ
  is a coloop (f(i) = i+n), not a loop. See `Conj43/Coloop.lean`.
-/
import Mathlib

namespace Conj43

/-- A **loopless** bounded affine permutation of type (k,n), represented by its
induced window permutation σ = ā on `Fin n`. Loops `f(i) = i` are excluded by
the encoding convention: a fixed point of σ is read as a **coloop**,
`f(i) = i + n` (L4 widening, 2026-09-15). This is exactly Galashin's hypothesis
in Conjecture 4.3 — loopless f may have coloops — and matches the paper's
`sec:reduction`/`prop:rowdiff`, which are stated with coloops allowed. The
fixed-point-free core (derangements of [n], the census cell enumeration) is the
sub-family `∀ i, F.σ i ≠ i`. -/
structure LooplessBAP (n : ℕ) where
  σ : Equiv.Perm (Fin n)

variable {n : ℕ}

/-- A label `p` is a **coloop**: `ā(p) = p`, equivalently `f(p) = p + n`. -/
def IsColoop (F : LooplessBAP n) (p : Fin n) : Prop := F.σ p = p

instance (F : LooplessBAP n) (p : Fin n) : Decidable (IsColoop F p) := by
  unfold IsColoop; infer_instance

/-- The bounded affine permutation f : ℤ → ℤ itself: the unique lift of σ with
f(i+n) = f(i)+n and `i < f(i) ≤ i+n` — strict on the right exactly away from
coloops (paper: "x' − s ≤ n is strict exactly when x is not a coloop"). The
`+1`/`−1` shift of the residue puts the representative in `{1,…,n}` rather than
`{0,…,n−1}`, which is what makes a fixed point of σ a coloop and not a loop. -/
def LooplessBAP.f (F : LooplessBAP n) (i : ℤ) : ℤ :=
  if h : 0 < n then
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast h
    have hlt : (i % (n : ℤ)).toNat < n := by
      have h1 : 0 ≤ i % (n : ℤ) := Int.emod_nonneg i hn.ne'
      have h2 : i % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos i hn
      omega
    i + 1 + (((F.σ ⟨(i % (n : ℤ)).toNat, hlt⟩ : ℕ) - i - 1) % (n : ℤ))
  else i

/-- Rank k of the cell: the number of anti-exceedances σ(i) ≤ i, a coloop
counting as one (its strand contributes a full turn, f(i) = i+n).
Equals the cardinality of every necklace term I_r. -/
def rank (F : LooplessBAP n) : ℕ :=
  (Finset.univ.filter fun i => F.σ i ≤ i).card

/-! ### The ε-resolved boundary circle (census-verbatim, modulus 5n) -/

/-- Position of the entry endpoint b⁺_{s_x} of the strand with exit label x
(census `entry`): 5·s_x + 4 mod 5n, s_x = σ⁻¹ x. -/
def entryPos (F : LooplessBAP n) (x : Fin n) : ℕ :=
  (5 * (F.σ⁻¹ x : ℕ) + 4) % (5 * n)

/-- Position of the exit endpoint b⁻_x of label x (census `exit_`): 5x + 1. -/
def exitPos (x : Fin n) : ℕ := 5 * (x : ℕ) + 1

/-- One clockwise step from a to b on ℤ/m (census step `(b - a) % modulus`). -/
def step (m a b : ℕ) : ℕ := (b + m - a) % m

/-- Four points occur in this strict clockwise cyclic order, wrapping exactly
once (census `cyclic`: all steps positive, steps sum to the modulus). -/
def Clockwise4 (m a b c d : ℕ) : Prop :=
  0 < step m a b ∧ 0 < step m b c ∧ 0 < step m c d ∧ 0 < step m d a ∧
    step m a b + step m b c + step m c d + step m d a = m

instance (m a b c d : ℕ) : Decidable (Clockwise4 m a b c d) := by
  unfold Clockwise4; infer_instance

/-- Reflected position (census `(-value) % modulus`). -/
def negPos (m v : ℕ) : ℕ := (m - v) % m

/-! ### Pair classes (Galashin §5.4; census `endpoint_classes`) -/

/-- Mis^{↑↓}: b⁺_{s_p}, b⁻_p, b⁺_{s_q}, b⁻_q clockwise (census `updown`;
census normalizes to p < q before testing). -/
def MisUD (F : LooplessBAP n) (p q : Fin n) : Prop :=
  Clockwise4 (5 * n) (entryPos F p) (exitPos p) (entryPos F q) (exitPos q)

instance (F : LooplessBAP n) (p q : Fin n) : Decidable (MisUD F p q) := by
  unfold MisUD; infer_instance

/-- Mis^{↓↑}: the same four points counterclockwise, census-verbatim as the
reflected tuple being clockwise (census `downup`). Census computes this in an
`elif` after `updown`; the two orders are geometrically exclusive, so the
unguarded definition agrees (cross-validated). -/
def MisDU (F : LooplessBAP n) (p q : Fin n) : Prop :=
  Clockwise4 (5 * n) (negPos (5 * n) (entryPos F p)) (negPos (5 * n) (exitPos p))
    (negPos (5 * n) (entryPos F q)) (negPos (5 * n) (exitPos q))

instance (F : LooplessBAP n) (p q : Fin n) : Decidable (MisDU F p q) := by
  unfold MisDU; infer_instance

/-- Directed crossing edge p → q: the ε-resolved endpoints occur clockwise as
b⁺_{s_p}, b⁺_{s_q}, b⁻_p, b⁻_q (paper sec:setup; census `directed`). Defined on
ordered pairs; the census tests each unordered pair both ways, same edge set. -/
def CrossEdge (F : LooplessBAP n) (p q : Fin n) : Prop :=
  Clockwise4 (5 * n) (entryPos F p) (entryPos F q) (exitPos p) (exitPos q)

instance (F : LooplessBAP n) (p q : Fin n) : Decidable (CrossEdge F p q) := by
  unfold CrossEdge; infer_instance

/-- The directed crossing-edge list, sorted lexicographically by (tail, head)
(census `directed_edges = sorted(directed)`; sort order is +1-shift invariant). -/
def crossEdges (F : LooplessBAP n) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun p =>
    (List.finRange n).filterMap fun q =>
      if CrossEdge F p q then some (p, q) else none

/-! ### Grassmann necklace (census `grassmann_necklace`, verbatim recursion) -/

/-- I₁ = {x : s_x ≥ x} (census `rows[0]` is the strict `>`; the non-strict form
is the L4 widening — a coloop has s_x = x and, by Galashin's affine formula
`I_r = {f(a) mod n : a < r ≤ f(a)}` with `f(x) = x + n`, lies in EVERY necklace
row, cf. paper eq:arc "A_x is then the whole row set"). The two agree on the
fixed-point-free core. -/
def necklaceFirst (F : LooplessBAP n) : Finset (Fin n) :=
  Finset.univ.filter fun x => (x : ℕ) ≤ (F.σ⁻¹ x : ℕ)

/-- Necklace recursion: row j (0-based) is I_{j+1}; the step from row i to row
i+1 removes 0-based label i and inserts σ(i), guarded by membership
(census: `(prior - {i}) | {permutation[i-1]} if i in prior else prior`).
For loopless f the guard always holds (r ∈ I_r — including at a coloop r, where
r ∈ I_r for every r and the step is the identity since σ r = r), so this matches
the paper's unconditional I_{r+1} = (I_r \ {r}) ∪ {f(r)}. -/
def necklaceAux (F : LooplessBAP n) : ℕ → Finset (Fin n)
  | 0 => necklaceFirst F
  | i + 1 =>
    let prior := necklaceAux F i
    if h : i < n then
      let lab : Fin n := ⟨i, h⟩
      if lab ∈ prior then insert (F.σ lab) (prior.erase lab) else prior
    else prior

/-- The Grassmann necklace: `necklace F r` is the paper's I_{r+1}. -/
def necklace (F : LooplessBAP n) (r : Fin n) : Finset (Fin n) :=
  necklaceAux F r

/-! ### The four matrices of prop:rowdiff -/

/-- Column index into the crossing-edge list. -/
abbrev EdgeIdx (F : LooplessBAP n) := Fin (crossEdges F).length

/-- The j-th directed crossing edge (tail, head). -/
def edgeOf (F : LooplessBAP n) (j : EdgeIdx F) : Fin n × Fin n :=
  (crossEdges F).get j

/-- Galashin Prop 5.12 twisted-Plücker exponent of the unordered pair
underlying e at necklace row r — census `exponent_column` verbatim:
+1 for Mis^{↑↓} with both labels in I_{r+1}, +1 for Mis^{↓↑} with both
absent, −1 for a directed crossing with tail in and head out (at most one
crossing orientation holds; census stores the oriented pair once). -/
def pairExponent (F : LooplessBAP n) (r : Fin n) (e : Fin n × Fin n) : ℤ :=
  let p := min e.1 e.2
  let q := max e.1 e.2
  let I := necklace F r
  (if MisUD F p q ∧ p ∈ I ∧ q ∈ I then 1 else 0)
    + (if MisDU F p q ∧ p ∉ I ∧ q ∉ I then 1 else 0)
    - (if CrossEdge F p q ∧ p ∈ I ∧ q ∉ I then 1 else 0)
    - (if CrossEdge F q p ∧ q ∈ I ∧ p ∉ I then 1 else 0)

/-- Necklace exponent matrix M_N, rows = necklace positions (row r = I_{r+1}),
columns = crossing pairs in census order. -/
def Mmat (F : LooplessBAP n) : Matrix (Fin n) (EdgeIdx F) ℤ :=
  Matrix.of fun r j => pairExponent F r (edgeOf F j)

/-- Directed incidence matrix B of G_f^x: column e = (tail, head) is
e_head − e_tail (census `incidence`: −1 at tail, +1 at head). -/
def Bmat (F : LooplessBAP n) : Matrix (Fin n) (EdgeIdx F) ℤ :=
  Matrix.of fun r j =>
    (if r = (edgeOf F j).2 then 1 else 0) - (if r = (edgeOf F j).1 then 1 else 0)

/-- Cyclic forward row-difference: (Dz)_r = z_{r+1} − z_r, index cyclic mod n
(census `np.roll(M, -1, axis=0) - M`). -/
def Dmat (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r s => (if s = r + 1 then 1 else 0) - (if s = r then 1 else 0)

/-- Necklace relabeling: (P_f z)_x = z_{s_x}, s_x = σ⁻¹ x (census
`relabeled[label-1] = cyclic_difference[inverse[label]-1]`). -/
def Pmat (F : LooplessBAP n) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun x s => if s = F.σ⁻¹ x then 1 else 0

/-- Exit-advance of a directed edge p→q: (q − p) mod n, valued in {1,…,n−1}
for p ≠ q (paper `adv`; 0-based labels, shift-invariant). -/
def adv {n : ℕ} (p q : Fin n) : ℕ := ((q : ℕ) + n - (p : ℕ)) % n

/-- The directed edges traversed by a cycle given as its vertex list
(consecutive pairs, including the closing edge last → first). -/
def cycleEdges {n : ℕ} (c : List (Fin n)) : List (Fin n × Fin n) :=
  c.zip (c.rotate 1)

/-- Total exit-advance around a vertex list (winding number × n). -/
def winding {n : ℕ} (c : List (Fin n)) : ℕ :=
  ((cycleEdges c).map fun e => adv e.1 e.2).sum

/-- Copy of the pinned `cycleEdges`. -/
def cycleEdgesD {n : ℕ} (c : List (Fin n)) : List (Fin n × Fin n) := c.zip (c.rotate 1)

/-- The directed edges a subset `S` contributes as a winding-one cycle. -/
def consecutiveEdges (S : Finset (Fin n)) : List (Fin n × Fin n) :=
  cycleEdgesD (S.sort (· ≤ ·))

end Conj43
