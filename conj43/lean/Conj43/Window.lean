/-
Conj43/Window.lean — L3B window-induction layer (part 1: encoding + bridge).

Generalized crossing edges over an arbitrary residue permutation (fixed points
allowed), in the compact 2n-point ε-resolved encoding (exit `2r`, entry `2r+1`),
matching an exact table audit (script not included). The pinned `crossEdges F` lives in the 5n
encoding; `gcross_iff_cross` proves the two agree on every pair (both cut to the
same linear order via `cw4_iff_linear`, then `omega`). Windows carry the integer
lift `w` used by the measure/ascent/κ-lift machinery of later parts.
-/
import Conj43.CyclicArc
import Conj43.Winding

namespace Conj43

variable {n : ℕ}

/-! ### Generalized directed crossing edges (2n encoding) -/

/-- Directed crossing edge `p → q` of a residue permutation `σ` (fixed points
allowed): entry of `p`, entry of `q`, exit of `p`, exit of `q` clockwise on the
`2n`-point circle, entry of label `ℓ` at `2·σ⁻¹ℓ+1`, exit at `2·ℓ`. -/
def GCross (σ : Equiv.Perm (Fin n)) (p q : Fin n) : Prop :=
  Clockwise4 (2 * n) (2 * (σ⁻¹ p : ℕ) + 1) (2 * (σ⁻¹ q : ℕ) + 1)
    (2 * (p : ℕ)) (2 * (q : ℕ))

instance (σ : Equiv.Perm (Fin n)) (p q : Fin n) : Decidable (GCross σ p q) := by
  unfold GCross; infer_instance

/-- The generalized crossing-edge set of a residue permutation. -/
def GEdgeSet (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => GCross σ e.1 e.2)

theorem mem_GEdgeSet {σ : Equiv.Perm (Fin n)} {e : Fin n × Fin n} :
    e ∈ GEdgeSet σ ↔ GCross σ e.1 e.2 := by
  unfold GEdgeSet; simp [Finset.mem_filter]

/-! ### Bridge to the pinned 5n-encoding `CrossEdge` -/

/-- The pinned `entryPos` reduction: the `% (5n)` is inert (`5·s+4 < 5n`). -/
theorem entryPos_reduce (F : LooplessBAP n) (x : Fin n) :
    entryPos F x = 5 * (F.σ⁻¹ x : ℕ) + 4 := by
  unfold entryPos
  have hlt : (F.σ⁻¹ x : ℕ) < n := (F.σ⁻¹ x).isLt
  exact Nat.mod_eq_of_lt (by omega)

/-- **Bridge.** The 2n-encoding `GCross` and the pinned 5n-encoding `CrossEdge`
define the same directed crossing edges. -/
theorem gcross_iff_cross (F : LooplessBAP n) (p q : Fin n) :
    GCross F.σ p q ↔ CrossEdge F p q := by
  have hn : 0 < n := by have := p.isLt; omega
  have hsp : (F.σ⁻¹ p : ℕ) < n := (F.σ⁻¹ p).isLt
  have hsq : (F.σ⁻¹ q : ℕ) < n := (F.σ⁻¹ q).isLt
  have hp : (p : ℕ) < n := p.isLt
  have hq : (q : ℕ) < n := q.isLt
  unfold GCross CrossEdge
  rw [entryPos_reduce, entryPos_reduce]
  unfold exitPos
  rw [cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega),
      cw4_iff_linear (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega

/-- Membership form of the bridge, at the level of edge sets. -/
theorem mem_GEdgeSet_iff_cross (F : LooplessBAP n) (e : Fin n × Fin n) :
    e ∈ GEdgeSet F.σ ↔ CrossEdge F e.1 e.2 := by
  rw [mem_GEdgeSet, gcross_iff_cross]

/-! ### Windows: the decorated bounded lift -/

/-- A decorated bounded window: residues form the permutation `σ`, the lift `w`
sits in `[i, i+n]`. Fixed positions (`σ i = i`) carry a decoration `w i ∈ {i,i+n}`;
active positions have `i < w i < i+n`. -/
structure Window (n : ℕ) where
  σ : Equiv.Perm (Fin n)
  w : Fin n → ℕ
  hres : ∀ i : Fin n, w i % n = (σ i : ℕ)
  hlb : ∀ i : Fin n, (i : ℕ) ≤ w i
  hub : ∀ i : Fin n, w i ≤ (i : ℕ) + n

namespace Window

variable (W : Window n)

/-- Window lift values are pairwise distinct integers. -/
theorem w_inj {i j : Fin n} (h : W.w i = W.w j) : i = j := by
  have hi := W.hres i; have hj := W.hres j
  rw [h] at hi
  have : (W.σ i : ℕ) = (W.σ j : ℕ) := by rw [← hi, hj]
  have hij : W.σ i = W.σ j := Fin.ext this
  exact W.σ.injective hij

/-- Position `i` is ACTIVE when `σ i ≠ i`. -/
@[reducible] def Active (i : Fin n) : Prop := W.σ i ≠ i

/-- Active positions have a strict lift `i < w i < i + n`. -/
theorem active_strict {i : Fin n} (h : W.Active i) :
    (i : ℕ) < W.w i ∧ W.w i < (i : ℕ) + n := by
  have hlb := W.hlb i
  have hub := W.hub i
  have h' : W.σ i ≠ i := h
  have hne : W.w i % n ≠ (i : ℕ) := by
    rw [W.hres i]; intro hc; exact h' (Fin.ext hc)
  have h1 : W.w i ≠ (i : ℕ) := by
    intro hc; apply hne; rw [hc]; exact Nat.mod_eq_of_lt i.isLt
  have h2 : W.w i ≠ (i : ℕ) + n := by
    intro hc; apply hne; rw [hc, Nat.add_mod_right]; exact Nat.mod_eq_of_lt i.isLt
  omega

/-- Fixed positions carry a decoration `w i = i` or `w i = i + n`. -/
theorem fixed_decoration {i : Fin n} (h : ¬ W.Active i) :
    W.w i = (i : ℕ) ∨ W.w i = (i : ℕ) + n := by
  have hn : 0 < n := by have := i.isLt; omega
  have hfix : W.σ i = i := not_not.mp h
  have hres := W.hres i
  rw [hfix] at hres
  have hlb := W.hlb i
  have hub := W.hub i
  have hi : (i : ℕ) < n := i.isLt
  -- w i = n·(w i / n) + i, and i ≤ w i ≤ i+n ⟹ the multiplier is 0 or 1
  have hdm : n * (W.w i / n) + W.w i % n = W.w i := Nat.div_add_mod (W.w i) n
  rw [hres] at hdm
  set d := W.w i / n with hd
  have hdle : n * d ≤ n := by omega
  have hd1 : d ≤ 1 := by
    by_contra hc
    have : n * 2 ≤ n * d := Nat.mul_le_mul (Nat.le_refl n) (by omega)
    omega
  interval_cases d <;> omega

end Window

end Conj43
