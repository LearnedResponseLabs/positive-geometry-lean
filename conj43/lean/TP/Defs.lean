/- Ordered-minor and network interfaces. Mathematical sources: Postnikov §§2–5,
   Lusztig §2. LeanLGV definitions are reused through the pinned source link;
   its original Apache-2.0 notices are preserved at that source. -/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import LGV.Quiver.Network

noncomputable section
open scoped BigOperators
namespace TP

abbrev Subset (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

def index {n k : ℕ} (s : Subset n k) (i : Fin k) : Fin n :=
  s.1.orderIsoOfFin s.2 i

def minor {R : Type*} [CommRing R] {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (I : Subset m k) (J : Subset n k) : R :=
  (A.submatrix (index I) (index J)).det

def TotallyNonneg {R : Type*} [CommRing R] [PartialOrder R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ k (I : Subset m k) (J : Subset n k), 0 ≤ minor A I J

def TotallyPos {R : Type*} [CommRing R] [PartialOrder R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ k (I : Subset m k) (J : Subset n k), 0 < minor A I J

def jacobiX {R : Type*} [DecidableEq R] [CommRing R] {n : ℕ}
    (i : Fin n) (a : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  1 + Matrix.of (fun r c => if r = i.castSucc ∧ c = i.succ then a else 0)

def jacobiY {R : Type*} [DecidableEq R] [CommRing R] {n : ℕ}
    (i : Fin n) (a : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  (jacobiX i a).transpose

def IsGenerator {R : Type*} [DecidableEq R] [CommRing R] [PartialOrder R]
    {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) R) : Prop :=
  (∃ i a, 0 ≤ a ∧ A = jacobiX i a) ∨
  (∃ i a, 0 ≤ a ∧ A = jacobiY i a) ∨
  (∃ d : Fin (n+1) → R, (∀ i, 0 < d i) ∧ A = Matrix.diagonal d)

/-- The decreasing rank is an explicit acyclicity witness. Parallel arrows allowed. -/
structure Network (R V : Type*) [Quiver V] where
  rank : V → ℕ
  decreases : ∀ {a b : V}, (a ⟶ b) → rank b < rank a
  weight : ∀ {a b : V}, (a ⟶ b) → R

def Network.endpoints {R V : Type*} [Quiver V] (N : Network R V)
    {k : ℕ} (s t : Fin k → V) : LGV.RankedQuiverNetwork R V (Fin k) where
  source := s
  sink := t
  rank := N.rank
  rank_decreases := N.decreases
  edgeWeight := N.weight

def Nonpermutable {R V : Type*} [CommRing R] [Quiver V] [Fintype V]
    [DecidableEq V] [∀ a b : V, Fintype (a ⟶ b)] {k : ℕ}
    (N : LGV.RankedQuiverNetwork R V (Fin k)) : Prop :=
  ∀ f : N.toFinitePathNetwork.SignedPathFamily, N.SignedVertexDisjoint f → f.1 = 1

def Network.pathMatrix {R V : Type*} [CommRing R] [Quiver V] [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)] (N : Network R V)
    {m n : ℕ} (s : Fin m → V) (t : Fin n → V) : Matrix (Fin m) (Fin n) R :=
  fun i j => (N.endpoints (fun _ : Fin 1 => s i) (fun _ => t j)).pathSum 0 0

/-- All ordered endpoint restrictions are nonpermutable. This is a combinatorial
    hypothesis, not a formal topological planarity assertion. -/
def OrderedNonpermutable {R V : Type*} [CommRing R] [Quiver V] [Fintype V]
    [DecidableEq V] [∀ a b : V, Fintype (a ⟶ b)] (N : Network R V)
    {m n : ℕ} (s : Fin m → V) (t : Fin n → V) : Prop :=
  ∀ k (I : Subset m k) (J : Subset n k),
    Nonpermutable (N.endpoints (s ∘ index I) (t ∘ index J))

/-- Alternation of two chords in the cyclic order induced by the finite line. -/
def Crosses {n : ℕ} (a b c d : Fin n) : Prop :=
  (min a b < min c d ∧ min c d < max a b ∧ max a b < max c d) ∨
  (min c d < min a b ∧ min a b < max c d ∧ max c d < max a b)

instance {n : ℕ} (a b c d : Fin n) : Decidable (Crosses a b c d) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)))

structure BoundaryNetwork (R V : Type*) [Quiver V] (n k : ℕ) extends Network R V where
  boundary : Fin n → V
  boundary_injective : Function.Injective boundary
  sources : Subset n k
  no_incoming : ∀ i ∈ sources.1, ∀ v, IsEmpty (v ⟶ boundary i)
  no_outgoing : ∀ i ∉ sources.1, ∀ v, IsEmpty (boundary i ⟶ v)

/-- Chords with alternating endpoints force an intersection of directed paths. -/
def BoundaryNetwork.CrossingObstruction {R V : Type*} [Quiver V] [DecidableEq V]
    {n k : ℕ} (N : BoundaryNetwork R V n k) : Prop :=
  ∀ a ∈ N.sources.1, ∀ c ∈ N.sources.1, ∀ b ∉ N.sources.1, ∀ d ∉ N.sources.1,
    Crosses a b c d → ∀ (p : Quiver.Path (N.boundary a) (N.boundary b))
      (q : Quiver.Path (N.boundary c) (N.boundary d)),
        ¬ LGV.RankedQuiverNetwork.VertexDisjoint p q

/-- Number of sources strictly between the two boundary labels in the linear order. -/
def sourceBetween {n k : ℕ} (I : Subset n k) (a b : Fin n) : ℕ :=
  (I.1.filter fun x => min a b < x ∧ x < max a b).card

/-- Source columns are the identity; remaining entries carry the boundary sign. -/
def boundaryMatrix {R V : Type*} [CommRing R] [Quiver V] [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)] {n k : ℕ} (N : BoundaryNetwork R V n k) :
    Matrix (Fin k) (Fin n) R := fun r j =>
  if j ∈ N.sources.1 then (if index N.sources r = j then 1 else 0)
  else (-1 : R) ^ sourceBetween N.sources (index N.sources r) j *
    N.toNetwork.pathMatrix (N.boundary ∘ index N.sources) N.boundary r j

def maxMinor {R : Type*} [CommRing R] {n k : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (J : Finset (Fin n)) : R :=
  if h : J.card = k then (A.submatrix id (index ⟨J,h⟩)).det else 0

def crossingNumber {n r : ℕ} (K L : Subset n r) (σ : Equiv.Perm (Fin r)) : ℕ :=
  (Finset.univ.filter fun ij : Fin r × Fin r => ij.1 < ij.2 ∧
    Crosses (index K ij.1) (index L (σ ij.1)) (index K ij.2) (index L (σ ij.2))).card

/-- Schur complement of the leading 1-by-1 block, with residual indices in order. -/
def pivotSchur {R : Type*} [Field R] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => A i.succ j.succ - A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ
end TP
