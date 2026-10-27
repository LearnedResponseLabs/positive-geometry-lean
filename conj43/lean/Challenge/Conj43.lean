/- Frozen component statements. Proof placeholders belong only to this challenge.
   The eleven declarations are the union of Statements.lean and axioms.lean.
   Existence of a partition does not assert uniqueness or the homeomorphism. -/
import Conj43.Defs

namespace Conj43

variable {n : ℕ}

theorem cot_cycle_inequality (m : ℕ) (hm : 3 ≤ m) (α d : Fin m → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = Real.pi) (hd : ∑ i, d i = 0) :
    0 ≤ ∑ i, Real.cot (α i) * d i ^ 2 ∧
      ((∑ i, Real.cot (α i) * d i ^ 2) = 0 ↔ ∀ i, d i = 0) := by sorry

theorem rowdiff (n : ℕ) [NeZero n] (F : LooplessBAP n) :
    Pmat F * Dmat n * Mmat F = Bmat F := by sorry

theorem crossEdges_subset_cover (n : ℕ) (F : LooplessBAP n) :
    ∃ Ss : List (Finset (Fin n)),
      (∀ S ∈ Ss, 3 ≤ S.card) ∧
      (Ss.flatMap consecutiveEdges).Perm (crossEdges F) := by sorry

theorem winding_one_partition (n : ℕ) (F : LooplessBAP n) :
    ∃ cycles : List (List (Fin n)),
      (∀ c ∈ cycles, 3 ≤ c.length ∧ c.Nodup ∧ winding c = n) ∧
      (cycles.flatMap cycleEdges).Perm (crossEdges F) := by sorry

theorem not_crossEdge_of_coloop_fst (F : LooplessBAP n) {p q : Fin n}
    (hp : IsColoop F p) : ¬ CrossEdge F p q := by sorry

theorem coloop_mem_necklace (F : LooplessBAP n) {p : Fin n} (hp : IsColoop F p)
    (r : Fin n) : p ∈ necklace F r := by sorry

theorem Bmat_coloop_row (F : LooplessBAP n) {p : Fin n} (hp : IsColoop F p)
    (j : EdgeIdx F) : Bmat F p j = 0 := by sorry

theorem PDM_coloop_row [NeZero n] (F : LooplessBAP n) {p : Fin n}
    (hp : IsColoop F p) (j : EdgeIdx F) :
    (Pmat F * Dmat n * Mmat F) p j = 0 := by sorry

theorem pairExponent_nonCross (F : LooplessBAP n) (p q r : Fin n)
    (hpq : ¬ CrossEdge F p q) (hqp : ¬ CrossEdge F q p) :
    pairExponent F r (p, q) = 0 := by sorry

theorem full_pair_columns_zero (n : ℕ) [NeZero n] (F : LooplessBAP n)
    (e : {e : Fin n × Fin n // e.1 < e.2})
    (hpq : ¬ CrossEdge F e.val.1 e.val.2)
    (hqp : ¬ CrossEdge F e.val.2 e.val.1) :
    let M : Matrix (Fin n) {e : Fin n × Fin n // e.1 < e.2} ℤ :=
      fun r j => pairExponent F r j.val
    let B : Matrix (Fin n) {e : Fin n × Fin n // e.1 < e.2} ℤ :=
      fun x j => if CrossEdge F j.val.1 j.val.2 then
        (if x = j.val.2 then 1 else 0) - (if x = j.val.1 then 1 else 0)
      else if CrossEdge F j.val.2 j.val.1 then
        (if x = j.val.1 then 1 else 0) - (if x = j.val.2 then 1 else 0)
      else 0
    (∀ r, M r e = 0) ∧ (∀ x, (Pmat F * Dmat n * M) x e = 0) ∧
      (∀ x, B x e = 0) := by sorry

theorem rowdiff_full_pairs (n : ℕ) [NeZero n] (F : LooplessBAP n) :
    let M : Matrix (Fin n) {e : Fin n × Fin n // e.1 < e.2} ℤ :=
      fun r j => pairExponent F r j.val
    let B : Matrix (Fin n) {e : Fin n × Fin n // e.1 < e.2} ℤ :=
      fun x j => if CrossEdge F j.val.1 j.val.2 then
        (if x = j.val.2 then 1 else 0) - (if x = j.val.1 then 1 else 0)
      else if CrossEdge F j.val.2 j.val.1 then
        (if x = j.val.1 then 1 else 0) - (if x = j.val.2 then 1 else 0)
      else 0
    Pmat F * Dmat n * M = B := by sorry

/-! Definition equations expose all project vocabulary reachable from these
statements. Standard logical, list, finite-set and matrix operations retain
Mathlib's meanings. LooplessBAP stores only a permutation; fixed points represent
coloops. These examples freeze equations, not merely the predicate names. -/

example (F : LooplessBAP n) : LooplessBAP.mk F.σ = F := rfl

example (F : LooplessBAP n) (p : Fin n) : IsColoop F p ↔ F.σ p = p := Iff.rfl

example (m a b : ℕ) : step m a b = (b + m - a) % m := rfl

example (m a b c d : ℕ) : Clockwise4 m a b c d ↔
    0 < step m a b ∧ 0 < step m b c ∧ 0 < step m c d ∧ 0 < step m d a ∧
      step m a b + step m b c + step m c d + step m d a = m := Iff.rfl

example (F : LooplessBAP n) (x : Fin n) :
    entryPos F x = (5 * (F.σ⁻¹ x : ℕ) + 4) % (5 * n) := rfl

example (x : Fin n) : exitPos x = 5 * (x : ℕ) + 1 := rfl

example (m v : ℕ) : negPos m v = (m - v) % m := rfl

example (F : LooplessBAP n) (p q : Fin n) : MisUD F p q ↔
    Clockwise4 (5 * n) (entryPos F p) (exitPos p) (entryPos F q) (exitPos q) := Iff.rfl

example (F : LooplessBAP n) (p q : Fin n) : MisDU F p q ↔
    Clockwise4 (5 * n) (negPos (5 * n) (entryPos F p)) (negPos (5 * n) (exitPos p))
      (negPos (5 * n) (entryPos F q)) (negPos (5 * n) (exitPos q)) := Iff.rfl

example (F : LooplessBAP n) (p q : Fin n) : CrossEdge F p q ↔
    Clockwise4 (5 * n) (entryPos F p) (entryPos F q) (exitPos p) (exitPos q) := Iff.rfl

example (F : LooplessBAP n) : crossEdges F =
    (List.finRange n).flatMap (fun p => (List.finRange n).filterMap
      (fun q => if CrossEdge F p q then some (p, q) else none)) := rfl

example (F : LooplessBAP n) : necklaceFirst F =
    Finset.univ.filter (fun x : Fin n => (x : ℕ) ≤ (F.σ⁻¹ x : ℕ)) := rfl

example (F : LooplessBAP n) : necklaceAux F 0 = necklaceFirst F := rfl

example (F : LooplessBAP n) (i : ℕ) : necklaceAux F (i + 1) =
    (let prior := necklaceAux F i
     if h : i < n then
       let lab : Fin n := ⟨i, h⟩
       if lab ∈ prior then insert (F.σ lab) (prior.erase lab) else prior
     else prior) := rfl

example (F : LooplessBAP n) (r : Fin n) : necklace F r = necklaceAux F r := rfl

example (F : LooplessBAP n) : EdgeIdx F = Fin (crossEdges F).length := rfl

example (F : LooplessBAP n) (j : EdgeIdx F) : edgeOf F j = (crossEdges F).get j := rfl

example (F : LooplessBAP n) (r : Fin n) (e : Fin n × Fin n) : pairExponent F r e =
    (let p := min e.1 e.2
     let q := max e.1 e.2
     let I := necklace F r
     (if MisUD F p q ∧ p ∈ I ∧ q ∈ I then 1 else 0)
       + (if MisDU F p q ∧ p ∉ I ∧ q ∉ I then 1 else 0)
       - (if CrossEdge F p q ∧ p ∈ I ∧ q ∉ I then 1 else 0)
       - (if CrossEdge F q p ∧ q ∈ I ∧ p ∉ I then 1 else 0)) := rfl

example (F : LooplessBAP n) : Mmat F =
    Matrix.of (fun r j => pairExponent F r (edgeOf F j)) := rfl

example (F : LooplessBAP n) : Bmat F =
    Matrix.of (fun r j => (if r = (edgeOf F j).2 then 1 else 0) -
      (if r = (edgeOf F j).1 then 1 else 0)) := rfl

example (n : ℕ) [NeZero n] : Dmat n =
    Matrix.of (fun r s => (if s = r + 1 then 1 else 0) - (if s = r then 1 else 0)) := rfl

example (F : LooplessBAP n) : Pmat F =
    Matrix.of (fun x s => if s = F.σ⁻¹ x then 1 else 0) := rfl

example (p q : Fin n) : adv p q = ((q : ℕ) + n - (p : ℕ)) % n := rfl

example (c : List (Fin n)) : cycleEdges c = c.zip (c.rotate 1) := rfl

example (c : List (Fin n)) : winding c =
    ((cycleEdges c).map (fun e => adv e.1 e.2)).sum := rfl

example (c : List (Fin n)) : cycleEdgesD c = c.zip (c.rotate 1) := rfl

example (S : Finset (Fin n)) : consecutiveEdges S =
    cycleEdgesD (S.sort (· ≤ ·)) := rfl

end Conj43

/- Append-only L5 challenges. New vocabulary is expanded here so these
statements still import only the existing definitional layer. -/
namespace Conj43
variable {n : ℕ}

theorem cycle_wrap_sum (c : List (Fin n)) (hlen : 3 ≤ c.length)
    (hw : winding c = n) :
    ((cycleEdges c).map fun e => if e.2 < e.1 then (1 : ℝ) else 0).sum = 1 := by sorry

theorem delta_cycle_sum (θ : Fin n → ℝ) (c : List (Fin n))
    (hlen : 3 ≤ c.length) (_hnodup : c.Nodup) (hw : winding c = n) :
    ((cycleEdges c).map fun e =>
      θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)).sum = Real.pi := by sorry

theorem hessian_psd (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : ∀ p q, CrossEdge F p q →
      let d := θ q - θ p + Real.pi * (if q < p then 1 else 0)
      0 < d ∧ d < Real.pi) (h : Fin n → ℝ) :
    let Q := ((crossEdges F).map fun e =>
      Real.cot (θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) *
        (h e.2 - h e.1)^2).sum
    0 ≤ Q ∧ (Q = 0 ↔ ∀ p q, CrossEdge F p q → h p = h q) := by sorry

theorem hessian_kernel_components (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : ∀ p q, CrossEdge F p q →
      let d := θ q - θ p + Real.pi * (if q < p then 1 else 0)
      0 < d ∧ d < Real.pi) (h : Fin n → ℝ) :
    ((crossEdges F).map fun e =>
      Real.cot (θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) *
        (h e.2 - h e.1)^2).sum = 0 ↔
    ∀ p q, Relation.ReflTransGen (fun a b => CrossEdge F a b ∨ CrossEdge F b a) p q →
      h p = h q := by sorry

theorem hessian_matrix_form (F : LooplessBAP n) (θ h : Fin n → ℝ) :
    let B : Matrix (Fin n) (EdgeIdx F) ℝ := fun r j => (Bmat F r j : ℝ)
    let w := fun j => Real.cot (θ (edgeOf F j).2 - θ (edgeOf F j).1 +
      Real.pi * (if (edgeOf F j).2 < (edgeOf F j).1 then 1 else 0))
    dotProduct h ((B * Matrix.diagonal w * B.transpose).mulVec h) =
      ((crossEdges F).map fun e =>
        Real.cot (θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) *
          (h e.2 - h e.1)^2).sum := by sorry

theorem hessian_matrix_kernel (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : ∀ p q, CrossEdge F p q →
      let d := θ q - θ p + Real.pi * (if q < p then 1 else 0)
      0 < d ∧ d < Real.pi) (h : Fin n → ℝ) :
    let B : Matrix (Fin n) (EdgeIdx F) ℝ := fun r j => (Bmat F r j : ℝ)
    let w := fun j => Real.cot (θ (edgeOf F j).2 - θ (edgeOf F j).1 +
      Real.pi * (if (edgeOf F j).2 < (edgeOf F j).1 then 1 else 0))
    (B * Matrix.diagonal w * B.transpose).mulVec h = 0 ↔
      ∀ p q, Relation.ReflTransGen (fun a b => CrossEdge F a b ∨ CrossEdge F b a) p q →
        h p = h q := by sorry

theorem hinge_identity (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : ∀ p q, CrossEdge F p q →
      let d := θ q - θ p + Real.pi * (if q < p then 1 else 0)
      0 < d ∧ d < Real.pi) (p q : Fin n) (he : CrossEdge F p q) :
    let t := fun j => Complex.exp (Complex.I * (θ j : ℂ))
    ‖(if q < p then t p / t q - t q / t p else t q / t p - t p / t q)‖ =
      2 * Real.sin (θ q - θ p + Real.pi * (if q < p then 1 else 0)) := by sorry

end Conj43

/-! Layer 6 frozen calculus and composition statements. -/
namespace Conj43
variable {n : ℕ}

theorem logSinPrimitive_derivative (u : ℝ) (hu : 0 < u) (huπ : u < Real.pi) :
    HasDerivAt (fun u => ∫ t in (Real.pi / 2)..u, Real.log (Real.sin t)) (Real.log (Real.sin u)) u ∧
    HasStrictDerivAt (fun u => ∫ t in (Real.pi / 2)..u, Real.log (Real.sin t)) (Real.log (Real.sin u)) u := by
  sorry

theorem admissible_isOpen (F : LooplessBAP n) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    IsOpen {θ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi)} := by
  sorry

theorem potential_gradient (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    HasFDerivAt Ψ (∑ r, G θ r • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) r)) θ ∧ HasStrictFDerivAt Ψ (∑ r, G θ r • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) r)) θ := by
  sorry

theorem gradient_hessian (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let H := (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))) * Matrix.diagonal (fun j => Real.cot (δ θ (edgeOf F j))) * (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).transpose
    HasFDerivAt G (ContinuousLinearMap.pi (fun r => ∑ s, H r s • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) s))) θ ∧ HasStrictFDerivAt G (ContinuousLinearMap.pi (fun r => ∑ s, H r s • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) s))) θ ∧
      ∀ h, dotProduct h (H.mulVec h) = ((crossEdges F).map fun e => Real.cot (δ θ e) * (h e.2 - h e.1)^2).sum := by
  sorry

theorem incidence_degree_balance (F : LooplessBAP n) :
    (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun _ => 1) = 0 := by
  sorry

theorem gradient_component_shifts (F : LooplessBAP n) (θ s : Fin n → ℝ)
    (hs : ∀ p q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → s p = s q) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    G (θ + s) = G θ := by
  sorry

theorem gradient_edge_constant (F : LooplessBAP n) (θ : Fin n → ℝ) (c : ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j))) + c) = G θ := by
  sorry

theorem hessian_gauge_positive (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) (h : Fin n → ℝ)
    (hh : ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → h p = 0) (hne : h ≠ 0) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    0 < ((crossEdges F).map fun e => Real.cot (δ θ e) * (h e.2 - h e.1)^2).sum := by
  sorry

theorem potential_slice_strictConvex (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    StrictConvexOn ℝ S Ψ := by
  sorry

theorem gradient_slice_strictMonotone (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 0 < dotProduct (G y - G x) (y-x) := by
  sorry

theorem gradient_slice_injective (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    Set.InjOn G S := by
  sorry

/-- The original gradient is a homeomorphism onto its image in the ambient coordinate space.
Openness is proved internally for the gradient with anchor coordinates deleted;
no identification with the incidence range is asserted by this statement. -/
theorem gradient_slice_embedding (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    Topology.IsEmbedding (fun θ : S => G θ.val) := by
  sorry

theorem potential_variational_inverse (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∀ x ∈ S, ∀ z ∈ S, Ψ x - dotProduct (G x) x ≤ Ψ z - dotProduct (G x) z ∧
      (Ψ z - dotProduct (G x) z = Ψ x - dotProduct (G x) x ↔ z = x) := by
  sorry

/-- Conditional end-to-end theorem. X is the ambient space, Crit its critical subset.
hMeas: continuity of measurement (Galashin Proposition 5.1 and admissible extension).
honto: gauge surjectivity (Galashin Proposition 4.2 and the sentence following (4.3)).
hR: continuity of logarithmic twisted necklace coordinates (Muller--Speyer twist and nonvanishing).
hcompat: the assembled identity R composed with Meas equals G (paper Proposition grad),
whose external monomial input is Galashin Proposition 5.12. This identity remains an
explicit hypothesis; the twist and the measurement map are not constructed in Lean.
No properness, coercivity, inverse-continuity, or dimension hypothesis is assumed. -/
theorem measurement_conditional_homeomorphism (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} [TopologicalSpace X] (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (R : Crit → (Fin n → ℝ))
    (hMeas : Continuous Meas) (honto : Function.Surjective Meas)
    (hR : Continuous R) (hcompat : ∀ θ, R (Meas θ) = (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j))))) θ.val) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∃ g : S ≃ₜ Set.range (fun θ : S => G θ.val), (∀ θ, (g θ).val = G θ.val) ∧
      ∃ e : S ≃ₜ Crit, (∀ θ, e θ = Meas θ) ∧
        ∀ z, ∃ hz : R z ∈ Set.range (fun θ : S => G θ.val), e.symm z = g.symm ⟨R z, hz⟩ := by
  sorry

/-- The codomain is the literal real incidence image, with the subspace topology. -/
theorem gradient_incidence_openEmbedding (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    let W := LinearMap.range (Matrix.toLin' (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))))
    ∃ g : S → W, (∀ θ, (g θ).val = G θ.val) ∧ Topology.IsOpenEmbedding g := by
  sorry

theorem variational_image_minimizer (F : LooplessBAP n) (a : Fin n → ℝ) :
    let δ := (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0))
    let Ψ := (fun θ : Fin n → ℝ => ∑ j : EdgeIdx F, ∫ t in (Real.pi / 2)..(δ θ (edgeOf F j)), Real.log (Real.sin t))
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin (δ θ (edgeOf F j)))))
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < δ θ (p,q) ∧ δ θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    ∀ y ∈ G '' S, ∃! x, x ∈ S ∧ ∀ z ∈ S, Ψ x - dotProduct y x ≤ Ψ z - dotProduct y z := by
  sorry

end Conj43

/-! Layer 7 frozen necklace log statements. -/
namespace Conj43
variable {n : ℕ}

/-- All unordered pairs occur on the left; Mis and other non-crossing exponents
vanish formally, before any row differences. -/
theorem necklace_log_crossing (F : LooplessBAP n) (θ : Fin n → ℝ) :
    (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ = (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Mmat F r j : ℝ))).mulVec (fun j => (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ (edgeOf F j)) := by
  sorry

theorem necklace_recovery_constant [NeZero n] (F : LooplessBAP n) (z : Fin n → ℝ) (c : ℝ) :
    (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (z + fun _ => c) = (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) z := by
  sorry

theorem necklace_log_hinge (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) (j : EdgeIdx F) :
    (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ (edgeOf F j) = Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j))) + Real.log 2 := by
  sorry

theorem necklace_log_gradient [NeZero n] (F : LooplessBAP n) (θ : Fin n → ℝ)
    (hθ : (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi)) :
    (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) ((fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ) = (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j))))) θ := by
  sorry

/-- hlog: Galashin Proposition 5.12, equation (5.8), restricted to necklace
rows after log absolute value and a common projective scalar. Includes the
admissible collision extension; zero-exponent pairs use the totalized log. -/
theorem gal512_gradient [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (N : Crit → (Fin n → ℝ))
    (hlog : ∀ θ, ∃ c : ℝ, N (Meas θ) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) :
    ∀ θ, (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (N (Meas θ)) = (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j))))) θ.val := by
  sorry

theorem gal512_recovery_incidence [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (N : Crit → (Fin n → ℝ))
    (honto : Function.Surjective Meas)
    (hlog : ∀ θ, ∃ c : ℝ, N (Meas θ) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) :
    ∀ z, (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (N z) ∈ LinearMap.range (Matrix.toLin' (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ)))) := by
  sorry

/-- hMeas: Galashin Proposition 5.1 and Theorem 6.9 (admissible measurement).
honto: Galashin Proposition 4.2 and gauge surjectivity following (4.3).
hN: Muller--Speyer twist regularity on the open cell and nonzero necklace
coordinates, with a continuous choice of logarithmic representatives.
hlog: Galashin Proposition 5.12, equation (5.8), on necklace rows, including
the admissible collision extension, up to a common projective log scalar.
The identity R composed with Meas equals G is derived internally. -/
theorem gal512_measurement_homeomorphism [NeZero n] (F : LooplessBAP n) (a : Fin n → ℝ)
    {X : Type*} [TopologicalSpace X] (Crit : Set X)
    (Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit) (N : Crit → (Fin n → ℝ))
    (hMeas : Continuous Meas) (honto : Function.Surjective Meas)
    (hN : Continuous N)
    (hlog : ∀ θ, ∃ c : ℝ, N (Meas θ) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) :
    let S := {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}
    let G := (fun θ : Fin n → ℝ => (Matrix.of (fun (r : Fin n) (j : EdgeIdx F) => (Bmat F r j : ℝ))).mulVec (fun j => Real.log (Real.sin ((fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (edgeOf F j)))))
    let R := fun z => (fun z : Fin n → ℝ => (Matrix.of (fun (x r : Fin n) => (Pmat F x r : ℝ))).mulVec ((Matrix.of (fun (r s : Fin n) => (Dmat n r s : ℝ))).mulVec z)) (N z)
    ∃ g : S ≃ₜ Set.range (fun θ : S => G θ.val), (∀ θ, (g θ).val = G θ.val) ∧
      ∃ e : S ≃ₜ Crit, (∀ θ, e θ = Meas θ) ∧
        ∀ z, ∃ hz : R z ∈ Set.range (fun θ : S => G θ.val), e.symm z = g.symm ⟨R z, hz⟩ := by
  sorry

theorem gauge_slice_nonempty (F : LooplessBAP n) (a : Fin n → ℝ) :
    ({θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p}).Nonempty := by
  sorry

/-- The hypotheses are jointly realized by the image of the necklace log
map and its inclusion. Crit is nonempty for every F and every anchor vector. -/
theorem gal512_hypotheses_nonvacuous (F : LooplessBAP n) (a : Fin n → ℝ) :
    ∃ Crit : Set (Fin n → ℝ), Crit.Nonempty ∧
      ∃ Meas : {θ : Fin n → ℝ | (∀ p q, CrossEdge F p q → 0 < (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) ∧ (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => θ e.2 - θ e.1 + Real.pi * (if e.2 < e.1 then 1 else 0)) θ (p,q) < Real.pi) ∧ ∀ p, (∀ q, Relation.ReflTransGen (fun p q => CrossEdge F p q ∨ CrossEdge F q p) p q → p ≤ q) → θ p = a p} → Crit, ∃ N : Crit → (Fin n → ℝ),
        Continuous Meas ∧ Function.Surjective Meas ∧ Continuous N ∧
        (∀ θ, ∃ c : ℝ, N (Meas θ) = (fun θ : Fin n → ℝ => fun r => ∑ e : {e : Fin n × Fin n // e.1 < e.2}, (pairExponent F r e.val : ℝ) * (fun (θ : Fin n → ℝ) (e : Fin n × Fin n) => let t := fun j => Complex.exp (Complex.I * (θ j : ℂ)); Real.log ‖(if e.2 < e.1 then t e.1 / t e.2 - t e.2 / t e.1 else t e.2 / t e.1 - t e.1 / t e.2)‖) θ e.val) θ.val + fun _ => c) := by
  sorry

end Conj43
