/-
Conj43/PairOrders.lean — the six cyclic orders of two strands' endpoints (reading-edition note for
interface item INT1).

For labels p ≠ q, write E_p = entryPos F p (the entry b⁺ of the strand ending at p), X_p = exitPos p
(its exit b⁻), and likewise E_q, X_q. These four positions are distinct, so they occur clockwise in
exactly one of six cyclic orders. The frozen predicates name four of them:
  CrossEdge F p q : E_p, E_q, X_p, X_q   (crossing, p → q)
  CrossEdge F q p : E_p, X_q, X_p, E_q   (crossing, q → p)
  MisUD F p q     : E_p, X_p, E_q, X_q   (misalignment)
  MisDU F p q     : E_p, X_q, E_q, X_p   (misalignment; defined as the mirror image of MisUD)
and the two left over are the aligned orders:
  Aligned F p q   : E_p, X_p, X_q, E_q
  Aligned F q p   : E_p, E_q, X_q, X_p
`pair_orders` proves that exactly one of the six holds. With `alignment_iff_affine`
(InterfaceCrossingProofs.lean), the two aligned orders are Galashin's alignment.
-/
import Conj43.RowDiff
import Conj43.Clockwise4Forms

namespace Conj43

variable {n : ℕ}

/-- The aligned order E_p, X_p, X_q, E_q (the strands run side by side in the same direction). -/
def Aligned (F : LooplessBAP n) (p q : Fin n) : Prop :=
  Clockwise4 (5 * n) (entryPos F p) (exitPos p) (exitPos q) (entryPos F q)

instance (F : LooplessBAP n) (p q : Fin n) : Decidable (Aligned F p q) := by
  unfold Aligned; infer_instance

/-- Exactly one of six propositions holds: one of them, and no two together. -/
def ExactlyOne6 (A B C D E G : Prop) : Prop :=
  (A ∨ B ∨ C ∨ D ∨ E ∨ G) ∧
  ¬(A ∧ B) ∧ ¬(A ∧ C) ∧ ¬(A ∧ D) ∧ ¬(A ∧ E) ∧ ¬(A ∧ G) ∧
  ¬(B ∧ C) ∧ ¬(B ∧ D) ∧ ¬(B ∧ E) ∧ ¬(B ∧ G) ∧
  ¬(C ∧ D) ∧ ¬(C ∧ E) ∧ ¬(C ∧ G) ∧
  ¬(D ∧ E) ∧ ¬(D ∧ G) ∧
  ¬(E ∧ G)

/-- On positions below `m`, `Clockwise4` is one of the four rotations of increasing order. -/
theorem cw4_iff_cyclic {m a b c d : ℕ} (hm : 0 < m)
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m) :
    Clockwise4 m a b c d ↔
      (a < b ∧ b < c ∧ c < d) ∨ (b < c ∧ c < d ∧ d < a) ∨
        (c < d ∧ d < a ∧ a < b) ∨ (d < a ∧ a < b ∧ b < c) := by
  unfold Clockwise4
  rcases step_spec hm ha hb with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases step_spec hm hb hc with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
      rcases step_spec hm hc hd with ⟨h3, e3⟩ | ⟨h3, e3⟩ <;>
        rcases step_spec hm hd ha with ⟨h4, e4⟩ | ⟨h4, e4⟩ <;>
          omega

/-- The reflection of a position strictly inside the circle. -/
theorem negPos_of_pos {m v : ℕ} (h0 : 0 < v) (hv : v < m) : negPos m v = m - v := by
  unfold negPos
  exact Nat.mod_eq_of_lt (by omega)

/-- `Clockwise4` does not depend on which of the four points is named first. -/
theorem cw4_rot {m a b c d : ℕ} : Clockwise4 m a b c d ↔ Clockwise4 m b c d a := by
  unfold Clockwise4
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h2, h3, h4, h1, by omega⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h4, h1, h2, h3, by omega⟩

/-- Reflecting the circle reverses the clockwise order. -/
theorem cw4_mirror {m a b c d : ℕ} (hm : 0 < m)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d)
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m) :
    Clockwise4 m (m - a) (m - b) (m - c) (m - d) ↔ Clockwise4 m a d c b := by
  rw [cw4_iff_cyclic hm (by omega) (by omega) (by omega) (by omega), cw4_iff_cyclic hm ha hd hc hb]
  omega

/-- Clockwise offsets from a fixed point determine the point. -/
theorem step_inj {m a x y : ℕ} (hm : 0 < m) (ha : a < m) (hx : x < m) (hy : y < m)
    (h : step m a x = step m a y) : x = y := by
  rcases step_spec hm ha hx with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases step_spec hm ha hy with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> omega

/-- **The six orders:** for p ≠ q, exactly one of the six cyclic orders of E_p, X_p, E_q, X_q
holds. Measured clockwise from E_p, the other three points sit at three distinct offsets, and the
six orders are their six sortings. -/
theorem pair_orders (F : LooplessBAP n) {p q : Fin n} (hpq : p ≠ q) :
    ExactlyOne6 (CrossEdge F p q) (CrossEdge F q p) (MisUD F p q) (MisDU F p q)
      (Aligned F p q) (Aligned F q p) := by
  have hp := p.isLt
  have hq := q.isLt
  have hsp := (F.σ⁻¹ p).isLt
  have hsq := (F.σ⁻¹ q).isLt
  have hm : 0 < 5 * n := by omega
  have hne : (p : ℕ) ≠ q := fun h => hpq (Fin.ext h)
  have hsne : (F.σ⁻¹ p : ℕ) ≠ (F.σ⁻¹ q : ℕ) := fun h => hpq ((F.σ⁻¹).injective (Fin.ext h))
  have eA := entryPos_eq F p
  have eC := entryPos_eq F q
  have eB : exitPos p = 5 * (p : ℕ) + 1 := rfl
  have eD : exitPos q = 5 * (q : ℕ) + 1 := rfl
  have ha : entryPos F p < 5 * n := by omega
  have hb : exitPos p < 5 * n := by omega
  have hc : entryPos F q < 5 * n := by omega
  have hd : exitPos q < 5 * n := by omega
  have hA : CrossEdge F p q ↔ (0 < step (5 * n) (entryPos F p) (entryPos F q) ∧
      step (5 * n) (entryPos F p) (entryPos F q) < step (5 * n) (entryPos F p) (exitPos p) ∧
      step (5 * n) (entryPos F p) (exitPos p) < step (5 * n) (entryPos F p) (exitPos q)) :=
    cw4_iff_offsets hm ha hc hb hd
  have hB : CrossEdge F q p ↔ (0 < step (5 * n) (entryPos F p) (exitPos q) ∧
      step (5 * n) (entryPos F p) (exitPos q) < step (5 * n) (entryPos F p) (exitPos p) ∧
      step (5 * n) (entryPos F p) (exitPos p) < step (5 * n) (entryPos F p) (entryPos F q)) := by
    unfold CrossEdge
    rw [cw4_rot]
    exact cw4_iff_offsets hm ha hd hb hc
  have hC : MisUD F p q ↔ (0 < step (5 * n) (entryPos F p) (exitPos p) ∧
      step (5 * n) (entryPos F p) (exitPos p) < step (5 * n) (entryPos F p) (entryPos F q) ∧
      step (5 * n) (entryPos F p) (entryPos F q) < step (5 * n) (entryPos F p) (exitPos q)) :=
    cw4_iff_offsets hm ha hb hc hd
  have hD : MisDU F p q ↔ (0 < step (5 * n) (entryPos F p) (exitPos q) ∧
      step (5 * n) (entryPos F p) (exitPos q) < step (5 * n) (entryPos F p) (entryPos F q) ∧
      step (5 * n) (entryPos F p) (entryPos F q) < step (5 * n) (entryPos F p) (exitPos p)) := by
    unfold MisDU
    rw [negPos_of_pos (by omega) ha, negPos_of_pos (by omega) hb, negPos_of_pos (by omega) hc,
      negPos_of_pos (by omega) hd,
      cw4_mirror hm (by omega) (by omega) (by omega) (by omega) ha hb hc hd]
    exact cw4_iff_offsets hm ha hd hc hb
  have hE : Aligned F p q ↔ (0 < step (5 * n) (entryPos F p) (exitPos p) ∧
      step (5 * n) (entryPos F p) (exitPos p) < step (5 * n) (entryPos F p) (exitPos q) ∧
      step (5 * n) (entryPos F p) (exitPos q) < step (5 * n) (entryPos F p) (entryPos F q)) :=
    cw4_iff_offsets hm ha hb hd hc
  have hG : Aligned F q p ↔ (0 < step (5 * n) (entryPos F p) (entryPos F q) ∧
      step (5 * n) (entryPos F p) (entryPos F q) < step (5 * n) (entryPos F p) (exitPos q) ∧
      step (5 * n) (entryPos F p) (exitPos q) < step (5 * n) (entryPos F p) (exitPos p)) := by
    unfold Aligned
    rw [cw4_rot, cw4_rot, cw4_rot]
    exact cw4_iff_offsets hm ha hc hd hb
  -- the three offsets are positive and distinct
  have u0 := (step_pos_iff hm ha hb).mpr (by omega)
  have v0 := (step_pos_iff hm ha hc).mpr (by omega)
  have w0 := (step_pos_iff hm ha hd).mpr (by omega)
  have uv : step (5 * n) (entryPos F p) (exitPos p) ≠ step (5 * n) (entryPos F p) (entryPos F q) :=
    fun h => by have := step_inj hm ha hb hc h; omega
  have uw : step (5 * n) (entryPos F p) (exitPos p) ≠ step (5 * n) (entryPos F p) (exitPos q) :=
    fun h => by have := step_inj hm ha hb hd h; omega
  have vw : step (5 * n) (entryPos F p) (entryPos F q) ≠ step (5 * n) (entryPos F p) (exitPos q) :=
    fun h => by have := step_inj hm ha hc hd h; omega
  rw [hA, hB, hC, hD, hE, hG]
  generalize step (5 * n) (entryPos F p) (exitPos p) = u at *
  generalize step (5 * n) (entryPos F p) (entryPos F q) = v at *
  generalize step (5 * n) (entryPos F p) (exitPos q) = w at *
  clear * - u0 v0 w0 uv uw vw
  unfold ExactlyOne6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- "None of the four frozen predicates" is exactly the two aligned orders. -/
theorem none_of_four_iff_aligned (F : LooplessBAP n) {p q : Fin n} (hpq : p ≠ q) :
    (¬ CrossEdge F p q ∧ ¬ CrossEdge F q p ∧ ¬ MisUD F p q ∧ ¬ MisDU F p q) ↔
      (Aligned F p q ∨ Aligned F q p) := by
  obtain ⟨hex, nAB, nAC, nAD, nAE, nAG, nBC, nBD, nBE, nBG, nCD, nCE, nCG, nDE, nDG, nEG⟩ :=
    pair_orders F hpq
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases hex with h | h | h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact absurd h h4
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨fun h' => nAE ⟨h', h⟩, fun h' => nBE ⟨h', h⟩, fun h' => nCE ⟨h', h⟩,
        fun h' => nDE ⟨h', h⟩⟩
    · exact ⟨fun h' => nAG ⟨h', h⟩, fun h' => nBG ⟨h', h⟩, fun h' => nCG ⟨h', h⟩,
        fun h' => nDG ⟨h', h⟩⟩

end Conj43
