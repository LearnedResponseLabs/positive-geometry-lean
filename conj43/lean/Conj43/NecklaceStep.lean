/-
Conj43/NecklaceStep.lean — the Grassmann necklace recursion without its guard (reading-edition note
for statement S14).

`necklaceAux` follows the census script: the step from row i to row i+1 is guarded by `i < n` and by
`i ∈ prior`. Below, the membership guard is shown to hold at every step, so the recursion is the
paper's unconditional `I_{r+1} = (I_r \ {r}) ∪ {f(r)}`. The wrap-around step closes the cycle: row n
equals row 0, so the cyclic form holds at every label, including the last.
-/
import Conj43.Defs

namespace Conj43

variable {n : ℕ}

/-- Membership in row r (0-based, r ≤ n), read off from σ⁻¹ x: for `σ⁻¹ x < x` the row lies in the
interval `(σ⁻¹ x, x]`; otherwise in its complement's wrap-around form. -/
def NecklaceRow (F : LooplessBAP n) (r : ℕ) (x : Fin n) : Prop :=
  if (F.σ⁻¹ x : ℕ) < x then (F.σ⁻¹ x : ℕ) < r ∧ r ≤ (x : ℕ)
  else (F.σ⁻¹ x : ℕ) < r ∨ r ≤ (x : ℕ)

theorem mem_necklaceAux_iff_row (F : LooplessBAP n) (r : ℕ) (hr : r ≤ n) (x : Fin n) :
    x ∈ necklaceAux F r ↔ NecklaceRow F r x := by
  induction r generalizing x with
  | zero =>
    simp only [necklaceAux, necklaceFirst, Finset.mem_filter, Finset.mem_univ, true_and,
      NecklaceRow]
    split_ifs <;> omega
  | succ r ih =>
    have hri : r < n := by omega
    have hl : (⟨r, hri⟩ : Fin n) ∈ necklaceAux F r := by
      rw [ih (by omega) ⟨r, hri⟩]
      dsimp only [NecklaceRow]
      split_ifs <;> omega
    simp only [necklaceAux, dif_pos hri, if_pos hl, Finset.mem_insert, Finset.mem_erase,
      ih (by omega) x]
    have hs : x = F.σ ⟨r, hri⟩ ↔ F.σ⁻¹ x = ⟨r, hri⟩ := by
      constructor
      · intro h; rw [h, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      · intro h; rw [← h, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    rw [hs]
    simp only [NecklaceRow, ne_eq, Fin.ext_iff]
    split_ifs <;> omega

/-- The guard always holds: label i lies in row i (i < n). -/
theorem self_mem_necklaceAux (F : LooplessBAP n) (i : ℕ) (hi : i < n) :
    (⟨i, hi⟩ : Fin n) ∈ necklaceAux F i := by
  rw [mem_necklaceAux_iff_row F i hi.le]
  dsimp only [NecklaceRow]
  split_ifs <;> omega

/-- **The recursion without its guard:** row i+1 is row i with label i removed and σ(i) added. -/
theorem necklaceAux_succ (F : LooplessBAP n) (i : ℕ) (hi : i < n) :
    necklaceAux F (i + 1) = (necklaceAux F i \ {⟨i, hi⟩}) ∪ {F.σ ⟨i, hi⟩} := by
  rw [Finset.union_comm, ← Finset.insert_eq, ← Finset.erase_eq]
  simp only [necklaceAux, dif_pos hi, if_pos (self_mem_necklaceAux F i hi)]

/-- **The cycle closes:** row n is row 0. -/
theorem necklaceAux_n (F : LooplessBAP n) : necklaceAux F n = necklaceAux F 0 := by
  ext x
  rw [mem_necklaceAux_iff_row F n le_rfl, mem_necklaceAux_iff_row F 0 (Nat.zero_le n)]
  have hx := x.isLt
  have hs := (F.σ⁻¹ x).isLt
  dsimp only [NecklaceRow]
  split_ifs <;> omega

/-- **The paper's cyclic recursion** `I_{p+1} = (I_p \ {p}) ∪ {f(p) mod n}`, indices mod n, for the
pinned `necklace`. Lean is 0-based: row r is the paper's I_{r+1} and label r is the paper's label r+1,
so this is the paper's step at p = r+1, including the wrap from the last row back to the first. -/
theorem necklace_step (F : LooplessBAP n) (r : Fin n) :
    necklace F ⟨((r : ℕ) + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt r.isLt)⟩ =
      (necklace F r \ {r}) ∪ {F.σ r} := by
  have hr := necklaceAux_succ F r r.isLt
  simp only [Fin.eta] at hr
  show necklaceAux F (((r : ℕ) + 1) % n) = necklaceAux F r \ {r} ∪ {F.σ r}
  rcases Nat.lt_or_ge ((r : ℕ) + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h]
    exact hr
  · have he : (r : ℕ) + 1 = n := by have := r.isLt; omega
    rw [he, Nat.mod_self, ← necklaceAux_n F]
    rw [he] at hr
    exact hr

end Conj43
