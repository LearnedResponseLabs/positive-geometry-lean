/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceDefs
namespace Conj43
theorem galashin_isLooplessBAP {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) :
    IsLooplessBAP (rank F) n (galashinOf F) := by sorry

theorem galashin_residues {n : ℕ} (hn : 0 < n) (F : LooplessBAP n)
    (p : ℤ) (hp : 1 ≤ p) (hpn : p ≤ n) :
    Int.ModEq (n : ℤ) (galashinOf F p)
      ((F.σ ⟨(p - 1).toNat, by omega⟩ : ℕ) + 1) := by sorry

theorem galashin_injective {n : ℕ} (hn : 0 < n) (F G : LooplessBAP n) :
    galashinOf F = galashinOf G → F = G := by sorry

theorem galashin_surjective {k n : ℕ} (hn : 0 < n) (g : ℤ → ℤ)
    (hg : IsLooplessBAP k n g) :
    ∃ F : LooplessBAP n, galashinOf F = g ∧ rank F = k := by sorry

theorem galashin_coloop {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p : Fin n) :
    F.σ p = p ↔ galashinOf F ((p : ℤ) + 1) = ((p : ℤ) + 1) + n := by sorry

theorem galashin_no_loops {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (p : ℤ) :
    galashinOf F p ≠ p := by sorry

theorem galashin_rank_range {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) :
    1 ≤ rank F ∧ rank F ≤ n := by sorry

theorem galashin_necklace {n : ℕ} (hn : 0 < n) (F : LooplessBAP n) (r : Fin n) :
    necklace F r = galashinNecklace (galashinOf F) ((r : ℤ) + 1) := by sorry

end Conj43
