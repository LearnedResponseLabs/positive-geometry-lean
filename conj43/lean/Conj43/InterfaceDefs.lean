/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.Defs
namespace Conj43
/-- Galashin dfn:BAP, with the literal integer window [1,n]. -/
def IsBAP (k n : ℕ) (g : ℤ → ℤ) : Prop :=
  Function.Bijective g ∧ (∀ j, g (j + n) = g j + n) ∧
  (∑ j ∈ Finset.Icc (1 : ℤ) (n : ℤ), (g j - j)) = (k : ℤ) * n ∧
  ∀ j, j ≤ g j ∧ g j ≤ j + n

def IsLooplessBAP (k n : ℕ) (g : ℤ → ℤ) : Prop :=
  IsBAP k n g ∧ ∀ p, p < g p

def galashinOf {n : ℕ} (F : LooplessBAP n) : ℤ → ℤ :=
  fun p => F.f (p - 1) + 1

/-- Reduce each g(p) into [1,n] as ((g(p)-1) mod n)+1,
then subtract one to obtain a zero-based label. -/
noncomputable def galashinNecklace {n : ℕ} (g : ℤ → ℤ) (q : ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x => ∃ p : ℤ, p < q ∧ q ≤ g p ∧
    (x : ℤ) = (((g p - 1) % (n : ℤ)) + 1) - 1
end Conj43
