/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceDefs
namespace Conj43
/-- Affine crossing, correcting the repeated inverse argument in the source. -/
def affineCrossing (g : ℤ → ℤ) (n : ℕ) (P Q : ℤ) : Prop :=
  ∃ s t, g s = P ∧ g t = Q ∧ s < t ∧ t < P ∧ P < Q ∧ Q ≤ s + n

/-- Alignment via an inversion with its first input in the literal [1,n] window. -/
def affineAlignment {n : ℕ} (g : ℤ → ℤ) (p q : Fin n) : Prop :=
  ∃ s t : ℤ, (1 ≤ s ∧ s ≤ n) ∧ s < t ∧ g t < g s ∧
    (((g s - 1) % (n : ℤ) = (p : ℤ) ∧ (g t - 1) % (n : ℤ) = (q : ℤ)) ∨
     ((g s - 1) % (n : ℤ) = (q : ℤ) ∧ (g t - 1) % (n : ℤ) = (p : ℤ)))
end Conj43
