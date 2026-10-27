/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.Defs
namespace Conj43
/-- Strict interior of the clockwise arc from a to b. -/
def insideArc (m a b c : ℕ) : Prop :=
  0 < step m a c ∧ step m a c < step m a b

/-- Exactly one endpoint of the second chord is inside the first chord's arc. -/
def chordsInterleave (m a b c d : ℕ) : Prop :=
  (insideArc m a b c ↔ ¬ insideArc m a b d)
end Conj43
