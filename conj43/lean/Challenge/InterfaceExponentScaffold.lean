/- SPDX-License-Identifier: Apache-2.0 -/
import Conj43.InterfaceRefinedDefs
namespace Conj43
variable {n : ℕ}

/-! ### Group `exponent`: INT3, Galashin's (5.8) -/

theorem misUD_iff_galashin (hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    MisUD F p q ↔ galashinMisUD (galashinOf F) p q := by
  sorry

theorem misDU_iff_galashin (hn : 0 < n) (F : LooplessBAP n) (p q : Fin n) :
    MisDU F p q ↔ galashinMisDU (galashinOf F) p q := by
  sorry

/-- **INT3.** `pairExponent` is the exponent of the pair `{p, q}` on necklace row `r` in Galashin's (5.8),
with the row read through his affine necklace formula. -/
theorem pairExponent_eq_galashin (hn : 0 < n) (F : LooplessBAP n) (r p q : Fin n) (hpq : p ≠ q) :
    pairExponent F r (p, q) =
      galashinExponent (galashinOf F) (galashinNecklace (galashinOf F) ((r : ℤ) + 1)) p q := by
  sorry


end Conj43
