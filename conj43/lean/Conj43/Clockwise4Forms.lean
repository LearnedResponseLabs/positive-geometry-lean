/-
Conj43/Clockwise4Forms.lean — two equivalent readings of `Clockwise4` on positions below
the modulus (reading-edition note for statement S04).

`Clockwise4` asks for four positive steps that sum to `m`. Positivity is the distinctness
condition: on positions below `m`, a step is zero exactly when its two endpoints coincide.
The sum then picks out the clockwise order (the other cyclic orders sum to `2m` or `3m`).
Both forms below are equivalent to the definition on positions below `m`; outside that
range two different numbers can name the same position, so the range hypotheses are needed.
-/
import Conj43.CyclicArc

namespace Conj43

/-- On positions below `m`, a step is zero exactly when its endpoints coincide. -/
theorem step_pos_iff {m a b : ℕ} (hm : 0 < m) (ha : a < m) (hb : b < m) :
    0 < step m a b ↔ a ≠ b := by
  rcases step_spec hm ha hb with ⟨h, e⟩ | ⟨h, e⟩ <;> omega

/-- `Clockwise4` is the sum condition together with distinctness of consecutive points. -/
theorem cw4_iff_ne {m a b c d : ℕ} (hm : 0 < m)
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m) :
    Clockwise4 m a b c d ↔
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧
        step m a b + step m b c + step m c d + step m d a = m := by
  unfold Clockwise4
  rw [step_pos_iff hm ha hb, step_pos_iff hm hb hc, step_pos_iff hm hc hd, step_pos_iff hm hd ha]

/-- `Clockwise4` is strictly increasing positive offsets of `b`, `c`, `d` measured clockwise
from `a`. -/
theorem cw4_iff_offsets {m a b c d : ℕ} (hm : 0 < m)
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m) :
    Clockwise4 m a b c d ↔ 0 < step m a b ∧ step m a b < step m a c ∧ step m a c < step m a d := by
  rw [cw4_iff_linear hm ha hb hc hd]
  rcases step_spec hm ha hb with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases step_spec hm ha hc with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
      rcases step_spec hm ha hd with ⟨h3, e3⟩ | ⟨h3, e3⟩ <;>
        omega

end Conj43
