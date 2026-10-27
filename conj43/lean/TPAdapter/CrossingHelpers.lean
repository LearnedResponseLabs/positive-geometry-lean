/- SPDX-License-Identifier: Apache-2.0 -/
import TP.CrossingAdapterDefs
import Conj43.InterfaceCrossingProofs

namespace TP
variable {n : ℕ}

/-- Replacing a black fixed point by a coloop is the only change of affine lift. -/
theorem affine_loop_options (hn : 0 < n) (π : DecPerm n) (z : ℤ) :
    π.affine z = (Conj43.LooplessBAP.mk π.perm).f z ∨
      (π.affine z = z ∧ (Conj43.LooplessBAP.mk π.perm).f z = z+n) := by
  obtain ⟨r,k,hz⟩ := exists_window hn z
  have hf : (Conj43.LooplessBAP.mk π.perm).f z =
      (π.perm r : ℤ) + (if π.perm r ≤ r then (n : ℤ) else 0) + n*k := by
    rw [hz, mul_comm (n : ℤ) k, Conj43.f_translate hn, Conj43.f_window hn]
  rw [π.affine_eq hn z r k hz, hf]
  unfold DecPerm.windowLift
  simp only [Fin.le_def]
  split_ifs <;> omega

/-- A loop or coloop cannot supply either endpoint of an affine crossing. -/
theorem affine_crossing_ignore_loops (hn : 0 < n) (π : DecPerm n) (P Q : ℤ) :
    Conj43.affineCrossing π.affine n P Q ↔
      Conj43.affineCrossing (Conj43.LooplessBAP.mk π.perm).f n P Q := by
  constructor
  · rintro ⟨s,t,hs,ht,hst,htP,hPQ,hQs⟩
    have es : π.affine s = (Conj43.LooplessBAP.mk π.perm).f s :=
      (affine_loop_options hn π s).resolve_right (by rintro ⟨h,_⟩; omega)
    have et : π.affine t = (Conj43.LooplessBAP.mk π.perm).f t :=
      (affine_loop_options hn π t).resolve_right (by rintro ⟨h,_⟩; omega)
    exact ⟨s,t,es.symm.trans hs,et.symm.trans ht,hst,htP,hPQ,hQs⟩
  · rintro ⟨s,t,hs,ht,hst,htP,hPQ,hQs⟩
    have es : π.affine s = (Conj43.LooplessBAP.mk π.perm).f s :=
      (affine_loop_options hn π s).resolve_right (by rintro ⟨_,h⟩; omega)
    have et : π.affine t = (Conj43.LooplessBAP.mk π.perm).f t :=
      (affine_loop_options hn π t).resolve_right (by rintro ⟨_,h⟩; omega)
    exact ⟨s,t,es.trans hs,et.trans ht,hst,htP,hPQ,hQs⟩

/-- The shift from the 0-based lift to Galashin's 1-based lift preserves crossings. -/
theorem affine_crossing_shift (F : Conj43.LooplessBAP n) (P Q : ℤ) :
    Conj43.affineCrossing F.f n P Q ↔
      Conj43.affineCrossing (Conj43.galashinOf F) n (P+1) (Q+1) := by
  constructor
  · rintro ⟨s,t,hs,ht,hst,htP,hPQ,hQs⟩
    refine ⟨s+1,t+1,?_,?_,by omega,by omega,by omega,by omega⟩ <;>
      simp [Conj43.galashinOf, hs, ht]
  · rintro ⟨s,t,hs,ht,hst,htP,hPQ,hQs⟩
    simp only [Conj43.galashinOf] at hs ht
    exact ⟨s-1,t-1,by omega,by omega,by omega,by omega,by omega,by omega⟩
end TP
