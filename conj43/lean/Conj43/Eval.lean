/-
Conj43/Eval.lean — executable semantics for the L0 census cross-validation.

Evaluates the ACTUAL statement-level definitions (crossEdges, necklace, Bmat,
Mmat, Pmat, Dmat and the matrix product P_f·D·M_N) on a concrete 1-based
window and emits JSON. Output labels are converted back to 1-based to match
the Python census. Consumed by a cross-validation script (not included) via a generated driver file.
-/
import Conj43.Statements

namespace Conj43.Eval

open Conj43

/-- Build a `LooplessBAP n` from a 1-based census window (e.g. `[2,3,1]`),
checking length and bijectivity decidably. (L4: fixed points of σ are no longer
rejected — they are the coloops; `isDerangement?` below keeps the census gate.) -/
def ofWindow? (n : ℕ) [NeZero n] (w : List ℕ) : Option (LooplessBAP n) :=
  if w.length = n then
    let v : Fin n → Fin n := fun i => ⟨(w.getD i.val 1 - 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
    if hb : Function.Bijective v then
      let σ : Equiv.Perm (Fin n) :=
        ⟨v, Fintype.bijInv hb, Fintype.leftInverse_bijInv hb, Fintype.rightInverse_bijInv hb⟩
      some ⟨σ⟩
    else none
  else none

/-- Decidable coloop test, exposed for the finite gates. -/
def coloopsOf {n : ℕ} (F : LooplessBAP n) : List ℕ :=
  ((List.finRange n).filter fun i => F.σ i = i).map fun i => (i : ℕ) + 1

private def jList (l : List String) : String :=
  "[" ++ String.intercalate "," l ++ "]"

private def jInts (l : List ℤ) : String := jList (l.map toString)

private def jMat (m : List (List ℤ)) : String := jList (m.map jInts)

/-- Flatten a Fin-indexed integer matrix to row-major lists. -/
def matToLists {n E : ℕ} (M : Matrix (Fin n) (Fin E) ℤ) : List (List ℤ) :=
  (List.finRange n).map fun r => (List.finRange E).map fun j => M r j

private def cellJsonAux (n : ℕ) [NeZero n] (w : List ℕ) : String :=
  match ofWindow? n w with
  | none => "{\"error\":\"invalid window\"}"
  | some F =>
    let edges := (crossEdges F).map fun e =>
      "[" ++ toString ((e.1 : ℕ) + 1) ++ "," ++ toString ((e.2 : ℕ) + 1) ++ "]"
    let nk := (List.finRange n).map fun r =>
      jList (((necklace F r).sort (· ≤ ·)).map fun x => toString ((x : ℕ) + 1))
    let PDM := Pmat F * Dmat n * Mmat F
    let advTotal := ((crossEdges F).map fun e => adv e.1 e.2).sum
    "{\"window\":" ++ jList (w.map toString) ++
      ",\"coloops\":" ++ jList ((coloopsOf F).map toString) ++
      ",\"rank\":" ++ toString (rank F) ++
      ",\"edges\":" ++ jList edges ++
      ",\"necklace\":" ++ jList nk ++
      ",\"B\":" ++ jMat (matToLists (Bmat F)) ++
      ",\"M\":" ++ jMat (matToLists (Mmat F)) ++
      ",\"PDM\":" ++ jMat (matToLists PDM) ++
      ",\"adv_total\":" ++ toString advTotal ++ "}"

/-- JSON record for one census cell given as (n, 1-based window). -/
def cellJson : (n : ℕ) → List ℕ → String
  | 0, _ => "{\"error\":\"n=0\"}"
  | m + 1, w => cellJsonAux (m + 1) w

end Conj43.Eval
