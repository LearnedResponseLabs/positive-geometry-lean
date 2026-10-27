import Conj43

def main : IO Unit := do
  IO.println (Conj43.Eval.cellJson 2 [2,1])
  IO.println (Conj43.Eval.cellJson 3 [2,3,1])
  IO.println (Conj43.Eval.cellJson 3 [3,1,2])
  IO.println (Conj43.Eval.cellJson 4 [2,1,4,3])
  IO.println (Conj43.Eval.cellJson 4 [2,3,4,1])
  IO.println (Conj43.Eval.cellJson 4 [2,4,1,3])
  IO.println (Conj43.Eval.cellJson 4 [3,1,4,2])
  IO.println (Conj43.Eval.cellJson 4 [3,4,1,2])
  IO.println (Conj43.Eval.cellJson 4 [3,4,2,1])
  IO.println (Conj43.Eval.cellJson 4 [4,1,2,3])
  IO.println (Conj43.Eval.cellJson 4 [4,3,1,2])
  IO.println (Conj43.Eval.cellJson 4 [4,3,2,1])
