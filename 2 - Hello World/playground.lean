/- Nested actions cannot be lifted from the branches of an `if`. -/

def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5

def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7

/- A program that prints 0 when number A is five, or number B otherwise, might be written as follows: -/
def test1 : IO Unit := do
  let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB) /- runs getNumB only if getNumA is equal to 5 -/
  (← IO.getStdout).putStrLn s!"The answer is {a}"

/- This program would be equivalent to: -/
def test2 : IO Unit := do
  let x ← getNumA
  let y ← getNumB /- runs getNumB regardless of whether the result of getNumA is equal to 5 -/
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"

/- To prevent this confusion, nested actions are not allowed in an if that is not itself a line in the do. -/
