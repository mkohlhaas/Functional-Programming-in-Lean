/- ----------------------- -/
/- Flexible Layouts for do -/
/- ----------------------- -/

-- This version uses only whitespace-sensitive layout.
-- Each IO action or local binding in the do is expected to start on its own line, and they should all have the same indentation.
def main1 : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trimAscii
  stdout.putStrLn s!"Hello, {name}!"

-- This version is as explicit as possible.
-- Indentation can be replaced with curly braces.
def main2 : IO Unit := do {
  let stdin ← IO.getStdin;
  let stdout ← IO.getStdout;

  stdout.putStrLn "How would you like to be addressed?";
  let name := (← stdin.getLine).trimAscii;
  stdout.putStrLn s!"Hello, {name}!"
}

-- This version uses a semicolon to put two actions on the same line.
-- Newlines can be replaced with a semicolon.
def main3 : IO Unit := do
  let stdin ← IO.getStdin; let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trimAscii
  stdout.putStrLn s!"Hello, {name}!"
