def main : IO Unit := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine

  /- let name := input.dropEndWhile Char.isWhitespace -/
  let name :=input.trimAscii
  stdout.putStrLn s!"Hello, {name}!"
