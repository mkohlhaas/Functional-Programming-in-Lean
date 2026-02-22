import Greeting
import Greeting.Smile

/- open Expression -/
open Expression (happy)

def main : IO Unit :=
  IO.println s!"Hello, {hello} with {happy}!!"
