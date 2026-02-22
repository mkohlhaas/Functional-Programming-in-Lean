def bufsize : USize := 20 * 1024

-- A do expression contains a sequence of statements, which may be:
-- · expressions that represent IO actions
-- · ordinary local definitions with let and := where the defined name refers to the value of the provided expression
-- · local definitions with let and ← where the defined name refers to the result of executing the value of the provided expression

-- Furthermore, if and match expressions that occur immediately under a do are implicitly considered to have their own
-- do in each branch. Inside of a do expression, nested actions are expressions with a left arrow immediately under
-- parentheses. The Lean compiler implicitly lifts them to the nearest enclosing do, which may be implicitly part of
-- a branch of a match or if expression, and gives them a unique name. This unique name then replaces the origin site
-- of the nested action.

-- functions whose definition is marked partial are not required to terminate
-- partial bc it calls itself recursively on input that is not immediately smaller than an argument -/
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
 if not (← filename.pathExists) then
   (← IO.getStderr).putStrLn s!"File not found: {filename}"
   pure none
 else
   let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
   pure (some (IO.FS.Stream.ofHandle handle))

def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args

-- In Lean, `main` can have one of three types:
-- main : IO Unit                  is used for simple programs that cannot read their command-line arguments and always return exit code 0
-- main : IO UInt32                is used for programs without arguments that may signal success or failure
-- main : List String → IO UInt32  is used for programs that take command-line arguments and signal success or failure

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
