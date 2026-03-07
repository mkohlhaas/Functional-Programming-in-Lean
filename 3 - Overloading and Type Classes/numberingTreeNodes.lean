/- -------------------- -/
/- Numbering Tree Nodes -/
/- -------------------- -/

inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)

def number1 (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf                => (n, BinTree.leaf)
    | BinTree.branch left x right => let (k, numberedLeft)  := helper n left
                                     let (i, numberedRight) := helper (k + 1) right
                                     (i, BinTree.branch numberedLeft (k, x) numberedRight)
  (helper 0 t).snd

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)
  
def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => ok BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

/- ----------------------------------- -/
/- Monads: A Functional Design Pattern -/
/- ----------------------------------- -/

-- Each of these examples has consisted of:
-- ·  A polymorphic type, such as Option, Except ε, WithLog α, or State σ
-- ·  An operator andThen that takes care of some repetitive aspect of sequencing programs that have this type
-- ·  An operator ok that is (in some sense) the most boring way to use the type
-- ·  A collection of other operations, such as none, fail, save, and get, that name ways of using the type

-- This style of API is called a monad.
-- While the idea of monads is derived from a branch of mathematics called category theory, no understanding of category theory is needed in order to use them for programming.
-- The key idea of monads is that each monad encodes a particular kind of side effect using the tools provided by the pure functional language Lean.
-- For example,
--  · Option  represents programs that can fail by returning none
--  · Except  represents programs that can throw exceptions
--  · WithLog represents programs that accumulate a log while running
--  · State   represents programs with a single mutable variable
