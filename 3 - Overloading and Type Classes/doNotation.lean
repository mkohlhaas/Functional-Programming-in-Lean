/- ====================== -/
/- do-Notation for Monads -/
/- ====================== -/

/- Translations -/

-- ---------------------- --
-- 1. single expression E --
-- ---------------------- --

-- do E => E

-- ---------------- --
-- 2. do let with ← --
-- ---------------- --

-- do let x ← E₁
--    Stmt
--    …
--    Eₙ

-- =>

-- E₁ >>= fun x =>
--   do Stmt
--      …
--      Eₙ

-- ----------------------------------- --
-- 3. first statement is an expression --
-- ----------------------------------- --

-- do E₁
--    Stmt
--    …
--    Eₙ

-- =>

-- E₁ >>= fun () =>
--   do Stmt
--      …
--      Eₙ

-- ----------------- --
-- 4. do let with := --
-- ----------------- --

-- do let x := E₁
--    Stmt
--    …
--    Eₙ

-- =>

-- let x := E₁
-- do Stmt
--    …
--    Eₙ

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first   =>
  lookup xs 2 >>= fun third   =>
  lookup xs 4 >>= fun fifth   =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

-- using do-notation
def firstThirdFifthSeventh' [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) := do
  let first   ← lookup xs 0
  let third   ← lookup xs 2
  let fifth   ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

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
    | BinTree.leaf                => ok BinTree.leaf
    | BinTree.branch left x right => helper left ~~> fun numberedLeft =>
                                     get ~~> fun n =>
                                     set (n + 1) ~~> fun () =>
                                     helper right ~~> fun numberedRight =>
                                     ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

instance : Monad (State σ) where
  pure x          := fun s => (s, x)
  bind first next := fun s =>
                       let (s', x) := first s
                       next x s'

-- using do-notation
def number' (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf                => pure BinTree.leaf
    | BinTree.branch left x right => do
                                       let numberedLeft ← helper left
                                       let n ← get
                                       set (n + 1)
                                       let numberedRight ← helper right
                                       ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)

#eval aTree        
#eval number  aTree
#eval number' aTree

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | []      => pure []
  | x :: xs => f x       >>= fun hd =>
               mapM f xs >>= fun tl =>
               pure (hd :: tl)

-- with do-notation
def mapM' [Monad m] (f : α → m β) : List α → m (List β)
  | []      => pure []
  | x :: xs => do
                 let hd ← f x
                 let tl ← mapM f xs
                 pure (hd :: tl)

-- with nested actions
def mapM'' [Monad m] (f : α → m β) : List α → m (List β)
  | []      => pure []
  | x :: xs => do pure ((← f x) :: (← mapM f xs))


-- increment increases a saved state by a given amount, returning the old value
def increment' (howMuch : Int) : State Int Int :=
  get               >>= fun i  =>
  set (i + howMuch) >>= fun () =>
  pure i

def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

-- with nested actions
def number'' (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf                => pure BinTree.leaf
    | BinTree.branch left x right => do
                                     pure
                                       (BinTree.branch
                                         (← helper left)
                                         ((← increment), x)
                                         (← helper right))
  (helper t 0).snd

#eval number'' aTree

-- `mapM increment` has type List Int → State Int (List Int),
-- and expanding the definition of State yields List Int → Int → (Int × List Int).
-- It takes an initial sum as an argument, which should be 0.
#eval mapM   increment' [1, 2, 3, 4, 5] 0
#eval mapM'  increment' [1, 2, 3, 4, 5] 0
#eval mapM'' increment' [1, 2, 3, 4, 5] 0

/- --------- -/
/- Exercises -/
/- --------- -/
