/- ------- -/
/- Logging -/
/- ------- -/

def isEven (i : Int) : Bool :=
  i % 2 == 0

-- This function is a simplified example of a common pattern.
-- Many programs need to traverse a data structure once, while both
-- computing a main result and accumulating some kind of tertiary extra result.

def sumAndFindEvens1 : List Int → List Int × Int
  | []      => ([], 0)
  | i :: is => let (moreEven, sum) := sumAndFindEvens1 is
               (if isEven i then i :: moreEven else moreEven, sum + i)

#eval sumAndFindEvens1 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

-- computes the sum of all the nodes in a tree with an inorder traversal,
-- while simultaneously recording each nodes visited
def inorderSum1 : BinTree Int → List Int × Int
  | BinTree.leaf         => ([], 0)
  | BinTree.branch l x r => let (leftVisited, leftSum)   := inorderSum1 l
                            let (hereVisited, hereSum)   := ([x], x)
                            let (rightVisited, rightSum) := inorderSum1 r
                            (leftVisited ++ hereVisited ++ rightVisited,
                             leftSum + hereSum + rightSum)

#eval inorderSum1 (BinTree.branch BinTree.leaf 5 (BinTree.branch BinTree.leaf 10 BinTree.leaf))

def sumAndFindEvens2 : List Int → List Int × Int
  | []      => ([], 0)
  | i :: is => let (moreEven, sum) := sumAndFindEvens2 is
               let (evenHere, ())  := (if isEven i then [i] else [], ())
               (evenHere ++ moreEven, sum + i)

#eval sumAndFindEvens2 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

-- a pair that consists of an accumulated result together with a value can be given its own name
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

-- the process of saving a list of accumulated results while passing a value on to the next step
-- of a computation can be factored out into a helper
def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok (x : β)    : WithLog α β    := {log := [],     val := x}
def save (data : α) : WithLog α Unit := {log := [data], val := ()}

def sumAndFindEvens3 : List Int → WithLog Int Int
  | []      => ok 0
  | i :: is => andThen (if isEven i then save i else ok ()) fun ()  =>
               andThen (sumAndFindEvens3 is)                fun sum =>
               ok (i + sum)

#eval sumAndFindEvens3 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def inorderSum3 : BinTree Int → WithLog Int Int
  | BinTree.leaf         => ok 0
  | BinTree.branch l x r => andThen (inorderSum3 l) fun leftSum  =>
                            andThen (save x)        fun ()       =>
                            andThen (inorderSum3 r) fun rightSum =>
                            ok (leftSum + x + rightSum)

#eval inorderSum3 (BinTree.branch BinTree.leaf 5 (BinTree.branch BinTree.leaf 10 BinTree.leaf))

infixl:55 " ~~> " => andThen


def sumAndFindEvens : List Int → WithLog Int Int
  | []      => ok 0
  | i :: is => (if isEven i then save i else ok ()) ~~> fun () =>
               sumAndFindEvens is ~~> fun sum =>
               ok (i + sum)

def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf         => ok 0
  | BinTree.branch l x r => inorderSum l ~~> fun leftSum  =>
                            save x       ~~> fun ()       =>
                            inorderSum r ~~> fun rightSum =>
                            ok (leftSum + x + rightSum)

open BinTree in
def intTree : BinTree Int :=
  branch
    (branch
       (branch leaf 1 (branch leaf 2 leaf))
       3 
       leaf)
    4 
    (branch leaf 5 leaf)

#eval inorderSum intTree
