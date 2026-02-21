#eval 1 + 3 * 5

#eval String.append "Hello, " "Lean!"

#eval String.append "great " (String.append "oak " "tree")

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

#eval 42 + 19

#eval String.append "A" (String.append "B" "C")

#eval String.append (String.append "A" "B") "C"

#eval if 3 == 3 then 5 else 7

#eval if 3 ==4 then "equal" else "not equal"

#eval (1 + 2 : Nat)

#eval 1 - 2

#eval (1 - 2 : Nat)

#eval (1 - 2 : Int)

#check (1 - 2 : Int)

#check (1 - 2)

/- #check String.append ["hello", " "] "world" -/

def hello := "Hello"

def lean : String := "Lean"

#eval String.append " " lean

#eval String.append hello (String.append " " lean)

def add1_1 n := n + 1

#eval add1_1 5

def add1_2 (n : Nat) : Nat := n + 1

#eval add1_2 5

/- def maximum1 n k : Nat := -/
/-   if n < k then -/
/-     k -/
/-   else n -/
  
def maximum2 (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n 

#eval maximum2 2 5

def spaceBetween1 (before : String) (after : String) : String :=
  String.append before (String.append " " after)
  
/- def spaceBetween2 before after : String := -/
/-   String.append before (String.append " " after) -/

#check  spaceBetween1
#check (spaceBetween1)

/- Define the function joinStringsWith with type String → String → String → String that creates a new string by placing its first argument between its second and third arguments. joinStringsWith ", " "one" "and another" should evaluate to "one, and another". -/

def joinStringsWith sep before after := String.append before (String.append sep after)

#check joinStringsWith

#eval joinStringsWith ", " "one" "and another"

#check joinStringsWith ": "

def volume (height : Nat) width depth := height * width * depth

#check volume
#check (volume)

/- def Str : Type := String -/

def Str := String
/- abbrev Str := String -/

def aStr : Str    := "This is a string."
def bStr : String := "This is another string."

#eval aStr ++ aStr
#eval bStr ++ bStr

/- def NaturalNumber : Type := Nat -/
def NaturalNumber := Nat

/- def thirtyEight : NaturalNumber := 38 -/

def thirtyEight : NaturalNumber := (38 : Nat)

abbrev N := Nat

def thirtyNine : N := 39

#check 1.2
#check -454.2123215
#check 0.0

#check 0
#check (0 : Float)

structure Point where
  x : Float
  y : Float

def origin : Point := { x := 0.0,
                        y := 0.0 }

#eval origin                       

#eval origin.x
#eval origin.y

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x,
    y := p1.y + p2.y }

def p1 : Point := { x := 1.5, y := 32 }
def p2 : Point := { x := -8,  y := 0.2 }
  
#eval addPoints p1 p2 

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance p1 p2

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := { x := 0.0,
                            y := 0.0,
                            z := 0.0 }

#check ({ x := 0.0, y := 0.0 } : Point)
#check { x := 0.0, y := 0.0 : Point}

/- def zeroX (p : Point) : Point := { x := 0, -/
/-                                    y := p.y } -/

def zeroX (p : Point) : Point := { p with x := 0 }

def fourAndThree : Point := { x := 4.3, y := 3.4 }

#eval fourAndThree
#eval zeroX fourAndThree
#eval fourAndThree

#check Point.mk 1.5 2.8

#check (Point.mk)
#check (Point.x)
#check (Point.y)

#eval origin.x
#eval Point.x origin

structure MyPoint where
  point :: /- new constructor name -/
  x : Float
  y : Float

#check MyPoint.point 1.5 2.8

#eval "one string".append " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor

structure RectangularPrism where 
   height : Float
   width  : Float
   depth  : Float

def volumePrism (p : RectangularPrism) : Float := p.height * p.width * p.depth

structure Segment where
  p1 : Point
  p2 : Point

def segmentLength (l : Segment) : Float := distance l.p1 l.p2

/- Which names are introduced by the declaration of RectangularPrism? -/
/- p.height, p.width, p.depth, p.mk -/

/- Which names are introduced by the following declarations of Hamster and Book? What are their types? -/

structure Hamster where
  name : String
  fluffy : Bool
  
structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

inductive MyBool where
  | false : MyBool
  | true  : MyBool

inductive MyNat where
  | zero 
  | succ (n : Nat)

#eval Nat.succ Nat.zero
#eval Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ _ => false

#eval isZero 0
#eval isZero 5

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

#eval pred 0
#eval pred 5
#eval pred 839

def depth (p : Point3D) : Float :=
  match p with
  | { x := _h,
      y := _w,
      z :=  d } => d

#eval depth origin3D 

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ k => not (even k)

def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ k => not (evenLoops n)

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => Nat.succ (plus n k')

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)

structure PPoint (α : Type) where
  x : α
  y : α

def natOrigin : PPoint Nat := { x := Nat.zero,
                                y := Nat.zero }

def replaceX (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
                                
#eval replaceX natOrigin 5

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => ( 3 : Nat)
  | Sign.neg => (-3 : Int)

#eval posOrNegThree Sign.pos
#eval posOrNegThree Sign.neg

def primesUnder10 : List Nat := [2, 3, 5, 7]

inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

#eval explicitPrimesUnder10

#eval List.length ["Sourdough", "bread"]

def length (xs : List α) : Nat :=
  match xs with
  | List.nil        => Nat.zero
  | List.cons _ lst => Nat.succ (length lst)


#eval length ["Sourdough", "bread"]

def length1 (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (length1 ys)

#eval length1 ["Sourdough", "bread"]

#eval ["Sourdough", "bread"].length

#check List.length
#check List.length (α := Int)

inductive MyOption (α : Type) : Type where
  | none           : MyOption α
  | some (val : α) : MyOption α

def head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | []     => none
  | y :: _ => some y

#eval head? ([] : List String)
#eval head? ["Sourdough", "bread"]

#eval primesUnder10.head?

/- List.head  requires the caller to provide mathematical evidence that the list is not empty -/
/- List.head? returns an Option -/
/- List.head! crashes the program when passed an empty list -/
/- List.headD takes a default value to return in case the list is empty -/

#eval [].head? (α := Int)
#eval ([] : List Int).head?

structure MyProd (α : Type) (β : Type) : Type where
  fst : α
  snd : β

def fives1 : String × Int := { fst := "five", snd := 5 }
def fives2 : String × Int := ("five", 5)

def sevens1 : String × Int × Nat   := ("VII",  7,  4)
def sevens2 : String × (Int × Nat) := ("VII",  7,  4)
def sevens3 : (String × Int) × Nat := (("VII", 7), 4)

inductive MySum (α : Type) (β : Type) : Type where
  | inl : α → MySum α β
  | inr : β → MySum α β

def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot",  /- dog -/
   Sum.inr "Tiger", /- cat -/
   Sum.inl "Fifi",  /- dog -/
   Sum.inl "Rex",   /- dog -/
   Sum.inr "Floof"] /- cat -/

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | []                => 0
  | Sum.inl _ :: pets => howManyDogs pets + 1
  | Sum.inr _ :: pets => howManyDogs pets

#eval howManyDogs animals

/- in polymorphic code can be used as a placeholder for missing data -/
inductive MyUnit : Type where
  | unit : MyUnit

/- ann = annotation -/
inductive ArithExpr (ann : Type) : Type where
  | int   : ann → Int → ArithExpr ann
  | plus  : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

/- ArithExpr SourcePos  -/
/- ArithExpr Unit  -/

/- Empty indicates unreachable code -/

/- Types that offer multiple constructors are called SUM TYPES.
   Types whose single constructor takes multiple arguments are called PRODUCT TYPES. -/

def badSameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (_ :: xs', _ :: ys') => badSameLength xs' ys'
  | _ => false

/- nested pattern matching -/
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs with
  | [] =>
    match ys with
    | [] => true
    | _  => false
  | _ :: xs' =>
    match ys with
    | _ :: ys' => sameLength xs' ys'
    | _        => false

inductive WoodSplittingTool where
  | axe
  | maul
  | froe
  deriving Repr
  
#eval WoodSplittingTool.axe

def allTools : List WoodSplittingTool := [
  WoodSplittingTool.axe,
  WoodSplittingTool.maul,
  WoodSplittingTool.froe
]

#eval allTools

def lastEntry (l : List α) : Option α := 
  match l with
  | []       => none
  | [elem]   => some elem
  | _ :: xs  => lastEntry xs

#eval lastEntry ([] : List Nat)
#eval lastEntry [1]
#eval lastEntry [1, 2, 3, 4, 5]

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | x :: xs => if predicate x then some x else List.findFirst? xs predicate

#eval List.findFirst? [] even
#eval List.findFirst? [1, 2, 3, 4, 5] even

def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  match pair with
  | (a, b) => (b, a)

#eval Prod.switch (1, 2) 

inductive Pet where
 | dogName : String → Pet
 | catName : String → Pet

def animals1 : List Pet :=
  [Pet.dogName "Spot",
   Pet.catName "Tiger",
   Pet.dogName "Fifi",
   Pet.dogName "Rex",
   Pet.catName "Floof"]

def howManyDogs1 (pets : List Pet) : Nat :=
  match pets with
  | []                    => 0
  | Pet.dogName _ :: pets => howManyDogs1 pets + 1
  | Pet.catName _ :: pets => howManyDogs1 pets

#eval howManyDogs1 animals1

def badZip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match (xs, ys) with
  | ([], _) => []
  | (_, []) => []
  | (x :: xs', y :: ys') => List.cons (x, y) (badZip xs' ys')


def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | [] => []
  | x :: xs' => match ys with
                | [] => []
                | y :: ys' => List.cons (x, y) (zip xs' ys')

#eval zip [1, 2, 3, 4, 5] ["a", "b", "c", "d", "e"]
#eval zip [1, 2, 3, 4   ] ["a", "b", "c", "d", "e"]
#eval zip [1, 2, 3, 4, 5] ["a", "b", "c", "d"     ]

def takeAcc (n : Nat) (xs : List α) (ys : List α) : List α :=
  match n with
  | 0 => ys
  | _ => match xs with
         | []       => List.reverse ys
         | x :: xs' => takeAcc (n - 1) xs' (List.cons x ys)

def take (n : Nat) (xs : List α) : List α := takeAcc n xs []

#eval take 1 ["bolete", "oyster"] 
#eval take 3 ["bolete", "oyster"] 

def distribute (e : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match e with
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)
  
#eval distribute (1, (Sum.inl "a" : String ⊕ String))
#eval distribute (1, (Sum.inr "a" : String ⊕ String))

/- Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum. -/
def mult2sum (e : Bool × α) : α ⊕ α :=
  match e with
  | (true,  a) => Sum.inl a
  | (false, a) => Sum.inr a

def lengthExplicit {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (lengthExplicit ys)

def lengthImplicit (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (lengthImplicit ys)

def lengthPatternMatching : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (lengthPatternMatching ys)

def drop : Nat → List α → List α
  | Nat.zero, xs        => xs
  | _, []               => []
  | Nat.succ n, _ :: xs => drop n xs

def fromOption (default : α) : Option α → α
  | none   => default
  | some x => x

#eval none.getD ""
#eval (some "salmonberry").getD ""

/- given a list of pairs returns a pair of lists -/
def unzipInefficient : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => (x :: (unzipInefficient xys).fst, y :: (unzipInefficient xys).snd) /- oops, two recursive calls -/

/- only one recursive call with `let` -/
/- To use `let` on a single line, separate the local definition from the body with a semicolon. -/
def unzipEfficient : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let unzipped : List α × List β := unzipEfficient xys
                     (x :: unzipped.fst, y :: unzipped.snd)

/- Local definitions with `let` may also use pattern matching when one pattern is enough to match all cases. -/
def unzip : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let (xs, ys) : List α × List β := unzip xys
                     (x :: xs, y :: ys)

/- recursive let definitions must be explicitly indicated so -/
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar      => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

/- type annotations -/
def id1 (x : α) : α := x
def id2 (x : α)     := x
def id3 x           := x

def dropSimultaneousMatching (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys         => ys
  | _, []                => []
  | Nat.succ n , _ :: ys => dropSimultaneousMatching n ys

def sameLengthPair (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], [])             => true
  | (x :: xs', y :: ys') => sameLengthPair xs' ys'
  | _                    => false


/- Lean tracks the connection between the expression being matched and the patterns, -/
/- and this information is used for purposes that include checking for termination -/
/- and propagating static type information. -/
def sameLengthSimultaneousMatching (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], []             => true
  | _ :: xs', _ :: ys' => sameLengthSimultaneousMatching xs' ys'
  | _, _               => false

/- using literals instead of Nat.zero, Nat.succ -/
def evenLiterals : Nat → Bool
  | 0     => true
  | n + 1 => not (evenLiterals n)

def halveLiterals : Nat → Nat
  | Nat.zero              => 0
  | Nat.succ Nat.zero     => 0
  | Nat.succ (Nat.succ n) => halveLiterals n + 1

def halve : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n + 2 => halve n + 1

def halveBad : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2 + n => halveBad n + 1
  
/- anonymous function -/
#check fun x => x + 1

/- with type annotation -/
#check fun (x : Int) => x + 1

/- with type params -/
#check fun {α : Type} (x : α) => x

/- can be written with λ instead of `fun`-/
#check λ x => x + 1

/- anonymous function with pattern matching -/
#check fun
  | 0     => none
  | n + 1 => some n

/- function written as a function expression -/
def double : Nat → Nat := fun
  | 0     => 0
  | k + 1 => double k + 2

/- centered dot `·` -/
#check fun x => x + 1
#check (· + 1) 

#check (· + 5, 3)   /- a function that returns a pair of numbers  -/
#check ((· + 5), 3) /- a pair of a function and a number. -/

#eval (· , ·) 1 2

#eval (fun x => x + x) 5 

#eval (· * 2) 5 

/- Namespaces -/

def Nat.double (x : Nat) : Nat := x + x

#eval (4 : Nat).double

namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

#check NewNamespace.triple

#check NewNamespace.quadruple

/- open namespace prior to an expression -/
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)

/- open namespace prior to a command -/
open NewNamespace in
#check quadruple

/- Namespaces may be opened for all following commands for the rest of the file. -/
/- To do this, omit the `in` from a top-level usage of open. -/

inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph :   Inline → Inline
  | strong : Inline → Inline

def Inline.string1? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _               => none

/- `if let` can be used with sum types and might be easier to read (???) -/
def Inline.string2? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none

/- Constructing Structures -/

/- 1. constructor -/
#eval Point.mk 1 2

/- 2. brace notation -/
#eval ({ x := 1, y := 2 } : Point)
#eval  { x := 1, y := 2 : Point } 

/- 3. positional structure arguments -/
#eval (⟨1, 2⟩ : Point)

/- string interpolation -/
#eval s!"three fives is {NewNamespace.triple 5}"

/- function cannot string interpolated -/
#check s!"three fives is {NewNamespace.triple}"
