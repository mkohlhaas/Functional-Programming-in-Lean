import Lean -- for Lean.Json.escape

/- ---------------- -/
/- Positive Numbers -/
/- ---------------- -/

inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos

def seven1 : Pos := 7

def seven2 : Pos := Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

def fourteen1  : Pos := seven2 + seven2
def fortyNine1 : Pos := seven2 * seven2

/- --------------------- -/
/- Classes and Instances -/
/- --------------------- -/

-- Type classes are first class, just as types are first class.
-- A type class is another kind of type.
-- The type of Plus is Type → Type.
class Plus (α : Type) where
  plus : α → α → α

-- The `:` after `instance` indicates that Plus Nat is indeed a type.
instance : Plus Nat where
  plus := Nat.add 

#eval Plus.plus 5 3

-- By default, type class methods are defined in a namespace with the same name as the type class. 
open Plus (plus)

#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k    => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen2 : Pos := plus seven2 seven2

#eval fourteen2

-- no instance for Plus Float
#eval plus 5.2 917.25861

/- ------------------- -/
/- Overloaded Addition -/
/- ------------------- -/

-- The Lean libraries are set up so that an instance of Add will be found when searching for an instance of 
-- HAdd (heterogeneous add) in which both arguments have the same type.
instance : Add Pos where
  add := Pos.plus
  
def fourteen3 : Pos := seven2 + seven2

#eval fourteen3

/- --------------------- -/
/- Conversion to Strings -/
/- --------------------- -/

-- ToString Type Class

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one    => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

#eval s!"There are {seven2}"

-- piggypacking Nats
def Pos.toNat : Pos → Nat
  | Pos.one    => 1
  | Pos.succ n => n.toNat + 1
  
instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven2}"

/- ------------------------- -/
/- Overloaded Multiplication -/
/- ------------------------- -/

-- The Lean libraries are set up so that an instance of Mul will be found when searching for an instance of 
-- HMul (heterogeneous multiplication) in which both arguments have the same type.
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k    => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

#eval [seven2 * Pos.one,
       seven2 * seven2,
       Pos.succ Pos.one * seven2]

/- --------------- -/
/- Literal Numbers -/
/- --------------- -/

-- type classes that are used to overload numeric literals: Zero, One, and OfNat

/- type classes -/

class MyZero (α : Type) where
  zero : α

class MyOne (α : Type) where
  one : α 

class MyOfNat (α : Type) (_ : Nat) where
  ofNat : α

/- instances -/

-- Zero instance doesn't make any sense for Pos

instance : One Pos where
  one := Pos.one

-- intermezzo

inductive LT4 where
  | zero
  | one
  | two
  | three

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (0 : LT4)
#eval (1 : LT4)
#eval (2 : LT4)
#eval (3 : LT4)

#eval (4 : LT4)

-- For Pos, the OfNat instance should work for any Nat other than Nat.zero.
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0     => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n
    
-- Pos doesn't have a zero
def zero  : Pos := 0

def one   : Pos := 1
def two   : Pos := 2
def three : Pos := 3
def four  : Pos := 4
def five  : Pos := 5
def six   : Pos := 6
def seven : Pos := 7
def eight : Pos := 8
-- …

/- --------- -/
/- Exercises -/
/- --------- -/

-- Another Representation

structure Pos1 where
  succ ::
  pred : Nat

-- Define instances of Add, Mul, ToString, and OfNat that allow this version of Pos to be used conveniently.

def altOne   := Pos1.succ 0
def altTwo   := Pos1.succ 1
def altThree := Pos1.succ 2
def altFour  := Pos1.succ 3
def altFive  := Pos1.succ 4
def altSix   := Pos1.succ 5

#eval altOne   
#eval altTwo   
#eval altThree 
#eval altFour  
#eval altFive  
#eval altSix   

/- Addition -/

def Pos1.plus : Pos1 → Pos1 → Pos1
  | Pos1.succ n, Pos1.succ m => Pos1.succ (n + m + 1)

instance : Add Pos1 where
  add := Pos1.plus
  
#eval altOne + altOne
#eval altTwo + altOne
#eval altTwo + altTwo
#eval altSix + altSix

/- Multiplication -/

def Pos1.mul : Pos1 → Pos1 → Pos1
  | Pos1.succ n, Pos1.succ m => Pos1.succ ((n + 1) * (m + 1) - 1)

instance : Mul Pos1 where
  mul := Pos1.mul

#eval altOne * altOne
#eval altTwo * altOne
#eval altTwo * altTwo
#eval altSix * altSix

instance : OfNat Pos1 (n + 1) where
  ofNat := 
   match n with
   | 0 => Pos1.succ 0
   | m => Pos1.succ m

-- Pos1 doesn't have a zero
def zero1  : Pos1 := 0

def one1   : Pos1 := 1
def two1   : Pos1 := 2
def three1 : Pos1 := 3
def four1  : Pos1 := 4
def five1  : Pos1 := 5
def six1   : Pos1 := 6
def seven3 : Pos1 := 7
def eight1 : Pos1 := 8
-- …

instance : ToString Pos1 where
  toString x := toString (x.pred + 1)

#eval s!"There are {one1}"  
#eval s!"There are {two1}"  
#eval s!"There are {three1}"
#eval s!"There are {four1}" 
#eval s!"There are {five1}" 
#eval s!"There are {six1}"  
#eval s!"There are {seven3}"
#eval s!"There are {eight1}"

/- Even Numbers -/

-- Define a datatype that represents only even numbers.
-- Define instances of Add, Mul and ToString that allow it to be used conveniently.

-- Christian wants an inductive type definition
-- https://proofassistants.stackexchange.com/questions/2435/recursive-type-class-for-ofnat-even
-- https://github.com/James-Oswald/Functional-Programming-In-Lean/blob/lean-3.51.1/src/4.2.lean

structure Even where
  even : Nat

def evenZero   := Even.mk 0
def evenTwo    := Even.mk 1
def evenFour   := Even.mk 2
def evenSix    := Even.mk 3
def evenEight  := Even.mk 4
def evenTen    := Even.mk 5
def evenTwelve := Even.mk 6

#eval evenZero   
#eval evenTwo    
#eval evenFour   
#eval evenSix    
#eval evenEight  
#eval evenTen    
#eval evenTwelve 

def Even.plus : Even → Even → Even 
| Even.mk n, Even.mk m => Even.mk (((2 * n) + (2 * m)) / 2)

instance : Add Even where
  add := Even.plus

#eval evenZero   + evenZero  
#eval evenZero   + evenTwo   
#eval evenTwo    + evenTwo   
#eval evenEight  + evenSix   
#eval evenTwelve + evenSix   
#eval evenTwelve + evenTwelve

instance : ToString Even where
  toString e := toString (2 * e.even)

#eval s!"There are {evenZero}"  
#eval s!"There are {evenTwo}"   
#eval s!"There are {evenFour}"  
#eval s!"There are {evenSix}"   
#eval s!"There are {evenEight}" 
#eval s!"There are {evenTen}"   
#eval s!"There are {evenTwelve}"

/- HTTP Requests -/

-- TBD ;-)

/- ----------------------------- -/
/- Type Classes and Polymorphism -/
/- ----------------------------- -/

/- ----------------------------------- -/
/- Checking Polymorphic Function Types -/
/- ----------------------------------- -/

-- couldn't figure out type of implicit arguments -> prints metavariables
#check (IO.println)

-- signature without metavariables
#check @IO.println

/- ------------------------------------------------------ -/
/- Defining Polymorphic Functions with Instance Implicits -/
/- ------------------------------------------------------ -/

def List.sumOfContents1 [Add α] [OfNat α 0] : List α → α
  | []      => 0
  | x :: xs => x + xs.sumOfContents1

def List.sumOfContents2 [Add α] [Zero α] : List α → α
  | []      => 0
  | x :: xs => x + xs.sumOfContents2

def fourNats : List Nat := [1, 2, 3, 4]

#eval fourNats.sumOfContents1
#eval fourNats.sumOfContents2

def fourPos : List Pos := [1, 2, 3, 4]

-- Pos doesn't have zeros
#eval fourPos.sumOfContents1
#eval fourPos.sumOfContents2

-- this function is in the standard library
#check List.sum

-- Specifications of required instances in square brackets are called INSTANCE IMPLICITS.

-- The most important difference between ordinary IMPLICIT ARGUMENTS and INSTANCE IMPLICITS is the strategy that Lean uses to find an argument value.
-- In the case of ordinary IMPLICIT ARGUMENTS, Lean uses a technique called UNIFICATION to find a single unique argument value that would allow the program to pass the type checker.
-- This process relies only on the specific types involved in the function's definition and the call site.
-- For INSTANCE IMPLICITS, Lean instead consults a built-in table of instance values.

structure PPoint (α : Type) where
  x : α
  y : α

--     α must also be addable
--           ^^^^^^^
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

/- ------------------------------  -/
/- Methods and Implicit Arguments  -/
/- ------------------------------  -/

-- The type parameter α can be implicit because the arguments to Add.add provide information about which type the user intended. 
#check Add.add 

-- In the case of OfNat.ofNat, the particular Nat literal to be decoded does not appear as part of any other parameter's type.
-- This means that Lean would have no information to use when attempting to figure out the implicit parameter n.
-- In this case, Lean uses an explicit parameter for the class's method.
--                                                     ^^^^^^^^^^
#check OfNat.ofNat

/- --------- -/
/- Exercises -/
/- --------- -/

-- see solution for inductive type
-- https://proofassistants.stackexchange.com/questions/2435/recursive-type-class-for-ofnat-even
-- https://github.com/James-Oswald/Functional-Programming-In-Lean/blob/lean-3.51.1/src/4.2.lean

-- Even Number Literals

instance : OfNat Even n where
  ofNat := Even.mk (n / 2)

/- --------------------------- -/
/- Controlling Instance Search -/
/- --------------------------- -/

def addNatPos : Nat → Pos → Pos
  | 0, p     => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0     => p
  | p, n + 1 => Pos.succ (addPosNat p n)

#eval addNatPos 5 4
#eval addPosNat 5 4

/- -------------------------- -/
/- Heterogeneous Overloadings -/
/- -------------------------- -/

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Nat) + (5 : Nat)
#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)
#eval (3 : Pos) + (5 : Pos)

class HPlus1 (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ
  
instance : HPlus1 Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus1 Pos Nat Pos where
  hPlus := addPosNat

-- Note: metavariables represent unknown parts of a program that could not be inferred
-- see error message from language server
#eval HPlus1.hPlus (3 : Pos) (5 : Nat)

-- with (unconvenient) type annotations
#eval (HPlus1.hPlus (3 : Pos) (5 : Nat) : Pos)

/- ----------------- -/
/- Output Parameters -/
/- ----------------- -/

-- Most type class parameters are inputs to the search algorithm: they are used to select an instance.

-- In some cases, it can be convenient to start the search process even when some of the type parameters
-- are not yet known, and use the instances that are discovered in the search to determine values for metavariables.

-- The parameters that aren't needed to start instance search are outputs of the process, which is declared with
-- the outParam modifier.

class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

-- With this output parameter, type class instance search is able to select an instance without knowing γ in advance.
#eval HPlus.hPlus (3 : Pos) (5 : Nat)

/- ----------------- -/
/- Default Instances -/
/- ----------------- -/

-- Default instances are instances that are available for instance search even when not all their inputs are known. 

-- When one of these instances can be used, it will be used.

instance [Add α] : HPlus α α α where
  hPlus := Add.add

-- With this instance, hPlus can be used for any addable type, like Nat:
#eval HPlus.hPlus (3 : Nat) (5 : Nat)

#check HPlus.hPlus (5 : Nat) (3 : Nat)
#check HPlus.hPlus (5 : Nat)

--In the vast majority of cases, when someone supplies one argument to addition, the other argument will have the same type.
-- To make this instance into a default instance, apply the `default_instance` attribute.

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

#check HPlus.hPlus (5 : Nat)

-- Default instances can also be assigned priorities that affect which will be chosen in situations where more than one might apply.
-- For more information on default instance priorities, please consult the Lean manual.

/- --------- -/
/- Exercises -/
/- --------- -/

-- TBD

/- =================== -/
/- Arrays and Indexing -/
/- =================== -/

/- ------ -/
/- Arrays -/
/- ------ -/

def northernTrees : Array String := #["sloe", "birch", "elm", "oak"]

#eval northernTrees.size 

#eval northernTrees[0]
#eval northernTrees[1]
#eval northernTrees[2]
#eval northernTrees[3]

#eval northernTrees[4]

/- --------------- -/
/- Non-Empty Lists -/
/- --------------- -/

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0                              => some xs.head
  | {head := _, tail := []}, _ + 1     => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n

def NonEmptyList.get1? : NonEmptyList α → Nat → Option α
  | xs, 0     => some xs.head
  | xs, n + 1 => xs.tail[n]?

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders :  idahoSpiders.inBounds 2 := by decide
theorem notSixSpiders       : ¬idahoSpiders.inBounds 5 := by decide

-- check at compile-time - Option not required
def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0     => xs.head
  | n + 1 => xs.tail[n]

/- -------------------- -/
/- Overloading Indexing -/
/- -------------------- -/

class MyGetElem
    (coll     : Type)
    (idx      : Type)
    (item     : outParam Type)
    (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

-- NonEmptyList becomes just as convenient to use as List 
#eval idahoSpiders.head
#eval idahoSpiders[0]  
#eval idahoSpiders[1]  
#eval idahoSpiders[2]  
#eval idahoSpiders[3]  
#eval idahoSpiders[4]  

#eval idahoSpiders[5]  

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]

def carBrands := ["BMW", "Mercedes", "VW"]

#eval carBrands[one]
#eval carBrands[two]

#eval carBrands[three]

-- using Bool as an index type
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ := if not i then p.x else p.y
  
def p1 := { x := 1, y := 2 : PPoint Nat}

#eval p1[false]
#eval p1[true] 


/- ================ -/
/- Standard Classes -/
/- ================ -/

/- ---------- -/
/- Arithmetic -/
/- ---------- -/

-- -----------|---------------|------------
-- Expression | Desugaring    | Class Name
-- -----------|---------------|------------
-- x + y      | HAdd.hAdd x y | HAdd
-- x - y      | HSub.hSub x y | HSub
-- x * y      | HMul.hMul x y | HMul
-- x / y      | HDiv.hDiv x y | HDiv
-- x % y      | HMod.hMod x y | HMod
-- x ^ y      | HPow.hPow x y | HPow
-- - x        | Neg.neg x     | Neg
-- -----------|---------------|------------

/- ----------------- -/
/- Bitwise Operators -/
/- ----------------- -/

-- -----------|----------------------------|--------------
-- Expression | Desugaring                 | Class Name
-- -----------|----------------------------|--------------
-- x &&& y    | HAnd.hAnd x y              | HAnd
-- x ||| y    | HOr.hOr x y                | HOr
-- x ^^^ y    | HXor.hXor x y              | HXor
-- ~~~x       | Complement.complement x    | Complement
-- x >>> y    | HShiftRight.hShiftRight x y| HShiftRight
-- x <<< y    | HShiftLeft.hShiftLeft x y  | HShiftLeft
-- -----------|----------------------------|--------------

-- The homogeneous versions of HAnd and HOr are called AndOp and OrOp rather than And and Or.

/- --------------------- -/
/- Equality and Ordering -/
/- --------------------- -/

-- BEq = Boolean Equality '=='
-- Propositional Equality needs a proof '='

-- Boolean Equality yields a boolean value (true/false)
#eval "Octopus"   ==  "Cuttlefish"         
#eval "Octopodes" ==  "Octo".append "podes"

-- functions cannot be checked for equality
#eval (fun (x : Nat) => 1 + x) == (Nat.succ ·)

-- The expression x == y is shorthand for BEq.beq x y.

-- we have to provide a proof that they are the same functions
#eval (fun (x : Nat) => 1 + x) = (Nat.succ ·)

-- a proposition
#check 2 < 4

-- but perfectly acceptable
#eval if 2 < 4 then 1 else 2

-- not decidable
#eval if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"

-- The following propositions, that are usually decidable, are overloaded with type classes.

-- -----------|------------|------------
-- Expression | Desugaring | Class Name
-- -----------|------------|------------
-- x < y      | LT.lt x y  | LT
-- x ≤ y      | LE.le x y  | LE
-- x > y      | LT.lt y x  | LT
-- x ≥ y      | LE.le y x  | LE
-- -----------|------------|------------

instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat

instance : LE Pos where
  le x y := LE.le x.toNat y.toNat

-- These propositions are not decidable by default because Lean doesn't unfold the definitions
-- of propositions while synthesizing an instance.
#eval (1 : Pos) < (2 : Pos)

-- can be bridged using the inferInstanceAs operator, which finds an instance for a given class if it exists
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))

instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat ≤ y.toNat))

#eval (1 : Pos) < (2 : Pos)

-- The type checker confirms that the definitions of the propositions match. Confusing them results in an error.
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))

inductive MyOrdering where
  | lt
  | eq
  | gt

def Pos.comp : Pos → Pos → Ordering
  | Pos.one,    Pos.one    => Ordering.eq
  | Pos.one,    Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one    => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp

/- ------- -/
/- Hashing -/
/- ------- -/

class MyHashable (α : Type) where
  hash : α → UInt64

-- The standard library contains a function mixHash with type UInt64 → UInt64 → UInt64 that can be used to combine hashes for different fields for a constructor.
def hashPos : Pos → UInt64
  | Pos.one    => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

-- using recursive instance search
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

-- Binary trees use both recursion and recursive instance search in the implementations of BEq and Hashable
inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf                    => true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 => x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ => false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf                => 0
  | BinTree.branch left x right =>
    mixHash 1
      (mixHash (hashBinTree left)
        (mixHash (hash x)
          (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

/- ------------------------- -/
/- Deriving Standard Classes -/
/- ------------------------- -/

deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList

-- Instances can be derived for at least the following classes:
--  · Inhabited
--  · BEq
--  · Repr
--  · Hashable
--  · Ord

/- --------- -/
/- Appending -/
/- --------- -/

class MyHAppend (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ

-- The syntax xs ++ ys desugars to HAppend.hAppend xs ys.
-- For homogeneous cases, it's enough to implement an instance of Append.

instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys := { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["Trapdoor Spider"]

/- -------- -/
/- Functors -/
/- -------- -/

#eval Functor.map (· + 5) [1, 2, 3]                     
#eval Functor.map toString (some (List.cons 5 List.nil))
#eval Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]   

-- with infix operator <$>
#eval (· + 5) <$> [1, 2, 3]                     
#eval toString <$> (some (List.cons 5 List.nil))
#eval List.reverse <$> [[1, 2, 3], [4, 5, 6]]   


instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

-- default method definitions

def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | []        => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail

-- Default method definitions contain := in a class definition.

class MyFunctor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  -- default method definition
  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

deriving instance ToString for NonEmptyList

/- --------- -/
/- Exercises -/
/- --------- -/

/- ========= -/
/- Coercions -/
/- ========= -/

-- When Lean encounters an expression of one type in a context that expects a different type,
-- it will attempt to coerce the expression before reporting a type error.

-- The coercions are extensible by defining instances of type classes.

/- ----------------- -/
/- Strings and Paths -/
/- ----------------- -/

def fileDumper : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "Which file? "
  stdout.flush
  let f := (← stdin.getLine).trimAscii.copy
  stdout.putStrLn s!"'The file {f}' contains:"
  stdout.putStrLn (← IO.FS.readFile f) -- automatic coercion from String to FilePath; not necessary to write IO.FS.readFile ⟨f⟩

/- ---------------- -/
/- Positive Numbers -/
/- ---------------- -/

-- List.drop expects a Nat (author could have used a type class)
#eval [1, 2, 3, 4].drop (2 : Pos)

-- type class Coe describes overloaded ways of coercing from one type to another
class MyCoe (α : Type) (β : Type) where
  coe : α → β

instance : Coe Pos Nat where
  coe x := x.toNat

#eval [1, 2, 3, 4].drop (2 : Pos)

-- Pos.toNat was used
#check [1, 2, 3, 4].drop (2 : Pos)

/- ------------------ -/
/- Chaining Coercions -/
/- ------------------ -/

-- There is already a coercion from Nat to Int.
-- Because of that instance, combined with the Coe Pos Nat instance, allows:
def oneInt : Int := Pos.one

-- even circular coercions work
inductive A where
  | a

inductive B where
  | b

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()

#eval coercedToB

-- The Lean standard library defines a coercion from any type α to Option α that wraps the value in some. 

def List.last? : List α → Option α
  | []       => none
  | [x]      => x -- `some` not necessary
  | _ :: xs  => last? xs

#eval List.last? ([] : List Nat)
#eval List.last? [1]            
#eval List.last? [1, 2]         
#eval List.last? [1, 2, 3]      

-- these coercions can be chained
def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"

#eval perhapsPerhapsPerhaps

-- automatic coercions not used
def perhapsPerhapsPerhapsNat1 : Option (Option (Option Nat)) :=
  392

-- telling what type `392` is results in automatic coercion
def perhapsPerhapsPerhapsNat2 : Option (Option (Option Nat)) :=
  (392 : Nat) 

-- explicit/manual coercion
def perhapsPerhapsPerhapsNat3 : Option (Option (Option Nat)) :=
  ↑(392 : Nat)

/- --------------------------------------- -/
/- Non-Empty Lists and Dependent Coercions -/
/- --------------------------------------- -/

-- allows non-empty lists to be used with the entire List API(!)
instance : Coe (NonEmptyList α) (List α) where
  coe
  | { head := x, tail := xs } => x :: xs

-- On the other hand, it is impossible to write an instance of Coe (List α) (NonEmptyList α), because there's no non-empty list that can represent the empty list.
-- This limitation can be worked around by using another version of coercions, which are called DEPENDENT COERCIONS.

-- dependent coercion takes the value being coerced as a parameter
class MyCoeDep (α : Type) (x : α) (β : Type) where
  coe : β

-- non-empty Lists can be coerced to a NonEmptyList
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }

/- ----------------- -/
/- Coercing to Types -/
/- ----------------- -/

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }

def foldMap1 (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs 

-- The CoeSort class is just like the Coe class, with the exception that the target of the coercion must be a sort, namely Type or Prop.
-- The term sort in Lean refers to these types that classify other types.
instance : CoeSort Monoid Type where
  coe m := m.Carrier

-- with this coercion, the type signatures become less bureaucratic
def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

-- Another useful example of CoeSort is used to bridge the gap between Bool and Prop.
-- Lean's if expression expects the condition to be a decidable proposition rather than a Bool. 

-- CoeSort allows us to use bools in if expressions.

instance : Coe Bool Prop where
  coe b := Eq b true

instance : CoeSort Bool Prop where
  coe b := b

/- --------------------- -/
/- Coercing to Functions -/
/- --------------------- -/

class MyCoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x

structure Adder where
  howMuch : Nat

def add5 : Adder := ⟨5⟩

#eval add5

-- Adder type is not a function
#eval add5 3

instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)

#eval add5 3

inductive JSON where
  | true   : JSON
  | false  : JSON
  | null   : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array  : List JSON → JSON

-- a JSON serializer is a structure that tracks the type it knows how to serialize along with the serialization code itself
structure JSONSerializer where
  Contents  : Type
  serialize : Contents → JSON

-- string serializer
def StrSerializer : JSONSerializer :=
  { Contents  := String,
    serialize := JSON.string
  }

-- JSON serializer as function
instance : CoeFun JSONSerializer (fun s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title : String) (R : JSONSerializer) (record : R.Contents) : JSON :=
  JSON.object [ ("title",  JSON.string title),
                ("status", JSON.number 200),
                ("record", R record)] -- a serializer can now be applied directly to an argument(!)

#eval buildResponse "Functional Programming in Lean" StrSerializer "Programming is fun!"

/- ----------------------- -/
/- Aside: JSON as a String -/
/- ----------------------- -/

#eval (5 : Float).toString

def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropEndWhile (· == '0')
    (noTrailingZeros.dropEndWhile (· == '.')).copy
  else numString

#eval dropDecimals (5   : Float).toString
#eval dropDecimals (5.2 : Float).toString

def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | []      => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))

#eval String.separate    ", " ["a", "b", "c"]
#eval String.intercalate ", " ["a", "b", "c"]

#eval ", ".separate []           
#eval ", ".separate ["1"]        
#eval ", ".separate ["1", "2"   ]

#eval ", ".intercalate []        
#eval ", ".intercalate ["1"]     
#eval ", ".intercalate ["1", "2"]

-- `partial` because Lean cannot see that it terminates
partial def JSON.asString (val : JSON) : String :=
  match val with
  | true           => "true"
  | false          => "false"
  | null           => "null"
  | string s       => "\"" ++ Lean.Json.escape s ++ "\""
  | number n       => dropDecimals n.toString
  | array elements => "[" ++ ", ".separate (elements.map asString) ++ "]"
  | object members => let memberToString mem := "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
                      "{" ++ ", ".separate (members.map memberToString) ++ "}"

#eval (buildResponse "Functional Programming in Lean" StrSerializer "Programming is fun!").asString

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

-- Natural number literals are overloaded with the OfNat type class.
-- Because coercions fire in cases where types don't match, rather
-- than in cases of missing instances, a missing OfNat instance for
-- a type does not cause a coercion from Nat to be applied.

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  392

/- --------------------- -/
/- Design Considerations -/
/- --------------------- -/

-- When a coercion is not applied for some reason, the user receives the original type error,
-- which can make it difficult to debug chains of coercions.

-- with type annotations
def lastSpider1 : Option String :=
  List.getLast? idahoSpiders


-- without type annotations
def lastSpider2 :=
  List.getLast? idahoSpiders

-- Note: coercions are not applied in the context of field accessor notation.

/- ======================= -/
/- Additional Conveniences -/
/- ======================= -/

/- -------------------------------- -/
/- Constructor Syntax for Instances -/
/- -------------------------------- -/

structure Tree : Type where
  latinName   : String
  commonNames : List String

-- useful when emphasizing that a structure type is tuple alike
def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

-- idiomatic
def birch : Tree :=
  { latinName   := "Betula pendula",
    commonNames := ["silver birch", "warty birch"]
  }

-- idiomatic
def sloe : Tree where
  latinName   := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]

-- Behind the scenes, type classes are structure types and instances are values of these types.

-- same syntaxes allowed
class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

-- idiomatic
instance : Display Tree where
  displayName t := t.latinName

/- -------- -/
/- Examples -/
/- -------- -/

-- An example is like a definition without a name.

-- In source files, example declarations are best paired with comments that
-- explain how the example illustrates the concepts of the library.

example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]
  }

-- function example, but cannot be called
example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
