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
