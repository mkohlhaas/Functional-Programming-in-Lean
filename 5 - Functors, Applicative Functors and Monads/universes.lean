/- ========= -/
/- Universes -/
/- ========= -/

-- A universe is a type that classifies other types.
-- Two of them are familiar: Type and Prop.
-- Type classifies ordinary types                        , such as Nat, String, Int → String × Char, IO Unit, …
-- Prop classifies propositions that may be true or false, such as "nisse" = "elf", 3 > 2, …

-- The whole point of the universe system is to rule out self-referential types. 

-- the type of Prop is Type
#check Prop

#check Type  
#check Type 1
#check Type 2
#check Type 3
-- …

-- Function types occupy the smallest universe that can contain both the argument type and the return type. 
#check Nat → Nat      
#check Type → Type    
#check Type 1 → Type 2

-- There is one exception to this rule.
-- If the return type of a function is a Prop, then the whole function type is in Prop.
#check (n : Nat) → n = n + 0
#check Type → 2 + 2 = 4     

/- ------------------ -/
/- User Defined Types -/
/- ------------------ -/

inductive MyList (α : Type) : Type where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

-- MyList is a Type → Type
#check MyList

-- it cannot be used to contain actual types
def myListOfNat : MyList Type := .cons Nat .nil

-- the argument to cons with type α is from a larger universe than MyList
inductive MyList' (α : Type 1) : Type where
  | nil  : MyList' α
  | cons : α → MyList' α → MyList' α

-- The specific rules that govern whether a datatype is allowed are somewhat complicated.
-- Generally speaking, it's easiest to start with the datatype in the same universe as the largest of its arguments.
-- Then, if Lean rejects the definition, increase its level by one, which will usually go through.

/- --------------------- -/
/- Universe Polymorphism -/
/- --------------------- -/

-- Type arguments are conventionally named with Greek letters.
-- Universe arguments are conventionally named u, v, and w.

inductive MyList'' (α : Type u) : Type u where
  | nil  : MyList'' α
  | cons : α → MyList'' α → MyList'' α

def myListOfNumbers : MyList'' Nat           := .cons 0 (.cons 1 .nil)
def myListOfNat'    : MyList'' Type          := .cons Nat .nil
def myListOfList    : MyList'' (Type → Type) := .cons MyList'' .nil

-- level arguments are written with a dot and curly braces
#check MyList.{0}

def myListOfNumbers' : MyList''.{0} Nat           := .cons 0 (.cons 1 .nil)
def myListOfNat''    : MyList''.{1} Type          := .cons Nat .nil
def myListOfList'    : MyList''.{1} (Type → Type) := .cons MyList''.{0} .nil

inductive MySum (α : Type u) (β : Type u) : Type u where
  | inl : α → MySum α β
  | inr : β → MySum α β

def stringOrNat  : MySum String Nat  := .inl "hello"
def typeOrType   : MySum Type Type   := .inr Nat
def stringOrType : MySum String Type := .inr Nat -- both arguments must be in the same universe

inductive MySum' (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → MySum' α β
  | inr : β → MySum' α β

def stringOrType' : MySum' String Type := .inr Nat -- arguments from different universes possible


-- In positions where Lean expects a universe level, any of the following are allowed:
-- · a concrete level, like 0 or 1
-- · a variable that stands for a level, such as u or v
-- · the maximum of two levels, written as max applied to the levels
-- · a level increase, written with + 1

/- ---------------------------------------- -/
/- Writing Universe-Polymorphic Definitions -/
/- ---------------------------------------- -/

/- --------------------- -/
/- Prop and Polymorphism -/
/- --------------------- -/

-- Prop is at the bottom of the universe hierarchy, and the type of Prop is Type.
-- This means that Prop is a suitable argument to provide to List, for the same reason that Nat is.

-- Lists of propositions have type List Prop.
def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]

-- Prop is a Type.
-- Behind the scenes, Prop and Type are united into a single hierarchy called Sort.
def someTruePropositions' : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]

/- ------------------------ -/
/- Polymorphism in Practice -/
/- ------------------------ -/
