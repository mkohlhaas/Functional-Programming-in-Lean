def woodlandCritters : List String := ["hedgehog", "deer", "snail"]

#eval woodlandCritters

def hedgehog := woodlandCritters[0]
def deer     := woodlandCritters[1]
def snail    := woodlandCritters[2]

#eval woodlandCritters.length

#eval hedgehog
#eval deer
#eval snail

-- Compile-time error!
def oops := woodlandCritters[3]

-- A PROPOSITION is a statement that can be true or false.
-- In Lean, propositions are types, types are propositions.

#eval 1 + 1 = 2

-- The evidence for this proposition is the constructor `rfl`, which is short for reflexivity.
-- In mathematics, a relation is reflexive if every element is related to itself.
-- This is a basic requirement in order to have a sensible notion of equality.
-- Because 1 + 1 computes to 2, they are really the same thing

-- From Wikipedia:
-- In mathematics, a binary relation R {\displaystyle R} on a set X is reflexive if it relates every element of X to itself.
-- An example of a reflexive relation is the relation "is equal to" on the set of real numbers, since every real number is equal to itself.
-- A reflexive relation is said to have the reflexive property or is said to possess reflexivity.
-- Along with symmetry and transitivity, reflexivity is one of three properties defining equivalence relations.

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

def onePlusOneIsFifteen : 1 + 1 = 15 := rfl

-- Just as Type describes types such as Nat, String, and List (Nat × String × (Int → Float)) that represent data structures and functions,
-- Prop describes propositions.

-- When a proposition has been proven, it is called a theorem.
-- In Lean, it is conventional to declare theorems with the `theorem` keyword instead of `def`.

def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo1 : 1 + 1 = 2 := rfl

theorem onePlusOneIsTwo2 : OnePlusOneIsTwo := rfl

-- Proofs are normally written using TACTICS, rather than by providing evidence directly.
-- TACTICS are small programs that construct evidence for a proposition.

-- onePlusOneIsTwo written with TACTICS
theorem onePlusOneIsTwo3 : 1 + 1 = 2 := by
  decide

-- TACTICS used in this book:
-- decide -> invokes a decision procedure that can check whether a statement is true or false
-- simp   -> short for simplify
-- grind  -> can automatically prove many theorems

-- The basic building blocks of logic, such as “and”, “or”, “true”, “false”, and “not”, are called logical CONNECTIVES.

-- Most of these connectives are defined like datatypes, and they have constructors.
-- If A and B are propositions, then A ∧ B is a proposition.
-- Evidence for A ∧ B consists of the constructor And.intro, which has the type A → B → A ∧ B.

-- with And.intro
theorem addAndAppend1 : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := And.intro rfl rfl

-- with decide
theorem addAndAppend2 : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide

-- A ∨ B has two constructors:
-- Or.inl with type A → A ∨ B
-- Or.inr with type B → A ∨ B

-- Implication A → B is shorthand for ¬A ∨ B in traditional logic.
-- In Lean implication is represented using functions.
-- In particular, a function that transforms evidence for A into evidence for B is itself evidence that A implies B.
-- The two formulations are equivalent.

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _b => Or.inl a

-- Connective  | Lean Syntax        | Evidence
-- ----------- | ------------------ | ----------------------------------------------------------------------
-- True        | True               | True.intro : True
-- False       | False              | No evidence
-- A and B     | A ∧ B              | And.intro : A → B → A ∧ B
-- A or B      | A ∨ B              | Either Or.inl : A → A ∨ B or Or.inr : B → A ∨ B
-- A implies B | A → B              | A function that transforms evidence of A into evidence of B
-- not A       | ¬A                 | A function that would transform evidence of A into evidence of False

-- The decide tactic can prove theorems that use these connectives:
theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive      : ¬(1 + 1 = 5)      := by decide
theorem trueIsTrue           : True              := by decide
theorem trueOrFalse          : True ∨ False      := by decide
theorem falseImpliesTrue     : False → True      := by decide

def third1 (xs : List α) : α := xs[2]

-- the obligation to show that the list has at least three entries can be imposed on the caller
-- xs.length > 2 is NOT a program that checks whether xs has more than 2 entries.
-- It is a proposition that could be true or false, and the argument ok must be evidence that it is true.
def third2 (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- decide can construct the evidence automatically
#eval third2 woodlandCritters (by decide)

/- ------------------------- -/
/- Indexing Without Evidence -/
/- ------------------------- -/

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters
#eval thirdOption ["only", "two"]

/- There is also a version that crashes the program when the index is out of bounds, rather than returning an Option: -/
#eval woodlandCritters[1]!
#eval woodlandCritters[2]!
#eval woodlandCritters[3]!

-- decide can proof a proposition to be true, but also to be false
#eval third2 ["rabbit"] (by decide)

-- The simp and decide tactics do not automatically unfold definitions with def.
theorem onePlusOneIsStillTwo1 : OnePlusOneIsTwo := by simp
theorem onePlusOneIsStillTwo2 : OnePlusOneIsTwo := by decide


-- definitions written with `abbrev` are always unfolded
abbrev OnePlusOneIsTwo1 : Prop := 1 + 1 = 2

theorem onePlusOneIsStillTwo3 : OnePlusOneIsTwo1 := by simp
theorem onePlusOneIsStillTwo4 : OnePlusOneIsTwo1 := by decide


-- polymorphic function
-- In Lean only programs whose types contain at least one value are allowed to crash.
-- If a program with an empty type could crash, then that crashing program could be used as a kind of fake evidence for a false proposition.
def unsafeThird (xs : List α) : α := xs[2]!

-- whitespace between list and brackets
#eval woodlandCritters[1]
#eval woodlandCritters [1] -- Lean attempts to treat woodlandCritters as a function

/- --------- -/
/- Exercises -/
/- --------- -/

-- rfl is about equality
theorem ex1 : 2 + 3 = 5                                 := by rfl
theorem ex2 : 15 - 8 = 7                                := by rfl
theorem ex3 : "Hello, ".append "world" = "Hello, world" := by rfl
theorem ex4 : 5 < 18                                    := by rfl

-- the same with decide
theorem ex5 : 2 + 3 = 5                                 := by decide
theorem ex6 : 15 - 8 = 7                                := by decide
theorem ex7 : "Hello, ".append "world" = "Hello, world" := by decide
theorem ex8 : 5 < 18                                    := by decide

def fifth (xs : List α) (ok : xs.length > 5) : α := xs[5]
