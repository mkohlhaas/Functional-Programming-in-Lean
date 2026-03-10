/- ============ -/
/- The IO Monad -/
/- ============ -/

-- exterior perspective:
-- An IO action is an instruction to Lean's run-time system.

-- interior perspective:
-- An IO action transforms the whole world.
-- IO actions are actually pure, bc they receive a unique world as an argument and then return the changed world.

-- #print reveals the internals of Lean datatypes and definitions
#print Nat         
#print Char.isAlpha
#print List.isEmpty
#print IO          
#print IO.Error    
-- EIO ε α represents IO actions that will either terminate with an error of type ε or succeed with a value of type α.
#print EIO         
-- A program with type EST ε σ α is a function that accepts an initial state of type σ and returns an EST.Out ε σ α. 
-- The state is wrapped in the type Void, which is an internal primitive that causes a value to be erased from compiled code; Void σ has the same representation as Unit.
#print EST         
#print EST.Out     
-- protected means that the full name EST.pure is needed even if the EST namespace has been opened.
#print EST.pure    
#print EST.bind    

-- Putting all of this together, IO is a monad that tracks state and errors at the same time.
-- The state is a type that represents the real world, called IO.RealWorld.
-- The type IO.RealWorld is a trivial primitive type that does not need any representation, bd it's only used inside of Void. 

