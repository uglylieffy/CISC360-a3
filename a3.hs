-- CISC 360 a3, Fall 2021

-- SEE THE FILE a3.pdf
-- for instructions

module A3
where
import Data.List

-- Q1:
-- Add your student ID (if in a group of 2, write the second student's ID in a comment):
student_id :: Integer
student_id = 20150516

-- THIS FILE WILL NOT COMPILE UNTIL YOU ADD YOUR STUDENT ID ABOVE.

{-
Q2: Truth Tables

To build a truth table for a formula, there are 4 steps:

  1) Traverse the formula to find all atomic propositions (propositional variables).

  2) Find all the possible valuations---combinations of True and False
      for the atomic propositions in the formula.

  3) Evaluate the formula for each valuation obtained in (2).

  4) Use the results of (1-3) to build the table.

In this question, you will implement steps (1-3).
-}

-- Variable is a synonym for String.
type Variable = String

-- In our simplified version of classical propositional logic,
-- we have the following definition for a Formula:
data Formula = Top                          -- truth
             | Bot                          -- falsehood (contradiction)
             | And Formula Formula          -- conjunction
             | Or Formula Formula           -- disjunction
             | Implies Formula Formula      -- implication
             | Equiv Formula Formula        -- equivalence ("if and only if")
             | Not Formula                  -- negation
             | Atom Variable                -- atomic proposition (propositional variable)
             deriving (Eq, Show)

-- Some propositional variables, for convenience
vA = Atom "A"
vB = Atom "B"
vC = Atom "C"
vD = Atom "D"
vE = Atom "E"
vF = Atom "F"

-- Some example formulas that you can use to test your functions
formula1  = Implies (And vA vB) vC
formula2  = Implies Bot (And vA vB)
formula3  = Implies (And vA vB) Top
formula4  = And (Implies vA (And vB vC)) (And vD vE)
formula5  = And vA vB
formula6  = Not vA
formula7  = Implies vA vB
formula8  = Or vA (Not vA)
formula9  = Or vA (Not vB)
formulaAB = Equiv vA vB
formulaBC = Equiv vB vC
formulaAC = Equiv vA vC
formula10 = Implies (And formulaAB formulaBC) formulaAC

-- A Valuation is a list of pairs corresponding to a truth value (i.e. True or False)
--  for each Variable in a formula
type Valuation = [(Variable, Bool)]

-- A TruthTable is an enumeration of the valuations for a given formula,
-- with each valuation paired with the corresponding evaluation of that formula.
-- (This corresponds to a truth table with no "intermediate columns".)
data TruthTable = TruthTable [(Valuation, Bool)]

{-
   This function is here so that when you print a TruthTable in GHCi, the table is nice and readable.
   You don't need to understand how this works to complete the assignment.
-}
instance Show TruthTable where
  show (TruthTable rows) =
    case rows of
      [] -> ""
      ([], result) : _ -> "   result is " ++ pad_show result ++ "\n"
      ((c,b) : valu, result) : xs -> 
        c ++ "=" ++ (pad_show b) ++ "   "
          ++ show (TruthTable [(valu,result)])
          ++ show (TruthTable xs)
    where
      pad_show True  = "True "
      pad_show False = "False"

{-
  Q2a: getAtoms:

  Traverse a formula and build a list of all Atoms in the formula, without duplicates.

  You may use the built-in function "nub", which takes a list and returns the list
  without duplicates.
-}

getAtoms :: Formula -> [Variable]

getAtoms Top               = []
getAtoms Bot               = []

getAtoms (Atom v)          = [v]

getAtoms (Not phi)         = getAtoms(phi)
getAtoms (And phi1 phi2)   = nub((getAtoms(phi1))++(getAtoms(phi2)))  -- simply return only variables
getAtoms (Or phi1 phi2)    = nub((getAtoms(phi1))++(getAtoms(phi2))) -- similar to above, it still will return phi1 & phi2's atoms
getAtoms (Implies phi psi) = nub((getAtoms(phi))++(getAtoms(psi))) -- same idea as above
getAtoms (Equiv phi1 phi2) = nub((getAtoms(phi1))++(getAtoms(phi2)))  -- same idea as above

{-
   Q2b: getValuations:

   Build a list of all possible valuations for a set of variables
-}
getValuations :: [Variable] -> [Valuation]
getValuations []       = [[]]
                          -- assign True and False to every elemnts
getValuations (c : cs) = map(\x -> (c, True) : x) (getValuations cs) ++ map(\x -> (c, False) : x) (getValuations cs)
                        
                          
                                       

{-
  Hint: To apply a function f to every element of a list xs,
   write  map f xs.
  For example, the following adds 1 to the start of every list
   in a list of lists [[2,3], [2,4]]:
   map (\ys -> 1 : ys) [[2,3], [2,4]]  ==  [[1,2,3], [1,2,4]]
-}

{-
   Q2c: evalF:
    Evaluate a formula with a particular valuation,
     returning the resulting boolean value
-}
{-
if expr1 then expr2 else False
-}
evalF :: Valuation -> Formula -> Bool
evalF _    Top                 = True
evalF _    Bot                 = False
evalF valu (Not phi1)          = not(evalF valu phi1)
evalF valu (Atom c)            = helpDecomp c valu
evalF valu (And phi1 phi2)     = (evalF valu phi1) && (evalF valu phi2)
evalF valu (Or phi1 phi2)      = (evalF valu phi1) || (evalF valu phi2)
evalF valu (Implies phi1 phi2) = if (evalF valu phi1) == False then True else evalF valu phi2
evalF valu (Equiv phi1 phi2)   = (evalF valu (Implies phi1 phi2)) && (evalF valu (Implies phi2 phi1))
                                          
-- helper function that identify the value part of the input valuation
helpDecomp :: Variable -> Valuation -> Bool
helpDecomp c [] = error "missing element"
helpDecomp c ((x, b) : xs) = if x == c then b else helpDecomp c xs
-- buildTable:
--  Build a truth table for a given formula.
--  You can use this function to help check your definitions
--  of getAtoms, getValuations and evalF.
buildTable :: Formula -> TruthTable
buildTable psi =
  let valuations = getValuations (getAtoms psi)
  in
    TruthTable (zip valuations
                    (map (\valu -> evalF valu psi) valuations))

{-
Q3: Tiny Theorem Prover
-}

-- a Context is a list of Formulas, representing assumptions
type Context = [Formula]

-- prove ctx phi:
--   return True if, assuming everything in ctx is true,
--    the formula phi is true according to the rules given in a3.pdf.
--   otherwise, return False.
prove :: Context -> Formula -> Bool
prove ctx phi =
  let decomposed = (decompose [] ctx) 
  in (
  if (elem phi decomposed || elem Bot decomposed) == True
  then True
  else prove_right decomposed phi
  )



-- decompose ctx1 ctx2
--  move through ctx2, decomposing And formulas into standalone assumptions
--                     and eliminating Implies formulas where possible      ????what does it mean by eliminate implies????
--                     (see a3.pdf).
-- invariants:
--  - ctx1 is completely decomposed (e.g., no formula in ctx1 is (And _ _))
--  - ctx2 is a "queue" of assumptions that aren't yet completely decomposed
decompose :: Context -> Context -> Context
decompose ctx1 []              = ctx1
decompose ctx1 (middle : ctx2) = 
  case middle of
    And phi1 phi2     -> decompose ctx1 (phi1 : phi2 : ctx2)
    Implies phi1 phi2 -> if prove (ctx1 ++ ctx2) phi1 then decompose ctx1 (phi2 : ctx2) -- call prove on phi1 with ctx = ctx
                            else decompose (ctx1 ++ [Implies phi1 phi2]) ctx2-- if prove （ctx1++ctx2） phi1 then decompose ctx1 (phi2 : ctx2)
                                                                        -- else decompose (ctx1 ++ [Implies phi1 phi2]) ctx2
                                        
    Equiv phi1 phi2   -> [Implies phi1 phi2,  Implies phi2 phi1] -- do similar as decompose:r
    
    middle            -> decompose (ctx1 ++ [middle]) ctx2

-- `case' does pattern matching without declaring a separate function

{-
   prove_right:
    assuming the context is decomposed,
    apply -Right rules (see a3.pdf)
     to break down the goal formula
    ("right" because we are working on the formula on the right-hand side,
     after the assumptions)
-}
prove_right :: Context -> Formula -> Bool

prove_right ctx Top               = True     -- Top-Right

prove_right ctx (And phi1 phi2)   = (prove ctx phi1) && (prove ctx phi2)-- call prove(And phi1 phi2)
prove_right ctx (Or phi1 phi2)    = (prove ctx phi1) || (prove ctx phi2)

prove_right ctx (Implies phi psi) = prove (phi : ctx) psi
  -- try to apply Implies-Right
  -- prove (phi : ctx) psi

prove_right ctx (Equiv phi1 phi2) =
  prove_right ctx (Implies phi1 phi2) && prove_right ctx (Implies phi2 phi1)
  -- try to apply Equiv-Right
  

prove_right ctx p                 =
  -- couldn't apply any of the -Right rules, so give up
  False


test_imp1 = prove [Implies vB vC] (Implies vB vC)
test_imp2 = prove [Implies vB vC] (Implies (And vB vB) vC)
test_imp3 = not (prove [Implies (And vB vD) vC] (Implies vB vC))

test_decompose1 = prove [And (Implies vA vB) (Implies vB vC)] (Implies vA vC)
test_decompose2 = prove [And vA (And vB vC)] (And vA vC)


{- Bonus question (worth no more than 5% of the marks for this assignment

   If you choose to attempt the bonus, write your solutions below.
   See a3.pdf for instructions.
-}
