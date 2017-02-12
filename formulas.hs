--Trabajo con formulas y notacion polaca
module Logic (module Logic) where

import Data.List
import Numeric
import Data.Char
import Data.Maybe

data Formula = 
      Atomic Char --Atomic variable
    | N Formula --Not
    | K Formula Formula --And
    | A Formula Formula --Or
    | C Formula Formula --Implication
    | E Formula Formula --Double implication

type Combination = [(Char, Int)]
type CombinationSet = [Combination]

type TruthTableResult = [(Combination, Int)]

instance Show Formula where
    showsPrec _ (Atomic label) = showChar label

    --Polish notation
    -- showsPrec _ (N a)   = showChar 'N' . shows a
    -- showsPrec _ (K a b) = showChar 'K' . shows a . shows b
    -- showsPrec _ (A a b) = showChar 'A' . shows a . shows b
    -- showsPrec _ (C a b) = showChar 'C' . shows a . shows b
    -- showsPrec _ (E a b) = showChar 'E' . shows a . shows b

    --Standard notation
    showsPrec _ (N a)   = showChar '(' . showChar '-' . shows a . showChar ')'
    showsPrec _ (K a b) = showChar '(' . shows a . showChar '^' . shows b . showChar ')'
    showsPrec _ (A a b) = showChar '(' . shows a . showChar 'v' . shows b . showChar ')'
    showsPrec _ (C a b) = showChar '(' . shows a . showString "->" . shows b . showChar ')'
    showsPrec _ (E a b) = showChar '(' . shows a . showString "<->" . shows b . showChar ')'

getAtomicVariables :: Formula -> [Char]
getAtomicVariables (Atomic label) = [label]
getAtomicVariables (N a)   = (getAtomicVariables a)
getAtomicVariables (K a b) = (getAtomicVariables a) `union` (getAtomicVariables b)
getAtomicVariables (A a b) = (getAtomicVariables a) `union` (getAtomicVariables b)
getAtomicVariables (C a b) = (getAtomicVariables a) `union` (getAtomicVariables b)
getAtomicVariables (E a b) = (getAtomicVariables a) `union` (getAtomicVariables b)

generateCombinationSet :: [Char] -> CombinationSet
generateCombinationSet [] = [[]]
generateCombinationSet atomicVariables = [zip atomicVariables (map digitToInt (normalizeBinary (showIntAtBase 2 intToDigit currentCounter "") (length atomicVariables))) | currentCounter <- [0..2^(length atomicVariables)-1]]

normalizeBinary :: String -> Int -> String
normalizeBinary _ 0 = []
normalizeBinary input requiredLength = mergeLists (replicate (requiredLength-(length input)) '0') input

mergeLists :: [a] -> [a] -> [a]
mergeLists [] ys = ys
mergeLists (x:xs) ys = x:mergeLists ys xs

testFormulaWith :: Formula -> Combination -> Int
testFormulaWith (Atomic a) combination = fromJust (lookup a combination)
testFormulaWith (N a)      combination = ((testFormulaWith a combination) + 1) `mod` 2
testFormulaWith (K a b)    combination = (testFormulaWith a combination) * (testFormulaWith b combination)
testFormulaWith (A a b)    combination = ((testFormulaWith a combination) * (testFormulaWith b combination) + (testFormulaWith a combination) + (testFormulaWith b combination)) `mod` 2
testFormulaWith (C a b)    combination = ((testFormulaWith a combination) * (testFormulaWith b combination) + (testFormulaWith a combination) + 1) `mod` 2
testFormulaWith (E a b)    combination = ((testFormulaWith a combination) + (testFormulaWith b combination) + 1) `mod` 2
    -- where
    --     aTested = (testFormulaWith a combination)
    --     bTested = (testFormulaWith b combination)

truthTableOfAux :: Formula -> CombinationSet -> [Int]
truthTableOfAux _ [] = []
truthTableOfAux formula (currentCombination:remainingCombinations) = (testFormulaWith formula currentCombination):(truthTableOfAux formula remainingCombinations)

truthTableOf :: Formula -> TruthTableResult
truthTableOf formula = zip combinationSet combinationSetResults
    where
        combinationSet = generateCombinationSet (getAtomicVariables formula)
        combinationSetResults = truthTableOfAux formula combinationSet

or' :: [Char] -> Combination -> Int
or' [] combination = 0
or' (a:as) combination = ((fromJust (lookup a combination)) * (or' as combination) + (fromJust (lookup a combination)) + (or' as combination)) `mod` 2

combinationToDisjunctive :: Combination -> Formula
combinationToDisjunctive (x@(char, value):xs:xss)
    | (value == 0) = A(Atomic char)(combinationToDisjunctive (xs:xss))
    | (value == 1) = A(N(Atomic char))(combinationToDisjunctive (xs:xss))
combinationToDisjunctive (x@(char, value):xs)
    | (value == 0) = Atomic char
    | (value == 1) = N(Atomic char)

generateConjunctiveTautology :: [Char] -> Formula
generateConjunctiveTautology (x:xs:xss) = K(A(Atomic x)(N(Atomic x)))(generateConjunctiveTautology (xs:xss))
generateConjunctiveTautology (x:xs) = A(Atomic x)(N(Atomic x))

conjunctiveNormalFormOfAux :: TruthTableResult -> Formula -> Formula
conjunctiveNormalFormOfAux [] formula = generateConjunctiveTautology (getAtomicVariables formula)
conjunctiveNormalFormOfAux ((firstAtomics,_):xs:xss) formula = K(combinationToDisjunctive firstAtomics)(conjunctiveNormalFormOfAux (xs:xss) formula)
conjunctiveNormalFormOfAux ((firstAtomics,_):xs) _ = combinationToDisjunctive firstAtomics

conjunctiveNormalFormOf :: Formula -> Formula
conjunctiveNormalFormOf formula = conjunctiveNormalFormOfAux clausesToInclude formula where
    truthTable = truthTableOf formula
    clausesToInclude = filter (\(_, x) -> x == 0) truthTable

combinationToConjunctive :: Combination -> Formula
combinationToConjunctive (x@(char, value):xs:xss)
    | (value == 1) = K(Atomic char)(combinationToConjunctive (xs:xss))
    | (value == 0) = K(N(Atomic char))(combinationToConjunctive (xs:xss))
combinationToConjunctive (x@(char, value):xs)
    | (value == 1) = Atomic char
    | (value == 0) = N(Atomic char)

generateDisjunctiveContradiction :: [Char] -> Formula
generateDisjunctiveContradiction (x:xs:xss) = A(K(Atomic x)(N(Atomic x)))(generateDisjunctiveContradiction (xs:xss))
generateDisjunctiveContradiction (x:xs) = K(Atomic x)(N(Atomic x))

disjunctiveNormalFormOfAux :: TruthTableResult -> Formula -> Formula
disjunctiveNormalFormOfAux [] formula = generateDisjunctiveContradiction (getAtomicVariables formula)
disjunctiveNormalFormOfAux ((firstAtomics,_):xs:xss) formula = A(combinationToConjunctive firstAtomics)(disjunctiveNormalFormOfAux (xs:xss) formula)
disjunctiveNormalFormOfAux ((firstAtomics,_):xs) _ = combinationToConjunctive firstAtomics

disjunctiveNormalFormOf :: Formula -> Formula
disjunctiveNormalFormOf formula = disjunctiveNormalFormOfAux clausesToInclude formula where
    truthTable = truthTableOf formula
    clausesToInclude = filter (\(_, x) -> x == 1) truthTable

