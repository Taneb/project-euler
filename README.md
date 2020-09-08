The goal of this project is to solve Project Euler problems in a fast,
proven-correct, and readable manner, priotized in that order.

The general structure of a solution will be:

```agda
-- The problem stated as clearly as possible, abstracted to take some notion of
-- input. This will normally be a ℕ representing an upper limit.
problem′ : A → ℕ

-- The problem filled in with the example given in the problem statement. Note
-- that not all problems have appropriate examples.
example : ℕ

-- A proof that the example matches the expected value, as a sort of smoke test
-- of our problem description.
example-correct : example ≡ n

-- The problem with the specific input desired.
problem : ℕ

-- The fast solution, again abstracted over the input.
solution′ : A → ℕ

-- A proof that for all inputs, our solution matches the problem.
solution-correct : problem′ ≗ solution′

-- The solution instantiated at the particular input the problem statement
-- calls for.
solution : ℕ

-- Output the solution.
open import Data.Nat.Show
open import IO
import IO.Primitive as Prim

main : Prim.IO _
main = run (putStrLn (show solution))
```
