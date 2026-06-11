import YoungDiagram.Sigma
import YoungDiagram.Lifting.MixPi2Lambda

open Variety hiding prime prime_def
open Chromosome Pointwise

/-- Elements of `Mix (Pi, 2 • Lambda)` with rank exactly `n`. -/
abbrev nMixPi2Lambda (n : ℕ) := {X : Mix (Pi, 2 • Lambda) // X.1.rank = n}
