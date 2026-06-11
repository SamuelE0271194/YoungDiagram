import YoungDiagram.Sigma
import YoungDiagram.Lifting.MixPiLambda

open Variety hiding prime prime_def
open Chromosome

/-- Elements of `Mix (Pi, Lambda)` with rank exactly `n`. -/
abbrev nMixPiLambda (n : ℕ) := {X : Mix (Pi, Lambda) // X.1.rank = n}
