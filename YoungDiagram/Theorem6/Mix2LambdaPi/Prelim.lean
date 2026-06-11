import YoungDiagram.Sigma
import YoungDiagram.Lifting.Mix2LambdaPi

open Variety hiding prime prime_def
open Chromosome Pointwise

/-- Elements of `Mix (2 • Lambda, Pi)` with rank exactly `n`. -/
abbrev nMix2LambdaPi (n : ℕ) := {X : Mix (2 • Lambda, Pi) // X.1.rank = n}
