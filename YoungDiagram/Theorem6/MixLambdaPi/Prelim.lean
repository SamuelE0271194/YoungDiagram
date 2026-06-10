import YoungDiagram.Lifting.MixLambdaPi

open Variety hiding prime prime_def
open Chromosome

abbrev nMixLambdaPi (n : ℕ) := {X : Mix (Lambda, Pi) // X.1.rank = n}
