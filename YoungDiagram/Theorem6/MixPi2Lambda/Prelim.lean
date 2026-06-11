import YoungDiagram.Sigma
import YoungDiagram.Lifting.MixPi2Lambda

open Variety hiding prime prime_def
open Chromosome Pointwise

/-- Elements of `Mix (Pi, 2 • Lambda)` with rank exactly `n`. -/
abbrev nMixPi2Lambda (n : ℕ) := {X : Mix (Pi, 2 • Lambda) // X.1.rank = n}

namespace MixPi2Lambda

/-- The filter of a (tsub) difference is the difference of filters. -/
lemma filter_sub_eq {X Y : Chromosome} {p : Gene → Prop} [DecidablePred p] :
    (X - Y).filter p = X.filter p - Y.filter p := by
  ext g
  simp only [Finsupp.filter_apply, Finsupp.tsub_apply]
  split_ifs <;> simp

/-- `evenPart` commutes with subtraction. -/
lemma evenPart_sub (X Y : Chromosome) :
    (X - Y).evenPart = X.evenPart - Y.evenPart := filter_sub_eq

/-- `oddPart` commutes with subtraction. -/
lemma oddPart_sub (X Y : Chromosome) :
    (X - Y).oddPart = X.oddPart - Y.oddPart := filter_sub_eq

end MixPi2Lambda
