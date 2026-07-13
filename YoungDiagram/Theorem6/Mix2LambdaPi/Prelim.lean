import YoungDiagram.Sigma
import YoungDiagram.Lifting.Mix2LambdaPi

open Variety hiding prime prime_def
open Chromosome Pointwise

/-- Elements of `Mix (2 • Lambda, Pi)` with rank exactly `n`. -/
abbrev nMix2LambdaPi (n : ℕ) := {X : Mix (2 • Lambda, Pi) // X.1.rank = n}

namespace Mix2LambdaPi

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

end Mix2LambdaPi
