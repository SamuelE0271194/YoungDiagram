import YoungDiagram.Theorem6.Mix2LambdaJoint

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/--
Theorem 6 of [Djoković 1982] for `Mix (Pi, 2 • Lambda)` (Label 4).
Given `X < Y` of equal rank in `Mix (Pi, 2 • Lambda)`, there exists a
`MixPi2Lambda.Step` from `X` to some `Z ≤ Y`.

The induction is joint with Label 3 because an odd prime iterate exchanges the
two varieties.  Common genes and positive sigma-agreement levels are fully
handled; the remaining dependency is the primitive-classification core of §17.
-/
theorem exists_mutation_le {n : ℕ} (X Y : nMixPi2Lambda n) (hXY : X < Y) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X Z ∧ Z ≤ Y :=
  (Mix2LambdaJoint.exists_mutation_le_joint n).2 X Y hXY

end MixPi2Lambda
