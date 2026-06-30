import YoungDiagram.Theorem6.Mix2LambdaJoint

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/--
Theorem 6 of [Djoković 1982] for `Mix (2 • Lambda, Pi)` (Label 3).
Given `X < Y` of equal rank in `Mix (2 • Lambda, Pi)`, there exists a
`Mix2LambdaPi.Step` from `X` to some `Z ≤ Y`.

The induction is joint with Label 4 because an odd prime iterate exchanges the
two varieties.  Common genes and positive sigma-agreement levels are fully
handled; the remaining dependency is the primitive-classification core of §17.
-/
theorem exists_mutation_le {n : ℕ} (X Y : nMix2LambdaPi n) (hXY : X < Y) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X Z ∧ Z ≤ Y :=
  (Mix2LambdaJoint.exists_mutation_le_joint n).1 X Y hXY

end Mix2LambdaPi
