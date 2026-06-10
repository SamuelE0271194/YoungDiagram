import YoungDiagram.Theorem6.MixLambdaPi.Prelim

open Variety hiding prime prime_def
open Chromosome Sigma

namespace MixLambdaPi

theorem exists_mutation_le {n : ℕ} : ∀ (X Y : nMixLambdaPi n), X < Y →
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X Z ∧ Z ≤ Y := sorry

end MixLambdaPi
