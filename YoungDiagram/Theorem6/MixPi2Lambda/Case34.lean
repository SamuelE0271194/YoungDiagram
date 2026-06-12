import YoungDiagram.Theorem6.MixPi2Lambda.Prelim

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! ## Cases 3 & 4 (§15.10): disjoint supports

For `Mix (Pi, 2 • Lambda)` the disjoint-pair sub-case (Case 3) cannot be closed
by a single primitive: the only candidate primitive (`type15`) has a target
whose maximal rank exceeds the source's by 2, leaving signature residuals that
no single primitive among `type9`–`type17` absorbs. The disjoint-pair sub-case
therefore folds into the §15.10 multi-primitive analysis (Case 4), so both are
handled together by `exists_mutation_le_case34`. -/

/-- Rank `≥ 2`, disjoint supports: the combined Case 3 + Case 4 (§15.10) analysis
for `Mix (Pi, 2 • Lambda)`. -/
lemma exists_mutation_le_case34 (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nMixPi2Lambda k, X.1 < Y.1 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬ ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

end MixPi2Lambda
