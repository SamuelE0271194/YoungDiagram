import YoungDiagram.Theorem6.Mix2LambdaPi.Prelim

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-! ## Cases 3 & 4 (§15.10): disjoint supports

For `Mix (2 • Lambda, Pi)` the disjoint-pair sub-case (Case 3) cannot be closed
by a single primitive: the only candidate primitive (`type15`) has a target
whose maximal rank exceeds the source's by 2, leaving signature residuals that
no single primitive among `type9`–`type17` absorbs. The disjoint-pair sub-case
therefore folds into the §15.10 multi-primitive analysis (Case 4), so both are
handled together by `exists_mutation_le_case34`. -/

/-- Rank `≥ 2`, disjoint supports: the combined Case 3 + Case 4 (§15.10) analysis
for `Mix (2 • Lambda, Pi)`. -/
lemma exists_mutation_le_case34 (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nMix2LambdaPi k, X.1 < Y.1 →
      ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬ ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

end Mix2LambdaPi
