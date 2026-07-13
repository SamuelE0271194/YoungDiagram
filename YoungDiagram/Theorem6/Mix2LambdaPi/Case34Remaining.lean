import YoungDiagram.Theorem6.Mix2LambdaPi.Case34PairBranch

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

set_option maxHeartbeats 800000 in
-- The §17 polarized remainder now carries the type11 active-window proof inline;
-- elaborating its nested sigma decompositions needs a larger local budget.
/-- The remaining polarized part of §17 after the diagonal type13 branch.
This consists of the `2+1`, `1+1`, and no-equal-rank-pair cases, using
type10--type12 and type14--type17. -/
lemma exists_mutation_le_polarized_remaining (m : ℕ)
    (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hnodouble : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      2 ≤ X.1.1 gpos ∧ 2 ≤ X.1.1 gneg) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hpairs : ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg
  · exact exists_mutation_le_polarized_remaining_of_pair
      X Y hXY hcommon h17_1 hXpol hnodouble hpairs
  · -- No equal-rank positive/negative pair remains; this is the final
    -- minimum-rank part of §17, using type14/type15 and the boundary cases.
    exact exists_mutation_le_no_pair m X Y hXY hcommon h17_1 hXpol hpairs

end Mix2LambdaPi
