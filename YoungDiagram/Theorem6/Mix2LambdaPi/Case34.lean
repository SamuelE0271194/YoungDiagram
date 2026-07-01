import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Remaining

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-! ## Section 17 core after the induction and lifting reductions

The joint Label 3/4 induction first removes common genes and handles every
positive level at which the two sigma columns agree.  Consequently this file
starts precisely from condition (17.1) of Djoković: whenever `prime^[k] Y` is
nonzero at a positive level, the two sigma columns are unequal.  The remaining
proof is the type9--type17 classification from §17. -/

/-- The primitive-classification core of §17 for `Mix (2 • Lambda, Pi)`.

The hypotheses are disjointness and the negation of a positive sigma-agreement
level.  The latter is the Lean form of the reduction leading to (17.1). -/
lemma exists_mutation_le_reduced (m : ℕ)
    (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬ ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬ ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank := by
    intro k hkpos hYkne
    apply prime_iterate_rank_lt_of_sigma_ne hXY.le
    intro hsig
    exact hsigeq ⟨k, hkpos, hYkne, hsig⟩
  push Not at hcommon
  by_cases hNP : ∃ g : Gene, 0 < X.1.1 g ∧ g.type = .NonPolarized
  · obtain ⟨g, hXg, hgNP⟩ := hNP
    exact exists_mutation_le_of_nonpolarized X Y hXY hcommon h17_1 g hXg hgNP
  · push Not at hNP
    -- From here on `X` is polarized; this is the remaining type10--type17
    -- classification in §17.
    have hXpol : X.1.1.IsPolarized := by
      rw [IsPolarized_def']
      intro g hg
      exact hNP g (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg))
    by_cases hdouble : ∃ (gpos gneg : Gene),
        gpos.rank = gneg.rank ∧
        gpos.type = .Positive ∧ gneg.type = .Negative ∧
        2 ≤ X.1.1 gpos ∧ 2 ≤ X.1.1 gneg
    · obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXpos2, hXneg2⟩ := hdouble
      exact exists_mutation_le_of_double_pair X Y hXY hcommon h17_1
        gpos gneg hrank hgpos hgneg hXpos2 hXneg2
    · exact exists_mutation_le_polarized_remaining m X Y hXY hcommon h17_1
        hXpol hdouble

end Mix2LambdaPi
