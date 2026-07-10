import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDoubleEmpty

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 rank-two no-pair dispatcher after closing double-empty

This integration layer preserves the prepared dispatcher API while supplying
the now-complete double-empty §17 Case 2 leaf internally.  Four genuine
rank-two leaves remain: singleton-empty, singleton rank-`≥4`, double
same-gene-extra, and double rank-`≥4`.
-/

/-- Rank-two no-pair dispatcher with the double-empty leaf discharged. -/
lemma exists_mutation_le_no_pair_rank_two_after_double_empty {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene)
    (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (single_empty :
      X.1.1 (-g) = 0 →
      ∀ restAfterG : Chromosome,
        restAfterG = X.1.1 - Finsupp.single g 1 →
        X.1.1 g = 1 →
        restAfterG = 0 →
        X.1.1 = Finsupp.single g 1 →
        m = 0 →
        signature X.1.1 = ((1 : ℚ), (1 : ℚ)) →
        Chromosome.prime^[3] X.1.1 = 0 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (single_rank_ge_four :
      X.1.1 (-g) = 0 →
      ∀ restAfterG : Chromosome,
        restAfterG = X.1.1 - Finsupp.single g 1 →
        X.1.1 g = 1 →
        restAfterG ≠ 0 →
        ∀ g₂ : Gene,
          0 < restAfterG g₂ →
          (∀ h : Gene, 0 < restAfterG h → g₂.rank ≤ h.rank) →
          0 < X.1.1 g₂ →
          2 ≤ g₂.rank →
          g₂.type ≠ GeneType.NonPolarized →
          g₂ ≠ -g →
          ∀ q₂ : ℕ, g₂.rank = 2 * q₂ + 4 →
          ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (double_same_gene :
      X.1.1 (-g) = 0 →
      ∀ restAfterDouble : Chromosome,
        restAfterDouble =
          X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 →
        restAfterDouble ≠ 0 →
        ∀ g₂ : Gene,
          0 < restAfterDouble g₂ →
          (∀ h : Gene, 0 < restAfterDouble h → g₂.rank ≤ h.rank) →
          0 < X.1.1 g₂ →
          2 ≤ g₂.rank →
          g₂.type ≠ GeneType.NonPolarized →
          g₂ ≠ -g →
          g₂ = g →
          ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (double_rank_ge_four :
      X.1.1 (-g) = 0 →
      ∀ restAfterDouble : Chromosome,
        restAfterDouble =
          X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 →
        restAfterDouble ≠ 0 →
        ∀ g₂ : Gene,
          0 < restAfterDouble g₂ →
          (∀ h : Gene, 0 < restAfterDouble h → g₂.rank ≤ h.rank) →
          0 < X.1.1 g₂ →
          2 ≤ g₂.rank →
          g₂.type ≠ GeneType.NonPolarized →
          g₂ ≠ -g →
          ∀ q₂ : ℕ, g₂.rank = 2 * q₂ + 4 →
          ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  refine exists_mutation_le_no_pair_rank_two_of_rank_branches X Y hXpol
    hno_pair g hgX hgmin hg_pol hg_rank single_empty single_rank_ge_four ?_
    double_same_gene double_rank_ge_four
  intro hneg_zero restAfterDouble hrestAfterDouble hrest_zero hXeq hm2
    hsigX hX3
  exact exists_mutation_le_no_pair_rank_two_double_empty X Y hXY h17_1
    g hgX hgmin hg_pol hg_rank hneg_zero restAfterDouble hrestAfterDouble
    hrest_zero hXeq hm2 hsigX hX3

end MixPi2Lambda
