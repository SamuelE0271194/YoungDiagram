import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairDispatcher
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoBranches

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair branch dispatcher

This is the no-pair aggregate glue layer.  It combines the top-level minimal
rank split with the prepared rank-`2` boundary dispatcher, leaving only the
actual mutation leaf solvers for later modules.
-/

/-- Full dispatcher glue for the Label 4 no-pair branch after the prepared
rank split. -/
lemma exists_mutation_le_no_pair_of_prepared_branches (m : ℕ)
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (single_empty :
      ∀ g : Gene,
        0 < X.1.1 g →
        (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) →
        g.type ≠ GeneType.NonPolarized →
        g.rank = 2 →
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
      ∀ g : Gene,
        0 < X.1.1 g →
        (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) →
        g.type ≠ GeneType.NonPolarized →
        g.rank = 2 →
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
    (double_empty :
      ∀ g : Gene,
        0 < X.1.1 g →
        (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) →
        g.type ≠ GeneType.NonPolarized →
        g.rank = 2 →
        X.1.1 (-g) = 0 →
        ∀ restAfterDouble : Chromosome,
          restAfterDouble =
            X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 →
          restAfterDouble = 0 →
          X.1.1 = Finsupp.single g 1 + Finsupp.single g 1 →
          m = 2 →
          signature X.1.1 = ((2 : ℚ), (2 : ℚ)) →
          Chromosome.prime^[3] X.1.1 = 0 →
          ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (double_same_gene :
      ∀ g : Gene,
        0 < X.1.1 g →
        (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) →
        g.type ≠ GeneType.NonPolarized →
        g.rank = 2 →
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
      ∀ g : Gene,
        0 < X.1.1 g →
        (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) →
        g.type ≠ GeneType.NonPolarized →
        g.rank = 2 →
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
            ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (rank_ge_four :
      ∀ (g : Gene) (q : ℕ),
        0 < X.1.1 g →
        (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) →
        g.type ≠ GeneType.NonPolarized →
        g.rank = 2 * q + 4 →
        (∀ h ∈ X.1.1.support, 2 * q + 4 ≤ h.rank) →
        Chromosome.prime^[1] X.1.1 ≠ 0 →
        Chromosome.prime^[1] Y.1.1 ≠ 0 →
        (Chromosome.prime^[1] X.1.1).rank <
          (Chromosome.prime^[1] Y.1.1).rank →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  refine exists_mutation_le_no_pair_of_rank_branches m X Y hXY hcommon h17_1
    hXpol hno_pair ?_ rank_ge_four
  intro g hgX hgmin hg_pol hg_rank
  exact exists_mutation_le_no_pair_rank_two_of_rank_branches X Y hXpol hno_pair
    g hgX hgmin hg_pol hg_rank
    (single_empty g hgX hgmin hg_pol hg_rank)
    (single_rank_ge_four g hgX hgmin hg_pol hg_rank)
    (double_empty g hgX hgmin hg_pol hg_rank)
    (double_same_gene g hgX hgmin hg_pol hg_rank)
    (double_rank_ge_four g hgX hgmin hg_pol hg_rank)

end MixPi2Lambda
