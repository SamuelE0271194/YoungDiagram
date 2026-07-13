import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleRest

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair rank-two branch dispatcher

This module combines the prepared singleton and double branch dispatchers.  The
rank-`2` no-pair boundary now exposes only the actual future leaf solvers:
singleton-empty, singleton rank-`≥4`, double-empty, double same-gene-extra, and
double rank-`≥4`.
-/

/-- Full dispatcher glue for the Label 4 rank-`2` no-pair branch after all
prepared structural splits. -/
lemma exists_mutation_le_no_pair_rank_two_of_rank_branches {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
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
    (double_empty :
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
  obtain ⟨_, hsingle_or_double⟩ :=
    no_pair_rank_two_boundary_data X hno_pair g hgX hg_pol
  rcases hsingle_or_double with hg_one | hg_two
  · exact exists_mutation_le_no_pair_rank_two_single_of_rank_ge_four X Y
      hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_one
      single_empty single_rank_ge_four
  · exact exists_mutation_le_no_pair_rank_two_double_of_rank_split X Y
      hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_two
      double_empty double_same_gene double_rank_ge_four

end MixPi2Lambda
