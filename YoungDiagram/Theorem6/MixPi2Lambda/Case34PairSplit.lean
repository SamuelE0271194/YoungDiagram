import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairRankOne

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Equal-rank pair structural split

The minimal equal-rank positive/negative pair has exactly one of the three
multiplicity shapes `2+1`, `1+2`, or `1+1` once the diagonal type13 case has
been excluded.  This module keeps that parity-independent bookkeeping separate
from the Label 4 rank-two boundary proofs.
-/

lemma equal_rank_pair_rank_split
    {N : ℕ} (X : nMixPi2Lambda N) (gpos gneg : Gene)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hXpos : 0 < X.1.1 gpos) :
    (gpos.rank = 2 ∧ gneg.rank = 2) ∨
      ∃ q : ℕ, gpos.rank = 2 * q + 4 ∧ gneg.rank = 2 * q + 4 := by
  have heven :=
    Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
      X.1.2 hXpos (by rw [hgpos]; decide)
  obtain ⟨r, hr⟩ := heven
  have hrpos := gpos.rank_pos
  cases r with
  | zero => omega
  | succ r =>
      by_cases hr0 : r = 0
      · left
        constructor <;> omega
      · right
        let q := r - 1
        refine ⟨q, ?_, ?_⟩ <;> omega

lemma exists_mutation_le_pair_of_multiplicity_branches
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hnodouble : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      2 ≤ X.1.1 gpos ∧ 2 ≤ X.1.1 gneg)
    (hpairs : ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (positive_double :
      ∀ (gpos gneg : Gene),
        gpos.rank = gneg.rank →
        gpos.type = .Positive → gneg.type = .Negative →
        0 < X.1.1 gpos → 0 < X.1.1 gneg →
        (∀ (p n : Gene), p.rank = n.rank →
          p.type = .Positive → n.type = .Negative →
          0 < X.1.1 p → 0 < X.1.1 n → gpos.rank ≤ p.rank) →
        2 ≤ X.1.1 gpos → X.1.1 gneg = 1 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (negative_double :
      ∀ (gpos gneg : Gene),
        gpos.rank = gneg.rank →
        gpos.type = .Positive → gneg.type = .Negative →
        0 < X.1.1 gpos → 0 < X.1.1 gneg →
        (∀ (p n : Gene), p.rank = n.rank →
          p.type = .Positive → n.type = .Negative →
          0 < X.1.1 p → 0 < X.1.1 n → gpos.rank ≤ p.rank) →
        X.1.1 gpos = 1 → 2 ≤ X.1.1 gneg →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (both_single :
      ∀ (gpos gneg : Gene),
        gpos.rank = gneg.rank →
        gpos.type = .Positive → gneg.type = .Negative →
        0 < X.1.1 gpos → 0 < X.1.1 gneg →
        (∀ (p n : Gene), p.rank = n.rank →
          p.type = .Positive → n.type = .Negative →
          0 < X.1.1 p → 0 < X.1.1 n → gpos.rank ≤ p.rank) →
        X.1.1 gpos = 1 → X.1.1 gneg = 1 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXpos, hXneg,
      hmin, hmult⟩ :=
    Mix2LambdaSection17.exists_min_equal_rank_pair_multiplicity_cases
      hnodouble hpairs
  rcases hmult with htwo_one | hone_two | hone_one
  · exact positive_double gpos gneg hrank hgpos hgneg hXpos hXneg hmin
      htwo_one.1 htwo_one.2
  · exact negative_double gpos gneg hrank hgpos hgneg hXpos hXneg hmin
      hone_two.1 hone_two.2
  · exact both_single gpos gneg hrank hgpos hgneg hXpos hXneg hmin
      hone_one.1 hone_one.2

end MixPi2Lambda
