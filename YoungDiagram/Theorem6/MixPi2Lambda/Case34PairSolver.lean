import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairSingleSolver

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

lemma exists_mutation_le_polarized_remaining_of_pair
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hnodouble : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      2 ≤ X.1.1 gpos ∧ 2 ≤ X.1.1 gneg)
    (hpairs : ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_pair_of_multiplicity_branches X Y hnodouble hpairs
  · intro gpos gneg hrank hgpos hgneg _hXpos _hXneg _hmin hpos hneg
    exact exists_mutation_le_pair_positive_double X Y hXY hcommon h17_1 hXpol
      gpos gneg hrank hgpos hgneg hpos hneg
  · intro gpos gneg hrank hgpos hgneg _hXpos _hXneg _hmin hpos hneg
    exact exists_mutation_le_pair_negative_double X Y hXY hcommon h17_1 hXpol
      gpos gneg hrank hgpos hgneg hpos hneg
  · intro gpos gneg hrank hgpos hgneg hXpos hXneg hmin hpos hneg
    exact exists_mutation_le_pair_both_single X Y hXY hcommon h17_1 hXpol
      gpos gneg hrank hgpos hgneg hXpos hXneg hmin hpos hneg

end MixPi2Lambda
