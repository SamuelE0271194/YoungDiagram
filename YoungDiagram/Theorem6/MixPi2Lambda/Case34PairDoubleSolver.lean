import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairDoubleZero

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

lemma exists_mutation_le_pair_positive_double
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : 2 ≤ X.1.1 gpos) (hneg : X.1.1 gneg = 1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  exact exists_mutation_le_pair_positive_double_of_high_zero
    X Y hXY hcommon h17_1 hXpol gpos gneg hrank hgpos hgneg hpos hneg
    (fun q hr hz => exists_mutation_le_pair_positive_double_high_zero
      X Y hXY hcommon h17_1 hXpol gpos gneg hrank hgpos hgneg hpos hneg
        hr hz)

lemma exists_mutation_le_pair_negative_double
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : 2 ≤ X.1.1 gneg) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  exact exists_mutation_le_pair_negative_double_of_high_zero
    X Y hXY hcommon h17_1 hXpol gpos gneg hrank hgpos hgneg hpos hneg
    (fun q hr hz => exists_mutation_le_pair_negative_double_high_zero
      X Y hXY hcommon h17_1 hXpol gpos gneg hrank hgpos hgneg hpos hneg
        hr hz)

end MixPi2Lambda
