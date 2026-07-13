import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairBoundary

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Pair double branches after closing the rank-two zero boundary -/

lemma exists_mutation_le_pair_positive_double_of_rank_cases
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
    (hpos : 2 ≤ X.1.1 gpos) (hneg : X.1.1 gneg = 1)
    (wrong_component : ∀ p, gpos.rank = 2 * p + 2 →
      ¬ (signature (Chromosome.prime^[2 * p + 3] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).1 →
      (signature (Chromosome.prime^[2 * p + 3] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).2 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (high_zero : ∀ q, gpos.rank = 2 * q + 4 →
      Chromosome.prime^[2 * q + 5] Y.1.1 = 0 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  rcases equal_rank_pair_rank_split X gpos gneg hrank hgpos (by omega) with
    ⟨hgpos2, hgneg2⟩ | ⟨q, hgposq, hgnegq⟩
  · exact exists_mutation_le_pair_positive_double_of_successor_cases
      X Y hXY hcommon h17_1 gpos gneg hrank hgpos hgneg hpos hneg
      (p := 0) (by omega) (wrong_component 0 (by omega)) (fun hY3 =>
        exists_mutation_le_pair_rank_two_positive_double_zero_successor
          X Y hXY hcommon h17_1 hXpol gpos gneg hgpos hgneg hgpos2 hgneg2
            hpos hneg hY3)
  · exact exists_mutation_le_pair_positive_double_of_successor_cases
      X Y hXY hcommon h17_1 gpos gneg hrank hgpos hgneg hpos hneg
      (p := q + 1) (by omega) (wrong_component (q + 1) (by omega)) (fun hz =>
        high_zero q hgposq (by
          simpa [show 2 * (q + 1) + 3 = 2 * q + 5 by omega] using hz))

lemma exists_mutation_le_pair_negative_double_of_rank_cases
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
    (hpos : X.1.1 gpos = 1) (hneg : 2 ≤ X.1.1 gneg)
    (wrong_component : ∀ p, gneg.rank = 2 * p + 2 →
      ¬ (signature (Chromosome.prime^[2 * p + 3] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).2 →
      (signature (Chromosome.prime^[2 * p + 3] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).1 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (high_zero : ∀ q, gneg.rank = 2 * q + 4 →
      Chromosome.prime^[2 * q + 5] Y.1.1 = 0 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  rcases equal_rank_pair_rank_split X gpos gneg hrank hgpos (by omega) with
    ⟨hgpos2, hgneg2⟩ | ⟨q, hgposq, hgnegq⟩
  · exact exists_mutation_le_pair_negative_double_of_successor_cases
      X Y hXY hcommon h17_1 gpos gneg hrank hgpos hgneg hpos hneg
      (p := 0) (by omega) (wrong_component 0 (by omega)) (fun hY3 =>
        exists_mutation_le_pair_rank_two_negative_double_zero_successor
          X Y hXY hcommon h17_1 hXpol gpos gneg hgpos hgneg hgpos2 hgneg2
            hpos hneg hY3)
  · exact exists_mutation_le_pair_negative_double_of_successor_cases
      X Y hXY hcommon h17_1 gpos gneg hrank hgpos hgneg hpos hneg
      (p := q + 1) (by omega) (wrong_component (q + 1) (by omega)) (fun hz =>
        high_zero q hgnegq (by
          simpa [show 2 * (q + 1) + 3 = 2 * q + 5 by omega] using hz))

end MixPi2Lambda
