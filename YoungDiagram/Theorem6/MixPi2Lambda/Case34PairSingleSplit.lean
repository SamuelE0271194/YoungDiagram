import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairDoubleSolver

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Equal-rank pair with multiplicities one and one -/

lemma exists_mutation_le_pair_both_single_of_cross_cases
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1)
    (rank_two_cross : gpos.rank = 2 → gneg.rank = 2 →
      ¬ ((signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2 ∧
        (signature (Chromosome.prime^[3] X.1.1)).2 <
          (signature (Chromosome.prime^[3] Y.1.1)).2) →
      ¬ ((signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[3] X.1.1)).1 <
          (signature (Chromosome.prime^[3] Y.1.1)).1) →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (rank_ge_four_cross : ∀ q, gpos.rank = 2 * q + 4 →
      gneg.rank = 2 * q + 4 →
      ¬ ((signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 ∧
        (signature (Chromosome.prime^[2 * q + 5] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * q + 5] Y.1.1)).2) →
      ¬ ((signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[2 * q + 5] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * q + 5] Y.1.1)).1) →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  rcases equal_rank_pair_rank_split X gpos gneg hrank hgpos (by omega) with
    ⟨hgpos2, hgneg2⟩ | ⟨q, hgposq, hgnegq⟩
  · by_cases hsnd :
        (signature (Chromosome.prime^[1] X.1.1)).2 <
            (signature (Chromosome.prime^[1] Y.1.1)).2 ∧
          (signature (Chromosome.prime^[3] X.1.1)).2 <
            (signature (Chromosome.prime^[3] Y.1.1)).2
    · exact exists_mutation_le_type15_positive_of_snd_lt_of_pair
        X Y hXY hcommon h17_1 gpos gneg hgpos hgneg
          (q := 0) (by omega) hrank (by omega) (by omega) hsnd.1 hsnd.2
    · by_cases hfst :
          (signature (Chromosome.prime^[1] X.1.1)).1 <
              (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
            (signature (Chromosome.prime^[3] X.1.1)).1 <
              (signature (Chromosome.prime^[3] Y.1.1)).1
      · exact exists_mutation_le_type15_negative_of_fst_lt_of_pair
          X Y hXY hcommon h17_1 gpos gneg hgpos hgneg
            (q := 0) (by omega) hrank (by omega) (by omega) hfst.1 hfst.2
      · exact rank_two_cross hgpos2 hgneg2 hsnd hfst
  · by_cases hsnd :
        (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 <
            (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 ∧
          (signature (Chromosome.prime^[2 * q + 5] X.1.1)).2 <
            (signature (Chromosome.prime^[2 * q + 5] Y.1.1)).2
    · exact exists_mutation_le_type15_positive_of_snd_lt_of_pair
        X Y hXY hcommon h17_1 gpos gneg hgpos hgneg
          (q := q + 1) (by omega) hrank (by omega) (by omega)
          (by simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega] using hsnd.1)
          (by simpa [show 2 * (q + 1) + 3 = 2 * q + 5 by omega] using hsnd.2)
    · by_cases hfst :
          (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 ∧
            (signature (Chromosome.prime^[2 * q + 5] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * q + 5] Y.1.1)).1
      · exact exists_mutation_le_type15_negative_of_fst_lt_of_pair
          X Y hXY hcommon h17_1 gpos gneg hgpos hgneg
            (q := q + 1) (by omega) hrank (by omega) (by omega)
            (by simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega] using hfst.1)
            (by simpa [show 2 * (q + 1) + 3 = 2 * q + 5 by omega] using hfst.2)
      · exact rank_ge_four_cross q hgposq hgnegq hsnd hfst

end MixPi2Lambda
