import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairSplit

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Equal-rank pair double branches

The `2+1` and `1+2` pair branches first inspect the successor of the common
even rank.  A strict component aligned with the doubled gene is exactly the
diagonal type16 move.  The opposite component and a vanishing successor are
kept as explicit continuation callbacks.
-/

lemma exists_mutation_le_pair_positive_double_of_successor_cases
    {m p : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : 2 ≤ X.1.1 gpos) (hneg : X.1.1 gneg = 1)
    (hpos_rank : gpos.rank = 2 * p + 2)
    (wrong_component :
      ¬ (signature (Chromosome.prime^[2 * p + 3] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).1 →
      (signature (Chromosome.prime^[2 * p + 3] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).2 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (zero_successor :
      Chromosome.prime^[2 * p + 3] Y.1.1 = 0 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hYsucc : Chromosome.prime^[2 * p + 3] Y.1.1 ≠ 0
  · rcases prime_iterate_fst_or_snd_lt X Y hXY h17_1
      (k := 2 * p + 3) (by omega) hYsucc with hfst | ⟨hnfst, hsnd⟩
    · exact exists_mutation_le_type16_positive_of_pair_fst_lt
        X Y hXY hcommon h17_1 gpos gneg hrank hgpos hgneg hpos hneg (by
          intro p' hp'
          have : p' = p := by omega
          subst p'
          exact hfst)
    · exact wrong_component hnfst hsnd
  · exact zero_successor (not_not.mp hYsucc)

lemma exists_mutation_le_pair_negative_double_of_successor_cases
    {m p : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : 2 ≤ X.1.1 gneg)
    (hneg_rank : gneg.rank = 2 * p + 2)
    (wrong_component :
      ¬ (signature (Chromosome.prime^[2 * p + 3] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).2 →
      (signature (Chromosome.prime^[2 * p + 3] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).1 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (zero_successor :
      Chromosome.prime^[2 * p + 3] Y.1.1 = 0 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hYsucc : Chromosome.prime^[2 * p + 3] Y.1.1 ≠ 0
  · rcases prime_iterate_snd_or_fst_lt X Y hXY h17_1
      (k := 2 * p + 3) (by omega) hYsucc with hsnd | ⟨hnsnd, hfst⟩
    · exact exists_mutation_le_type16_negative_of_pair_snd_lt
        X Y hXY hcommon h17_1 gpos gneg hrank hgpos hgneg hpos hneg (by
          intro p' hp'
          have : p' = p := by omega
          subst p'
          exact hsnd)
    · exact wrong_component hnsnd hfst
  · exact zero_successor (not_not.mp hYsucc)

end MixPi2Lambda
