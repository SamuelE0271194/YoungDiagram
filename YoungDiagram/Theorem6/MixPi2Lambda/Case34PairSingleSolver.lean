import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairSingleRemainder

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

lemma exists_mutation_le_pair_high_both_single
    {m q : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1)
    (hpos_rank : gpos.rank = 2 * q + 4)
    (hmin : ∀ (p n : Gene), p.rank = n.rank →
      p.type = GeneType.Positive → n.type = GeneType.Negative →
      0 < X.1.1 p → 0 < X.1.1 n → gpos.rank ≤ p.rank) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hYpred : Chromosome.prime^[2 * q + 3] Y.1.1 ≠ 0 := by
    intro hz
    have hdom := (le_iff_dominates.mp hXY.le (2 * q + 3)).1
    have hYsig :
        signature (Chromosome.prime^[2 * q + 3] Y.1.1) = 0 := by
      rw [hz, map_zero]
    rw [hYsig] at hdom
    have hXfst := one_le_signature_prime_pred_fst_of_positive
      (X := X.1.1) (gpos := gpos) hgpos (by omega)
    have hXfst' :
        1 ≤ (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 := by
      simpa [hpos_rank] using hXfst
    simp only [Prod.fst_zero] at hdom
    linarith
  by_cases hYsucc : Chromosome.prime^[2 * q + 5] Y.1.1 ≠ 0
  · have hYpred' : Chromosome.prime^[2 * (q + 1) + 1] Y.1.1 ≠ 0 := by
      rw [show 2 * (q + 1) + 1 = 2 * q + 3 by omega]
      exact hYpred
    have hYsucc' : Chromosome.prime^[2 * (q + 1) + 3] Y.1.1 ≠ 0 := by
      rw [show 2 * (q + 1) + 3 = 2 * q + 5 by omega]
      exact hYsucc
    exact exists_mutation_le_pair_both_single_endpoints_nonzero
      X Y hXY hcommon h17_1 hXpol gpos gneg hrank hgpos hgneg hpos hneg
        (p := q + 1) (by omega) hYpred' hYsucc'
  · exact exists_mutation_le_pair_high_both_single_zero_successor
      X Y hXY hcommon h17_1 hXpol gpos gneg hrank hgpos hgneg hpos hneg
        hpos_rank hmin (not_not.mp hYsucc)

lemma exists_mutation_le_pair_both_single
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
    (hXpos : 0 < X.1.1 gpos) (_hXneg : 0 < X.1.1 gneg)
    (hmin : ∀ (p n : Gene), p.rank = n.rank →
      p.type = GeneType.Positive → n.type = GeneType.Negative →
      0 < X.1.1 p → 0 < X.1.1 n → gpos.rank ≤ p.rank)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  rcases equal_rank_pair_rank_split X gpos gneg hrank hgpos hXpos with
    ⟨hpos2, hneg2⟩ | ⟨q, hposq, hnegq⟩
  · exact exists_mutation_le_pair_rank_two_both_single X Y hXY hcommon h17_1
      hXpol gpos gneg hrank hgpos hgneg hpos2 hneg2 hpos hneg
  · exact exists_mutation_le_pair_high_both_single X Y hXY hcommon h17_1
      hXpol gpos gneg hrank hgpos hgneg hpos hneg hposq hmin

end MixPi2Lambda
