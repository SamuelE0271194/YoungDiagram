import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairDoubleClosed

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

lemma exists_mutation_le_pair_positive_double_wrong_component
    {m p : ℕ} (X Y : nMixPi2Lambda (m + 2))
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
    (hpos_rank : gpos.rank = 2 * p + 2)
    (hnfst : ¬ (signature (Chromosome.prime^[2 * p + 3] X.1.1)).1 <
      (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).1)
    (hsnd : (signature (Chromosome.prime^[2 * p + 3] X.1.1)).2 <
      (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).2) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hneg_rank : gneg.rank = 2 * p + 2 := by omega
  have hgap := type16_diagonal_gap_rank
    (ε := GeneType.Positive) (by decide) X Y hXY hcommon h17_1
    gpos gneg hgpos (by simpa using hgneg) hpos_rank hrank hpos (by omega)
  have hle_succ := le_iff_dominates.mp hXY.le (2 * p + 3)
  have hfst_eq :
      (signature (Chromosome.prime^[2 * p + 3] X.1.1)).1 =
        (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).1 :=
    le_antisymm hle_succ.1 (le_of_not_gt hnfst)
  have hYdrop := Mix2LambdaSection17.cond_15_6_Mix_Pi_2Lambda
    Y.1.2 (2 * p + 1)
  rw [if_neg (Nat.not_even_iff_odd.mpr ⟨p, by ring⟩)] at hYdrop
  have hXdrop := snd_drop_le_fst_drop_succ_add_one_even
    X.1.1 (Variety.mem_Pi_iff.mpr hXpol) gneg hneg_rank hgneg hneg
  have hsnd_pred :
      (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 :=
    snd_pred_strict_of_snd_succ_strict hfst_eq
      (fst_add_one_le_of_one_one_add_le hgap)
      (snd_add_one_le_of_one_one_add_le hgap)
      (by simpa [Sigma.sigma] using hYdrop) hXdrop hsnd
  exact exists_mutation_le_type15_positive_of_snd_lt_of_pair
    X Y hXY hcommon h17_1 gpos gneg hgpos hgneg hpos_rank hrank
      (by omega) (by omega) hsnd_pred hsnd

lemma exists_mutation_le_pair_negative_double_wrong_component
    {m p : ℕ} (X Y : nMixPi2Lambda (m + 2))
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
    (hneg_rank : gneg.rank = 2 * p + 2)
    (hnsnd : ¬ (signature (Chromosome.prime^[2 * p + 3] X.1.1)).2 <
      (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).2)
    (hfst : (signature (Chromosome.prime^[2 * p + 3] X.1.1)).1 <
      (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hpos_rank : gpos.rank = 2 * p + 2 := by omega
  have hgap := type16_diagonal_gap_rank
    (ε := GeneType.Negative) (by decide) X Y hXY hcommon h17_1
    gneg gpos hgneg (by simpa using hgpos) hneg_rank hrank.symm hneg (by omega)
  have hle_succ := le_iff_dominates.mp hXY.le (2 * p + 3)
  have hsnd_eq :
      (signature (Chromosome.prime^[2 * p + 3] X.1.1)).2 =
        (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).2 :=
    le_antisymm hle_succ.2 (le_of_not_gt hnsnd)
  have hYdrop := Mix2LambdaSection17.cond_15_7_Mix_Pi_2Lambda
    Y.1.2 (2 * p + 1)
  rw [if_neg (Nat.not_even_iff_odd.mpr ⟨p, by ring⟩)] at hYdrop
  have hXdrop := fst_drop_le_snd_drop_succ_add_one_even
    X.1.1 (Variety.mem_Pi_iff.mpr hXpol) gpos hpos_rank hgpos hpos
  have hfst_pred :
      (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 :=
    fst_pred_strict_of_fst_succ_strict hsnd_eq
      (fst_add_one_le_of_one_one_add_le hgap)
      (snd_add_one_le_of_one_one_add_le hgap)
      (by simpa [Sigma.sigma] using hYdrop) hXdrop hfst
  exact exists_mutation_le_type15_negative_of_fst_lt_of_pair
    X Y hXY hcommon h17_1 gpos gneg hgpos hgneg hneg_rank hrank
      (by omega) (by omega) hfst_pred hfst

end MixPi2Lambda
