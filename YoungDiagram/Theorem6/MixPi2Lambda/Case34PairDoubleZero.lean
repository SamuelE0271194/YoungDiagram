import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairDoubleAlmost

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

lemma exists_mutation_le_pair_positive_double_high_zero
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
    (hpos : 2 ≤ X.1.1 gpos) (hneg : X.1.1 gneg = 1)
    (hpos_rank : gpos.rank = 2 * q + 4)
    (hYsucc : Chromosome.prime^[2 * q + 5] Y.1.1 = 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hneg_rank : gneg.rank = 2 * (q + 1) + 2 := by omega
  have hgap := type16_diagonal_gap_rank
    (p := q + 1) (ε := GeneType.Positive) (by decide) X Y hXY hcommon h17_1
    gpos gneg hgpos (by simpa using hgneg) (by omega) hrank hpos (by omega)
  have hgap' : ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * q + 4] X.1.1) ≤
      signature (Chromosome.prime^[2 * q + 4] Y.1.1) := by
    simpa [show 2 * (q + 1) + 2 = 2 * q + 4 by omega] using hgap
  have hXsucc := signature_prime_iterate_eq_zero_of_le_zero hXY.le hYsucc
  have hYsucc_sig : signature (Chromosome.prime^[2 * q + 5] Y.1.1) = 0 := by
    rw [hYsucc, map_zero]
  have hfst_succ_eq :
      (signature (Chromosome.prime^[2 * q + 5] X.1.1)).1 =
        (signature (Chromosome.prime^[2 * q + 5] Y.1.1)).1 := by
    rw [hXsucc, hYsucc_sig]
  have hYdrop := Mix2LambdaSection17.cond_15_6_Mix_Pi_2Lambda
    Y.1.2 (2 * q + 3)
  rw [if_neg (Nat.not_even_iff_odd.mpr ⟨q + 1, by ring⟩)] at hYdrop
  have hXdrop := snd_drop_le_fst_drop_succ_add_one_even
    X.1.1 (Variety.mem_Pi_iff.mpr hXpol) gneg hneg_rank hgneg hneg
  have hsnd_pred :
      (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 :=
    snd_pred_strict_of_succ_fst_eq hfst_succ_eq
      (fst_add_one_le_of_one_one_add_le hgap')
      (snd_add_one_le_of_one_one_add_le hgap')
      (by simpa [Sigma.sigma] using hYdrop)
      (by simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega,
          show 2 * (q + 1) + 2 = 2 * q + 4 by omega,
          show 2 * (q + 1) + 3 = 2 * q + 5 by omega] using hXdrop)
  have hgap17 : ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * (q + 1) + 2] X.1.1) ≤
      signature (Chromosome.prime^[2 * (q + 1) + 2] Y.1.1) := by
    rw [show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
    exact hgap'
  exact exists_mutation_le_type17_diagonal_positive (q := q + 1)
    X Y hXY gpos gneg
    hgpos hgneg (by omega) hrank hpos (by omega)
      (type17_pred_gap_positive X Y hXY hsnd_pred) hgap17

lemma exists_mutation_le_pair_negative_double_high_zero
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
    (hpos : X.1.1 gpos = 1) (hneg : 2 ≤ X.1.1 gneg)
    (hneg_rank : gneg.rank = 2 * q + 4)
    (hYsucc : Chromosome.prime^[2 * q + 5] Y.1.1 = 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hpos_rank : gpos.rank = 2 * (q + 1) + 2 := by omega
  have hgap := type16_diagonal_gap_rank
    (p := q + 1) (ε := GeneType.Negative) (by decide) X Y hXY hcommon h17_1
    gneg gpos hgneg (by simpa using hgpos) (by omega) hrank.symm hneg (by omega)
  have hgap' : ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * q + 4] X.1.1) ≤
      signature (Chromosome.prime^[2 * q + 4] Y.1.1) := by
    simpa [show 2 * (q + 1) + 2 = 2 * q + 4 by omega] using hgap
  have hXsucc := signature_prime_iterate_eq_zero_of_le_zero hXY.le hYsucc
  have hYsucc_sig : signature (Chromosome.prime^[2 * q + 5] Y.1.1) = 0 := by
    rw [hYsucc, map_zero]
  have hsnd_succ_eq :
      (signature (Chromosome.prime^[2 * q + 5] X.1.1)).2 =
        (signature (Chromosome.prime^[2 * q + 5] Y.1.1)).2 := by
    rw [hXsucc, hYsucc_sig]
  have hYdrop := Mix2LambdaSection17.cond_15_7_Mix_Pi_2Lambda
    Y.1.2 (2 * q + 3)
  rw [if_neg (Nat.not_even_iff_odd.mpr ⟨q + 1, by ring⟩)] at hYdrop
  have hXdrop := fst_drop_le_snd_drop_succ_add_one_even
    X.1.1 (Variety.mem_Pi_iff.mpr hXpol) gpos hpos_rank hgpos hpos
  have hfst_pred :
      (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 :=
    fst_pred_strict_of_succ_snd_eq hsnd_succ_eq
      (fst_add_one_le_of_one_one_add_le hgap')
      (snd_add_one_le_of_one_one_add_le hgap')
      (by simpa [Sigma.sigma] using hYdrop)
      (by simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega,
          show 2 * (q + 1) + 2 = 2 * q + 4 by omega,
          show 2 * (q + 1) + 3 = 2 * q + 5 by omega] using hXdrop)
  have hgap17 : ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * (q + 1) + 2] X.1.1) ≤
      signature (Chromosome.prime^[2 * (q + 1) + 2] Y.1.1) := by
    rw [show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
    exact hgap'
  exact exists_mutation_le_type17_diagonal_negative (q := q + 1)
    X Y hXY gpos gneg
    hgpos hgneg (by omega) hrank (by omega) hneg
      (type17_pred_gap_negative X Y hXY hfst_pred) hgap17

end MixPi2Lambda
