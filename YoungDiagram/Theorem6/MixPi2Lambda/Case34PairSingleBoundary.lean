import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairSingleNonzero

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

lemma pair_rank_two_both_single_zero_successor_false
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hgpos2 : gpos.rank = 2) (hgneg2 : gneg.rank = 2)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1)
    (hY3 : Chromosome.prime^[3] Y.1.1 = 0) : False := by
  obtain ⟨hXshape, hY2L, _, _, hsigX⟩ :=
    pair_rank_two_zero_successor_shape X Y hXY hcommon hXpol gpos gneg
      hgpos hgneg hgpos2 hgneg2 (by omega) (by omega) hY3
  have hXrank : X.1.1.rank = 4 := by
    have hsum := @signature_sum_eq_rank X.1.1
    rw [hsigX, hpos, hneg] at hsum
    norm_num at hsum ⊢
    exact_mod_cast hsum.symm
  have hYrank : Y.1.1.rank = 4 := by
    rw [Y.2, ← X.2, hXrank]
  have hX1sig : signature (Chromosome.prime^[1] X.1.1) =
      ((1 : ℚ), (1 : ℚ)) := by
    conv_lhs => rw [hXshape, hpos, hneg, iterate_map_add, map_add]
    simp only [Function.iterate_one, prime_single, one_nsmul]
    rw [hgpos2, hgneg2, hgpos, hgneg]
    simp [signature_ofRank_one_positive, signature_ofRank_one_negative]
  have hY1 : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
    intro hz
    have hdom := (le_iff_dominates.mp hXY.le 1).1
    rw [hX1sig, hz, map_zero] at hdom
    norm_num at hdom
  have hr1 := h17_1 1 (by omega) hY1
  have hX1rank : (Chromosome.prime^[1] X.1.1).rank = 2 := by
    have hsum := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
    rw [hX1sig] at hsum
    norm_num at hsum ⊢
    exact_mod_cast hsum.symm
  have hY1lt : (Chromosome.prime^[1] Y.1.1).rank < 4 := by
    change Y.1.1.prime.rank < 4
    have hlt := prime_rank_lt (X := Y.1.1) (by
      intro hz
      rw [hz, map_zero] at hYrank
      omega)
    rwa [hYrank] at hlt
  obtain ⟨W0, hW0, hW0eq⟩ :=
    (AddSubmonoid.mem_smul_pointwise_iff_exists Y.1.1 2 Lambda).mp hY2L
  change 2 • W0 = Y.1.1 at hW0eq
  have hY1double : Chromosome.prime Y.1.1 = 2 • Chromosome.prime W0 := by
    rw [← hW0eq, map_nsmul]
  have hY1even : Even (Chromosome.prime Y.1.1).rank := by
    rw [hY1double, map_nsmul]
    refine ⟨(Chromosome.prime W0).rank, ?_⟩
    simp only [two_nsmul]
  rw [hX1rank] at hr1
  change Even (Chromosome.prime Y.1.1).rank at hY1even
  change 2 < (Chromosome.prime Y.1.1).rank at hr1
  change (Chromosome.prime Y.1.1).rank < 4 at hY1lt
  obtain ⟨r, hr⟩ := hY1even
  omega

lemma exists_mutation_le_pair_rank_two_both_single
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
    (hgpos2 : gpos.rank = 2) (hgneg2 : gneg.rank = 2)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hY1 : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
    intro hz
    have hdom := (le_iff_dominates.mp hXY.le 1).1
    rw [hz, map_zero] at hdom
    have hXfst := one_le_signature_prime_pred_fst_of_positive
      (X := X.1.1) (gpos := gpos) hgpos (by omega)
    have hXfst' : 1 ≤ (signature (Chromosome.prime^[1] X.1.1)).1 := by
      simpa [hgpos2] using hXfst
    norm_num at hdom
    have hXfst'' : 1 ≤ (signature (Chromosome.prime X.1.1)).1 := by
      simpa [Function.iterate_one] using hXfst'
    linarith
  by_cases hY3 : Chromosome.prime^[3] Y.1.1 ≠ 0
  · exact exists_mutation_le_pair_both_single_endpoints_nonzero
      X Y hXY hcommon h17_1 hXpol gpos gneg hrank hgpos hgneg hpos hneg
        (p := 0) (by omega) hY1 hY3
  · exact False.elim (pair_rank_two_both_single_zero_successor_false
      X Y hXY hcommon h17_1 hXpol gpos gneg hgpos hgneg hgpos2 hgneg2
        hpos hneg (not_not.mp hY3))

end MixPi2Lambda
