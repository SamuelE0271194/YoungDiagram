import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleOpposite

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Rank-two double fallback

The singleton Case 2 window machinery only uses the exact equation `X g = 1`
at its final mutation wrappers.  The underlying type15/type17 constructors need
only one available copy of the low rank-two gene.  These wrappers expose that
weaker hypothesis and therefore also cover the double branch.
-/

private lemma exists_mutation_le_type17_rank_two_of_directed_gaps
    {m q : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g gopp : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hopp_rank : gopp.rank = 2 * q + 4)
    (hg_copy : 1 ≤ X.1.1 g) (hopp_two : 2 ≤ X.1.1 gopp)
    (hne : g ≠ gopp) (hopp_type : gopp.type = -g.type)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hodd :
      (g.type = GeneType.Positive →
        ∀ j, 2 ≤ j → j ≤ 2 * q + 4 → ¬ Even j →
          ((2 : ℚ), (0 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1)) ∧
      (g.type = GeneType.Negative →
        ∀ j, 2 ≤ j → j ≤ 2 * q + 4 → ¬ Even j →
          ((0 : ℚ), (2 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1)))
    (hYtop : Chromosome.prime^[2 * q + 4] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_type17_rank_two_of_genes_of_gaps hg_pol
    X Y hXY g gopp rfl hopp_type hg_rank
      (show gopp.rank = 2 * (q + 1) + 2 by omega)
      hg_copy hopp_two hne
  · simpa using no_pair_rank_two_single_low_fallback_type15_pred_gap
      X Y hXY g hlow
  · intro j hjlo hjhi heven
    by_cases hjtop : j = 2 * q + 4
    · subst j
      exact type10_mid_gap_even_of_Y_ne X Y h17_1 heven (by omega) hYtop
    · exact no_pair_rank_two_single_even_mid_gap_before_second_rank
        X Y hXY h17_1 gopp (by omega) heven (by omega) (by
          rw [hopp_rank]
          omega)
  · exact hodd.1
  · exact hodd.2

private lemma exists_mutation_le_type15_rank_two_of_directed_gaps
    {m q : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g gopp : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hopp_rank : gopp.rank = 2 * q + 4)
    (hg_copy : 1 ≤ X.1.1 g) (hopp_one : X.1.1 gopp = 1)
    (hne : g ≠ gopp) (hopp_type : gopp.type = -g.type)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hodd :
      (g.type = GeneType.Positive →
        ∀ j, 2 ≤ j → j ≤ 2 * q + 4 → ¬ Even j →
          ((2 : ℚ), (0 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1)) ∧
      (g.type = GeneType.Negative →
        ∀ j, 2 ≤ j → j ≤ 2 * q + 4 → ¬ Even j →
          ((0 : ℚ), (2 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1)))
    (hYtop : Chromosome.prime^[2 * q + 4] Y.1.1 ≠ 0)
    (hsucc : RankTwoSingleType15Succ (q₂ := q) X Y g) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_type15_of_genes_of_gaps hg_pol
    (Nat.zero_le (q + 1)) X Y hXY g gopp rfl hopp_type
      (show g.rank = 2 * 0 + 2 by omega)
      (show gopp.rank = 2 * (q + 1) + 2 by omega)
      hg_copy (by omega) hne
  · simpa using no_pair_rank_two_single_low_fallback_type15_pred_gap
      X Y hXY g hlow
  · intro j hjlo hjhi heven
    by_cases hjtop : j = 2 * q + 4
    · subst j
      exact type10_mid_gap_even_of_Y_ne X Y h17_1 heven (by omega) hYtop
    · exact no_pair_rank_two_single_even_mid_gap_before_second_rank
        X Y hXY h17_1 gopp (by omega) heven (by omega) (by
          rw [hopp_rank]
          omega)
  · exact hodd.1
  · exact hodd.2
  · simpa [show 2 * (q + 1) + 3 = 2 * q + 5 by omega] using
      no_pair_rank_two_single_type15_succ_gap X Y hXY g hsucc

/-- Complete low-component fallback for any positive multiplicity of the
rank-two gene. -/
lemma exists_mutation_le_no_pair_rank_two_copy_low_fallback
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ h : Gene, 0 < X.1.1 h → Y.1.1 h ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ h : Gene, 0 < X.1.1 h → g.rank ≤ h.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized) (hg_rank : g.rank = 2)
    (hg_copy : 1 ≤ X.1.1 g)
    (hlow : RankTwoSingleLowFallback X Y g) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨gopp, q, hopp_type, hXopp, hopp_min, _hopp_pol, hopp_rank⟩ :=
    no_pair_rank_two_single_min_opposite_gene_data X Y hXY hXpol
      hno_pair g hgX hgmin hg_pol hg_rank hlow
  have hne : g ≠ gopp := by
    intro heq
    rw [← heq, hg_rank] at hopp_rank
    omega
  have hYtop := no_pair_rank_two_single_Y_iterate_ne_at_common_free_gene_rank
    X Y hXY hcommon gopp hXopp hopp_rank _hopp_pol
  rcases no_pair_rank_two_single_low_fallback_gap_split X Y g hlow with
    htwo | hone
  · have hodd := case2_odd_mid_gaps_before_min_opposite_of_two
      X Y hXY h17_1 hXpol g gopp hopp_rank hXopp hopp_min htwo
    by_cases hopp_two : 2 ≤ X.1.1 gopp
    · exact exists_mutation_le_type17_rank_two_of_directed_gaps
        X Y hXY h17_1 g gopp hg_pol hg_rank hopp_rank hg_copy hopp_two
          hne hopp_type hlow hodd hYtop
    · have hopp_one : X.1.1 gopp = 1 := by omega
      have hsucc := case2_type15_succ_of_min_opposite_one
        X Y hXY h17_1 hXpol g gopp hopp_rank hopp_one hopp_type hopp_min
          hlow hYtop
      exact exists_mutation_le_type15_rank_two_of_directed_gaps
        X Y hXY h17_1 g gopp hg_pol hg_rank hopp_rank hg_copy hopp_one
          hne hopp_type hlow hodd hYtop hsucc
  · have hodd := case2_odd_mid_gaps_before_min_opposite
      X Y hXY h17_1 hXpol g gopp hopp_rank hXopp hopp_min hone
    by_cases hopp_two : 2 ≤ X.1.1 gopp
    · exact exists_mutation_le_type17_rank_two_of_directed_gaps
        X Y hXY h17_1 g gopp hg_pol hg_rank hopp_rank hg_copy hopp_two
          hne hopp_type hlow hodd hYtop
    · have hopp_one : X.1.1 gopp = 1 := by omega
      have hsucc := case2_type15_succ_of_min_opposite_one
        X Y hXY h17_1 hXpol g gopp hopp_rank hopp_one hopp_type hopp_min
          hlow hYtop
      exact exists_mutation_le_type15_rank_two_of_directed_gaps
        X Y hXY h17_1 g gopp hg_pol hg_rank hopp_rank hg_copy hopp_one
          hne hopp_type hlow hodd hYtop hsucc

end MixPi2Lambda
