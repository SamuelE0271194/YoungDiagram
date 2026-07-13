import YoungDiagram.Theorem6.Mix2LambdaPi.Case34NegPartner

/-!
# §17 rank-one remainder-double boundary (`Case34PairBranch:67`)

The equal-rank-pair branch reaches a boundary where, after removing the
polarized pair `g⁺(2q+3) + g⁻(2q+3)` (each of multiplicity one), the residue is a
*same-sign* doubled rank-one gene `2 g^ε(1)`.  So

  `X = 2 g^ε(1) + g⁺(2q+3) + g⁻(2q+3)`.

Grouping the doubled rank-one gene with the opposite-sign pair gene gives exactly
the §17 Case-3 type16 move

  `2 g^ε(1) + g^{-ε}(2q+3) → g^ε(2q+5)`,

leaving the same-sign gene `g^ε(2q+3)` untouched in the rest.  This is precisely
the `exists_step_type16_neg_partner` engine, so we assemble its hypotheses here.
-/

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-- The type16 remainder-double step, ε-generic.  `g = g^ε(1)` is the doubled
rank-one gene and `gopp = g^{-ε}(2q+3)` is the opposite-sign pair gene; the
same-sign pair gene `g^ε(2q+3)` (and nothing else below rank `2q+3`) makes up the
rest. -/
lemma exists_step_remainder_double {N q : ℕ} {ε : GeneType}
    (hε : ε ≠ GeneType.NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ h : Gene, 0 < X.1.1 h → Y.1.1 h ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (g gopp : Gene)
    (hg_rank : g.rank = 1) (hg_type : g.type = ε)
    (hgopp_rank : gopp.rank = 2 * q + 3) (hgopp_type : gopp.type = -ε)
    (hg_two : 2 ≤ X.1.1 g) (hgopp_pos : 0 < X.1.1 gopp) (hgopp_one : X.1.1 gopp = 1)
    (hlow : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * q + 3 → h ≠ gopp → h.type = ε) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  classical
  -- `hpos_below` follows from `hlow` (rank ≤ 2q+2 forces `h ≠ gopp`).
  have hpos_below : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * q + 2 → h.type = ε := by
    intro h hh hr
    refine hlow h hh (by omega) ?_
    intro he; subst he; rw [hgopp_rank] at hr; omega
  -- `Y` does not vanish on `1 ≤ j ≤ 2q+3` (top-charge argument via `gopp`).
  have hYne : ∀ j, 1 ≤ j → j ≤ 2 * q + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0 := by
    intro j hjlo hjhi hYzero
    have hYzero3 : Chromosome.prime^[2 * q + 3] Y.1.1 = 0 := by
      have hle := (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := j)).2 hYzero
      rw [← Chromosome.prime_iterate_eq_zero_rank_le]
      intro h hh; exact le_trans (hle h hh) hjhi
    have hYrank : ∀ h : Gene, 0 < Y.1.1 h → h.rank ≤ 2 * q + 3 := by
      intro h hh
      exact (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := 2 * q + 3)).2 hYzero3
        h (Finsupp.mem_support_iff.mpr (ne_of_gt hh))
    have hYpol_top : ∀ h : Gene, 0 < Y.1.1 h → h.rank = 2 * q + 3 →
        h.type ≠ GeneType.NonPolarized := by
      intro h hh hhrank
      have hhodd : Odd h.rank := by rw [hhrank]; exact ⟨q + 1, by ring⟩
      have hodd_part : 0 < Y.1.1.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]; exact hh
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
        (Finsupp.mem_support_iff.mpr hodd_part.ne')
    cases hgt : ε with
    | NonPolarized => exact hε hgt
    | Positive =>
        have hgopp_neg : gopp.type = GeneType.Negative := by rw [hgopp_type, hgt]; rfl
        have hno_neg : Y.1.1 ⟨2 * q + 3, GeneType.Negative, by omega⟩ = 0 := by
          have htop_eq : (⟨2 * q + 3, GeneType.Negative, by omega⟩ : Gene) = gopp :=
            Gene.ext (by dsimp; rw [hgopp_rank]) hgopp_neg.symm
          have hle := hcommon gopp hgopp_pos
          rw [htop_eq]; omega
        have hYsnd0 := signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
          (W := Y.1.1) (p := q + 1) hYpol_top hYrank hno_neg
        have hYsnd0' : (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 = 0 := by
          simpa [show 2 * (q + 1) = 2 * q + 2 by omega] using hYsnd0
        have hXsnd1 := one_le_signature_prime_pred_snd_of_negative (X := X.1.1)
          (gneg := gopp) hgopp_neg hgopp_pos
        have hXsnd1' : 1 ≤ (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 := by
          simpa [hgopp_rank, show 2 * q + 3 - 1 = 2 * q + 2 by omega] using hXsnd1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).2
        linarith
    | Negative =>
        have hgopp_posT : gopp.type = GeneType.Positive := by rw [hgopp_type, hgt]; rfl
        have hno_pos : Y.1.1 ⟨2 * q + 3, GeneType.Positive, by omega⟩ = 0 := by
          have htop_eq : (⟨2 * q + 3, GeneType.Positive, by omega⟩ : Gene) = gopp :=
            Gene.ext (by dsimp; rw [hgopp_rank]) hgopp_posT.symm
          have hle := hcommon gopp hgopp_pos
          rw [htop_eq]; omega
        have hYfst0 := signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
          (W := Y.1.1) (p := q + 1) hYpol_top hYrank hno_pos
        have hYfst0' : (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 = 0 := by
          simpa [show 2 * (q + 1) = 2 * q + 2 by omega] using hYfst0
        have hXfst1 := one_le_signature_prime_pred_fst_of_positive (X := X.1.1)
          (gpos := gopp) hgopp_posT hgopp_pos
        have hXfst1' : 1 ≤ (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 := by
          simpa [hgopp_rank, show 2 * q + 3 - 1 = 2 * q + 2 by omega] using hXfst1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).1
        linarith
  have hsucc := np_succ_gap_of_one hε X Y hXY hXPi h17_1 gopp hgopp_rank hgopp_type
    hgopp_one hlow hYne
  exact exists_step_type16_neg_partner hε X Y hXY hXPi h17_1 g gopp
    hg_rank hg_type hgopp_rank hgopp_type hg_two (by omega) hpos_below hYne hsucc

end Mix2LambdaPi
