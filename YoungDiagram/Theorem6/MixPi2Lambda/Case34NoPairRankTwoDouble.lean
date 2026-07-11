import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwo

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair rank-two double branch

This module keeps the `2 <= X g` branch separate from the common rank-two
setup.  The lemma below is only a dispatcher: it splits on whether the double
remainder is empty and passes the prepared shape/minimal-gene data to future
leaf solvers.
-/

/-- Rank-`2` double branch reduced to the standard doubled-gene type10 gap
interface.  Unlike the double-empty leaf wrapper, this version does not assume
anything about the remainder after removing two copies of `g`, so it can be
reused by the same-gene-extra and rank-ge-four double leaves. -/
lemma exists_mutation_le_no_pair_rank_two_double_of_type10_gaps {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (g : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hg_two : 2 ≤ X.1.1 g)
    (hgap_pred :
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[1] X.1.1) ≤
        signature (Gene.ofRank 1 g.type) +
          signature (Chromosome.prime^[1] Y.1.1))
    (hgap_mid :
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[2] X.1.1) ≤
        signature (Chromosome.prime^[2] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 g.type) +
          signature (Chromosome.prime^[3] X.1.1) ≤
        signature (Chromosome.prime^[3] Y.1.1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg_rank0 : g.rank = 2 * 0 + 2 := by omega
  have hZle :
      (Y10 (le_refl 0) hg_pol hg_pol).1 +
          (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) ≤ Y.1.1 := by
    refine type10_double_target_add_rest_le_of_gaps
      (q := 0) hg_pol X Y hXY g rfl hg_rank0 hg_two ?_ ?_ ?_
    · simpa using hgap_pred
    · intro j hjlo hjhi
      have hj : j = 2 := by omega
      simpa [hj] using hgap_mid
    · simpa using hgap_succ
  exact exists_mutation_le_type10_of_double hg_pol X Y g rfl hg_rank0
    hg_two hZle

/-- Dispatcher glue for the double minimal-gene branch of the rank-`2` no-pair
case. -/
lemma exists_mutation_le_no_pair_rank_two_double_of_subcases {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene)
    (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hg_two : 2 ≤ X.1.1 g)
    (double_empty :
      X.1.1 (-g) = 0 →
      ∀ restAfterDouble : Chromosome,
        restAfterDouble =
          X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 →
        restAfterDouble = 0 →
        X.1.1 = Finsupp.single g 1 + Finsupp.single g 1 →
        m = 2 →
        signature X.1.1 = ((2 : ℚ), (2 : ℚ)) →
        Chromosome.prime^[3] X.1.1 = 0 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (double_rest :
      X.1.1 (-g) = 0 →
      ∀ restAfterDouble : Chromosome,
        restAfterDouble =
          X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 →
        restAfterDouble ≠ 0 →
        ∀ g₂ : Gene,
          0 < restAfterDouble g₂ →
          (∀ h : Gene, 0 < restAfterDouble h → g₂.rank ≤ h.rank) →
          0 < X.1.1 g₂ →
          2 ≤ g₂.rank →
          g₂.type ≠ GeneType.NonPolarized →
          g₂ ≠ -g →
          ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hneg_zero : X.1.1 (-g) = 0 :=
    no_pair_neg_gene_zero hno_pair hg_pol hgX
  let restAfterDouble : Chromosome :=
    X.1.1 - Finsupp.single g 1 - Finsupp.single g 1
  by_cases hrest_ne : restAfterDouble ≠ 0
  · obtain ⟨g₂, hg₂_rest, hg₂min, hXg₂, hg₂_rank_ge, hg₂_pol, hg₂_ne_neg⟩ :=
      no_pair_rank_two_double_rest_min_gene_data X hXpol hno_pair g hgX hgmin
        hg_pol hg_rank restAfterDouble rfl hrest_ne
    exact double_rest hneg_zero restAfterDouble rfl hrest_ne g₂
      hg₂_rest hg₂min hXg₂ hg₂_rank_ge hg₂_pol hg₂_ne_neg
  · have hrest_zero : restAfterDouble = 0 := Classical.not_not.mp hrest_ne
    obtain ⟨hXeq, hm2, hsigX, hX3⟩ :=
      no_pair_rank_two_double_empty_shape X g hg_two hg_rank restAfterDouble rfl
        hrest_zero
    exact double_empty hneg_zero restAfterDouble rfl hrest_zero hXeq hm2 hsigX hX3

end MixPi2Lambda
