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
