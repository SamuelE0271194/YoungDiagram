import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDouble

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair rank-two double-rest split

After two copies of the minimal rank-`2` gene have been removed, a nonempty
remainder has its own minimal gene `g₂`.  This file records the next structural
split only: `g₂` is either the same rank-`2` gene again (extra multiplicity), or
its rank is already in the rank-`≥4` window.
-/

/-- In the rank-`2` double branch, the first gene of the nonempty double
remainder is either the original minimal gene again, or it has rank `2*q+4`.
-/
lemma no_pair_rank_two_double_rest_rank_split {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
    (g g₂ : Gene)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hg₂_rank_ge : 2 ≤ g₂.rank)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_ne_neg : g₂ ≠ -g) :
    g₂ = g ∨ ∃ q₂ : ℕ, g₂.rank = 2 * q₂ + 4 := by
  have hg₂_even : Even g₂.rank :=
    Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
      X.1.2 hXg₂ hg₂_pol
  rcases eq_or_lt_of_le hg₂_rank_ge with hg₂_rank_two | hg₂_rank_gt_two
  · left
    have hrank_eq : g₂.rank = g.rank := by omega
    cases hgt : g.type <;> cases hg₂t : g₂.type
    · exact False.elim (hg_pol hgt)
    · exact False.elim (hg_pol hgt)
    · exact False.elim (hg_pol hgt)
    · exact False.elim (hg₂_pol hg₂t)
    · exact Gene.ext hrank_eq (by rw [hg₂t, hgt])
    · exfalso
      apply hg₂_ne_neg
      exact Gene.ext (by rw [Gene.neg_rank]; exact hrank_eq) (by simp [hg₂t, hgt])
    · exact False.elim (hg₂_pol hg₂t)
    · exfalso
      apply hg₂_ne_neg
      exact Gene.ext (by rw [Gene.neg_rank]; exact hrank_eq) (by simp [hg₂t, hgt])
    · exact Gene.ext hrank_eq (by rw [hg₂t, hgt])
  · right
    obtain ⟨r, hr⟩ := hg₂_even
    cases r with
    | zero =>
        omega
    | succ r =>
        cases r with
        | zero =>
            omega
        | succ q₂ =>
            refine ⟨q₂, ?_⟩
            rw [hr]
            ring

/-- Dispatcher glue for the nonempty double-remainder branch. -/
lemma exists_mutation_le_no_pair_rank_two_double_rest_of_rank_split {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (g g₂ : Gene)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hg₂_rank_ge : 2 ≤ g₂.rank)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_ne_neg : g₂ ≠ -g)
    (same_gene :
      g₂ = g →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (rank_ge_four :
      ∀ q₂ : ℕ, g₂.rank = 2 * q₂ + 4 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  rcases no_pair_rank_two_double_rest_rank_split X g g₂ hXg₂ hg_pol hg_rank
      hg₂_rank_ge hg₂_pol hg₂_ne_neg with hsame | ⟨q₂, hg₂_rank_q⟩
  · exact same_gene hsame
  · exact rank_ge_four q₂ hg₂_rank_q

/-- Full dispatcher glue for the rank-`2` double branch after the rank split.

Future leaf solvers only need to cover: the empty double remainder, the
same-gene extra-multiplicity remainder, and the rank-`≥4` remainder.
-/
lemma exists_mutation_le_no_pair_rank_two_double_of_rank_split {m : ℕ}
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
    (same_gene :
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
          g₂ = g →
          ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (rank_ge_four :
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
          ∀ q₂ : ℕ, g₂.rank = 2 * q₂ + 4 →
          ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  refine exists_mutation_le_no_pair_rank_two_double_of_subcases X Y hXpol
    hno_pair g hgX hgmin hg_pol hg_rank hg_two double_empty ?_
  intro hneg_zero restAfterDouble hrestAfterDouble hrest_ne g₂ hg₂_rest
    hg₂min hXg₂ hg₂_rank_ge hg₂_pol hg₂_ne_neg
  exact exists_mutation_le_no_pair_rank_two_double_rest_of_rank_split X Y g g₂
    hXg₂ hg_pol hg_rank hg₂_rank_ge hg₂_pol hg₂_ne_neg
    (same_gene hneg_zero restAfterDouble hrestAfterDouble hrest_ne g₂
      hg₂_rest hg₂min hXg₂ hg₂_rank_ge hg₂_pol hg₂_ne_neg)
    (rank_ge_four hneg_zero restAfterDouble hrestAfterDouble hrest_ne g₂
      hg₂_rest hg₂min hXg₂ hg₂_rank_ge hg₂_pol hg₂_ne_neg)

end MixPi2Lambda
