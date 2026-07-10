import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDoubleRest

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair rank-two singleton-rest split

In the singleton branch `X g = 1`, removing the minimal rank-`2` gene leaves no
copy of `g`.  Therefore a nonempty remainder cannot have a rank-`2` polarized
minimal gene: rank `2` would force it to be either `g` or `-g`, both impossible.
The selected remainder gene is consequently already in the rank-`≥4` window.
-/

/-- The minimal gene of a nonempty singleton remainder has normalized rank
`2*q₂+4`. -/
lemma no_pair_rank_two_single_rest_rank_ge_four {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
    (g g₂ : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (restAfterG : Chromosome)
    (hrestAfterG : restAfterG = X.1.1 - Finsupp.single g 1)
    (hg_one : X.1.1 g = 1)
    (hg₂_rest : 0 < restAfterG g₂)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg₂_rank_ge : 2 ≤ g₂.rank)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_ne_neg : g₂ ≠ -g) :
    ∃ q₂ : ℕ, g₂.rank = 2 * q₂ + 4 := by
  have hg₂_ne_g : g₂ ≠ g := by
    intro hsame
    have hrest_g_zero : restAfterG g = 0 := by
      rw [hrestAfterG, Finsupp.tsub_apply, Finsupp.single_eq_same, hg_one]
    rw [hsame, hrest_g_zero] at hg₂_rest
    omega
  rcases no_pair_rank_two_double_rest_rank_split X g g₂ hXg₂ hg_pol hg_rank
      hg₂_rank_ge hg₂_pol hg₂_ne_neg with hsame | hrank
  · exact False.elim (hg₂_ne_g hsame)
  · exact hrank

/-- Dispatcher glue for the nonempty singleton-remainder branch after its rank
normalization. -/
lemma exists_mutation_le_no_pair_rank_two_single_rest_of_rank_ge_four {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (g g₂ : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (restAfterG : Chromosome)
    (hrestAfterG : restAfterG = X.1.1 - Finsupp.single g 1)
    (hg_one : X.1.1 g = 1)
    (hg₂_rest : 0 < restAfterG g₂)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg₂_rank_ge : 2 ≤ g₂.rank)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_ne_neg : g₂ ≠ -g)
    (rank_ge_four :
      ∀ q₂ : ℕ, g₂.rank = 2 * q₂ + 4 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨q₂, hg₂_rank_q⟩ :=
    no_pair_rank_two_single_rest_rank_ge_four X g g₂ hg_pol hg_rank
      restAfterG hrestAfterG hg_one hg₂_rest hXg₂ hg₂_rank_ge
      hg₂_pol hg₂_ne_neg
  exact rank_ge_four q₂ hg₂_rank_q

/-- Full dispatcher glue for the singleton branch `X g = 1`.

The empty remainder branch receives the prepared singleton shape, while the
nonempty branch receives the normalized rank-`≥4` remainder gene.
-/
lemma exists_mutation_le_no_pair_rank_two_single_of_rank_ge_four {m : ℕ}
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
    (hg_one : X.1.1 g = 1)
    (single_empty :
      X.1.1 (-g) = 0 →
      ∀ restAfterG : Chromosome,
        restAfterG = X.1.1 - Finsupp.single g 1 →
        X.1.1 g = 1 →
        restAfterG = 0 →
        X.1.1 = Finsupp.single g 1 →
        m = 0 →
        signature X.1.1 = ((1 : ℚ), (1 : ℚ)) →
        Chromosome.prime^[3] X.1.1 = 0 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (rank_ge_four :
      X.1.1 (-g) = 0 →
      ∀ restAfterG : Chromosome,
        restAfterG = X.1.1 - Finsupp.single g 1 →
        X.1.1 g = 1 →
        restAfterG ≠ 0 →
        ∀ g₂ : Gene,
          0 < restAfterG g₂ →
          (∀ h : Gene, 0 < restAfterG h → g₂.rank ≤ h.rank) →
          0 < X.1.1 g₂ →
          2 ≤ g₂.rank →
          g₂.type ≠ GeneType.NonPolarized →
          g₂ ≠ -g →
          ∀ q₂ : ℕ, g₂.rank = 2 * q₂ + 4 →
          ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hneg_zero : X.1.1 (-g) = 0 :=
    no_pair_neg_gene_zero hno_pair hg_pol hgX
  let restAfterG : Chromosome := X.1.1 - Finsupp.single g 1
  by_cases hrest_ne : restAfterG ≠ 0
  · obtain ⟨g₂, hg₂_rest, hg₂min, hXg₂, hg₂_rank_ge, hg₂_pol, hg₂_ne_neg⟩ :=
      no_pair_rank_two_rest_min_gene_data X hXpol hno_pair g hgX hgmin
        hg_pol hg_rank restAfterG rfl hrest_ne
    exact exists_mutation_le_no_pair_rank_two_single_rest_of_rank_ge_four
      X Y g g₂ hg_pol hg_rank restAfterG rfl hg_one hg₂_rest hXg₂
      hg₂_rank_ge hg₂_pol hg₂_ne_neg
      (rank_ge_four hneg_zero restAfterG rfl hg_one hrest_ne g₂
        hg₂_rest hg₂min hXg₂ hg₂_rank_ge hg₂_pol hg₂_ne_neg)
  · have hrest_zero : restAfterG = 0 := Classical.not_not.mp hrest_ne
    obtain ⟨hXeq, hm0, hsigX, hX3⟩ :=
      no_pair_rank_two_single_empty_shape X g hgX hg_rank restAfterG rfl
        hg_one hrest_zero
    exact single_empty hneg_zero restAfterG rfl hg_one hrest_zero
      hXeq hm0 hsigX hX3

end MixPi2Lambda
