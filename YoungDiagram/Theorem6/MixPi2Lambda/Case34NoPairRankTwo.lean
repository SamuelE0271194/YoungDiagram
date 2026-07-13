import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPair

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair rank-two boundary setup

The rank-`2` no-pair branch is the new Label 4 boundary case.  This file keeps
only the common bookkeeping facts needed before the actual mutation subcases:
the opposite sign at the same rank is absent, the coefficient of the minimal
gene is either one or at least two, and removing one copy preserves the lower
rank bound on the remaining support.  The final lemma is a thin dispatcher that
lets the future mutation solvers plug into this prepared split.
-/

/-- Basic data for the rank-`2` boundary of the Label 4 no-pair branch. -/
lemma no_pair_rank_two_boundary_data {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hg_pol : g.type ≠ GeneType.NonPolarized) :
    X.1.1 (-g) = 0 ∧ (X.1.1 g = 1 ∨ 2 ≤ X.1.1 g) := by
  refine ⟨no_pair_neg_gene_zero hno_pair hg_pol hgX, ?_⟩
  omega

/-- Removing one copy of the rank-`2` minimal gene preserves the support facts
needed by the next rank-two subcase split. -/
lemma no_pair_rank_two_rest_support_data {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
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
    (restAfterG : Chromosome)
    (hrestAfterG : restAfterG = X.1.1 - Finsupp.single g 1) :
    ∀ h : Gene, 0 < restAfterG h →
      0 < X.1.1 h ∧ 2 ≤ h.rank ∧
        h.type ≠ GeneType.NonPolarized ∧ h ≠ -g := by
  intro h hhrest
  have hXh : 0 < X.1.1 h := by
    have hle : restAfterG h ≤ X.1.1 h := by
      rw [hrestAfterG]
      simp only [Finsupp.tsub_apply]
      omega
    exact lt_of_lt_of_le hhrest hle
  have hpol : h.type ≠ GeneType.NonPolarized :=
    IsPolarized_def'.mp hXpol h (Finsupp.mem_support_iff.mpr (ne_of_gt hXh))
  have hneg_zero : X.1.1 (-g) = 0 :=
    no_pair_neg_gene_zero hno_pair hg_pol hgX
  have hne_neg : h ≠ -g := by
    intro hh
    rw [hh, hneg_zero] at hXh
    omega
  have hrank_ge : 2 ≤ h.rank := by
    have hle := hgmin h hXh
    rwa [hg_rank] at hle
  exact ⟨hXh, hrank_ge, hpol, hne_neg⟩

/-- If the remainder after removing one copy of the rank-`2` minimal gene is
nonzero, choose its own minimal-rank gene and package the inherited facts. -/
lemma no_pair_rank_two_rest_min_gene_data {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
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
    (restAfterG : Chromosome)
    (hrestAfterG : restAfterG = X.1.1 - Finsupp.single g 1)
    (hrest_ne : restAfterG ≠ 0) :
    ∃ g₂ : Gene,
      0 < restAfterG g₂ ∧
      (∀ h : Gene, 0 < restAfterG h → g₂.rank ≤ h.rank) ∧
      0 < X.1.1 g₂ ∧
      2 ≤ g₂.rank ∧
      g₂.type ≠ GeneType.NonPolarized ∧
      g₂ ≠ -g := by
  obtain ⟨g₂, hg₂_rest, hg₂min⟩ :=
    Mix2LambdaSection17.exists_min_rank_gene hrest_ne
  obtain ⟨hXg₂, hg₂_rank_ge, hg₂_pol, hg₂_ne_neg⟩ :=
    no_pair_rank_two_rest_support_data X hXpol hno_pair g hgX hgmin
      hg_pol hg_rank restAfterG hrestAfterG g₂ hg₂_rest
  exact ⟨g₂, hg₂_rest, hg₂min, hXg₂, hg₂_rank_ge, hg₂_pol, hg₂_ne_neg⟩

/-- Shape of the singleton-empty leaf in the rank-`2` no-pair boundary.

If removing one copy of the minimal rank-`2` gene leaves nothing, then `X` is
exactly that one gene.  This also pins the ambient rank parameter to `m = 0`
and records the diagonal signature/vanishing successor facts needed by the
future leaf solver. -/
lemma no_pair_rank_two_single_empty_shape {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
    (g : Gene)
    (hgX : 0 < X.1.1 g)
    (hg_rank : g.rank = 2)
    (restAfterG : Chromosome)
    (hrestAfterG : restAfterG = X.1.1 - Finsupp.single g 1)
    (_hg_one : X.1.1 g = 1)
    (hrest_zero : restAfterG = 0) :
    X.1.1 = Finsupp.single g 1 ∧
      m = 0 ∧
      signature X.1.1 = ((1 : ℚ), (1 : ℚ)) ∧
      Chromosome.prime^[3] X.1.1 = 0 := by
  have hXeq : X.1.1 = Finsupp.single g 1 := by
    rw [← sub_single_add_single_eq hgX, ← hrestAfterG, hrest_zero]
    simp
  have hm0 : m = 0 := by
    have hrankX : X.1.1.rank = 2 := by
      rw [hXeq, rank_single, one_smul, hg_rank]
    rw [X.2] at hrankX
    omega
  have hg_sig : g.signature = ((1 : ℚ), (1 : ℚ)) := by
    have hgeven : Even g.rank := by
      rw [hg_rank]
      exact ⟨1, by omega⟩
    rw [Gene.signature_even_half hgeven, hg_rank]
    norm_num
  have hsigX : signature X.1.1 = ((1 : ℚ), (1 : ℚ)) := by
    rw [hXeq, signature_single g.rank_pos]
    simp [hg_sig]
  have hX3 : Chromosome.prime^[3] X.1.1 = 0 := by
    rw [hXeq, ← Gene.ofRank_eq_gene, hg_rank]
    exact prime_iterate_ofRank_eq_zero (n := 2) (k := 3) (ε := g.type) (by omega)
  exact ⟨hXeq, hm0, hsigX, hX3⟩

/-- Removing two copies of the rank-`2` minimal gene preserves the support facts
needed by the double branch. -/
lemma no_pair_rank_two_double_rest_support_data {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
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
    (restAfterDouble : Chromosome)
    (hrestAfterDouble :
      restAfterDouble = X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) :
    ∀ h : Gene, 0 < restAfterDouble h →
      0 < X.1.1 h ∧ 2 ≤ h.rank ∧
        h.type ≠ GeneType.NonPolarized ∧ h ≠ -g := by
  intro h hhrest
  have hXh : 0 < X.1.1 h := by
    have hle : restAfterDouble h ≤ X.1.1 h := by
      rw [hrestAfterDouble]
      simp only [Finsupp.tsub_apply]
      omega
    exact lt_of_lt_of_le hhrest hle
  have hpol : h.type ≠ GeneType.NonPolarized :=
    IsPolarized_def'.mp hXpol h (Finsupp.mem_support_iff.mpr (ne_of_gt hXh))
  have hneg_zero : X.1.1 (-g) = 0 :=
    no_pair_neg_gene_zero hno_pair hg_pol hgX
  have hne_neg : h ≠ -g := by
    intro hh
    rw [hh, hneg_zero] at hXh
    omega
  have hrank_ge : 2 ≤ h.rank := by
    have hle := hgmin h hXh
    rwa [hg_rank] at hle
  exact ⟨hXh, hrank_ge, hpol, hne_neg⟩

/-- If the double remainder is nonzero, choose its own minimal-rank gene and
package the inherited facts. -/
lemma no_pair_rank_two_double_rest_min_gene_data {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
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
    (restAfterDouble : Chromosome)
    (hrestAfterDouble :
      restAfterDouble = X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (hrest_ne : restAfterDouble ≠ 0) :
    ∃ g₂ : Gene,
      0 < restAfterDouble g₂ ∧
      (∀ h : Gene, 0 < restAfterDouble h → g₂.rank ≤ h.rank) ∧
      0 < X.1.1 g₂ ∧
      2 ≤ g₂.rank ∧
      g₂.type ≠ GeneType.NonPolarized ∧
      g₂ ≠ -g := by
  obtain ⟨g₂, hg₂_rest, hg₂min⟩ :=
    Mix2LambdaSection17.exists_min_rank_gene hrest_ne
  obtain ⟨hXg₂, hg₂_rank_ge, hg₂_pol, hg₂_ne_neg⟩ :=
    no_pair_rank_two_double_rest_support_data X hXpol hno_pair g hgX hgmin
      hg_pol hg_rank restAfterDouble hrestAfterDouble g₂ hg₂_rest
  exact ⟨g₂, hg₂_rest, hg₂min, hXg₂, hg₂_rank_ge, hg₂_pol, hg₂_ne_neg⟩

/-- Shape of the double-empty leaf in the rank-`2` no-pair boundary. -/
lemma no_pair_rank_two_double_empty_shape {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
    (g : Gene)
    (hg_two : 2 ≤ X.1.1 g)
    (hg_rank : g.rank = 2)
    (restAfterDouble : Chromosome)
    (hrestAfterDouble :
      restAfterDouble = X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (hrest_zero : restAfterDouble = 0) :
    X.1.1 = Finsupp.single g 1 + Finsupp.single g 1 ∧
      m = 2 ∧
      signature X.1.1 = ((2 : ℚ), (2 : ℚ)) ∧
      Chromosome.prime^[3] X.1.1 = 0 := by
  have hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g 1 := by
    have h :=
      Mix2LambdaSection17.double_single_add_rest (X := X.1.1) (g := g) hg_two
    rw [← hrestAfterDouble, hrest_zero, add_zero] at h
    exact h.symm
  have hm2 : m = 2 := by
    have hrankX : X.1.1.rank = 4 := by
      rw [hXeq, map_add, rank_single]
      rw [hg_rank]
      norm_num
    rw [X.2] at hrankX
    omega
  have hg_sig : g.signature = ((1 : ℚ), (1 : ℚ)) := by
    have hgeven : Even g.rank := by
      rw [hg_rank]
      exact ⟨1, by omega⟩
    rw [Gene.signature_even_half hgeven, hg_rank]
    norm_num
  have hsigX : signature X.1.1 = ((2 : ℚ), (2 : ℚ)) := by
    have hsingle_sig : signature (Finsupp.single g 1 : Chromosome) = g.signature := by
      rw [signature_single g.rank_pos]
      simp
    rw [hXeq, map_add, hsingle_sig, hg_sig]
    norm_num
  have hX3 : Chromosome.prime^[3] X.1.1 = 0 := by
    have hsingle3 : Chromosome.prime^[3] (Finsupp.single g 1 : Chromosome) = 0 := by
      rw [← Gene.ofRank_eq_gene, hg_rank]
      exact prime_iterate_ofRank_eq_zero (n := 2) (k := 3) (ε := g.type) (by omega)
    rw [hXeq, iterate_map_add, hsingle3]
    simp
  exact ⟨hXeq, hm2, hsigX, hX3⟩

/-- Dispatcher glue for the Label 4 rank-`2` no-pair boundary.

The actual mutation constructions are supplied as three branch solvers: the
minimal gene has multiplicity at least two, the singleton remainder is empty, or
the singleton remainder has its own minimal gene. -/
lemma exists_mutation_le_no_pair_rank_two_of_subcases {m : ℕ}
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
    (double :
      X.1.1 (-g) = 0 →
      2 ≤ X.1.1 g →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (single_empty :
      X.1.1 (-g) = 0 →
      ∀ restAfterG : Chromosome,
        restAfterG = X.1.1 - Finsupp.single g 1 →
        X.1.1 g = 1 →
        restAfterG = 0 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (single_rest :
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
          ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨hneg_zero, hsingle_or_double⟩ :=
    no_pair_rank_two_boundary_data X hno_pair g hgX hg_pol
  rcases hsingle_or_double with hg_one | hg_two
  · let restAfterG : Chromosome := X.1.1 - Finsupp.single g 1
    by_cases hrest_ne : restAfterG ≠ 0
    · obtain ⟨g₂, hg₂_rest, hg₂min, hXg₂, hg₂_rank_ge, hg₂_pol, hg₂_ne_neg⟩ :=
        no_pair_rank_two_rest_min_gene_data X hXpol hno_pair g hgX hgmin
          hg_pol hg_rank restAfterG rfl hrest_ne
      exact single_rest hneg_zero restAfterG rfl hg_one hrest_ne g₂
        hg₂_rest hg₂min hXg₂ hg₂_rank_ge hg₂_pol hg₂_ne_neg
    · exact single_empty hneg_zero restAfterG rfl hg_one (Classical.not_not.mp hrest_ne)
  · exact double hneg_zero hg_two

end MixPi2Lambda
