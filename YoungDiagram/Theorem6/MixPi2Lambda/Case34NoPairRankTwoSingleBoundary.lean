import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingle

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Singleton coefficient-one successor boundary

This module owns the final exact-one leaf after the low Type15/Type17 splits.
The empty remainder is impossible; the nonempty remainder is handled by the
next-gene continuation built above this module.
-/

/-- If a chromosome has total multiplicity one, it is a single gene. -/
private lemma eq_single_of_totalMult_eq_one
    {W : Chromosome} (hsum : W.sum (fun _ n => n) = 1) :
    ∃ g : Gene, W = Finsupp.single g 1 := by
  have hWne : W ≠ 0 := by
    intro hzero
    rw [hzero, Finsupp.sum_zero_index] at hsum
    omega
  obtain ⟨g, hg, _⟩ := Mix2LambdaSection17.exists_min_rank_gene hWne
  have hg_le : W g ≤ W.sum (fun _ n => n) :=
    Finsupp.single_eval_le_sum W (g := fun n : ℕ => n) rfl
      (fun _ => Nat.zero_le _) g
  have hg_one : W g = 1 := by omega
  refine ⟨g, ?_⟩
  ext z
  by_cases hzg : z = g
  · subst z
    simp [hg_one]
  · have hrest_sum := totalMult_sub_single_one hg_one
    rw [hsum] at hrest_sum
    have hgz : g ≠ z := fun h => hzg h.symm
    have hz_le :
        (W - Finsupp.single g 1 : Chromosome) z ≤
          (W - Finsupp.single g 1 : Chromosome).sum (fun _ n => n) :=
      Finsupp.single_eval_le_sum _ (g := fun n : ℕ => n) rfl
        (fun _ => Nat.zero_le _) z
    have hz_zero : W z = 0 := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hgz] at hz_le
      omega
    simp [hzg, hz_zero]

/-- The coefficient-one, successor-preferred leaf cannot have empty remainder
after removing the low gene and the later gene. -/
lemma exists_mutation_le_no_pair_rank_two_single_preferred_one_empty
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1) (g g₂ : Gene)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hg₂_one : X.1.1 g₂ = 1)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hone : RankTwoSingleExactOne X Y g)
    (hpreferred : RankTwoSingleSuccPreferred (q₂ := q₂) X Y g₂)
    (restAfterG₂ : Chromosome)
    (hrestAfterG₂ :
      restAfterG₂ = X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1)
    (hrest_zero : restAfterG₂ = 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  exfalso
  have hXdecomp := Mix2LambdaSection17.single_pair_add_rest
    (X := X.1.1) (g := g) (h := g₂) (by omega) (by omega) hne
  have hsub_zero :
      X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1 = 0 := by
    rw [← hrestAfterG₂, hrest_zero]
  rw [hsub_zero, add_zero] at hXdecomp
  have hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g₂ 1 :=
    hXdecomp.symm
  have hXrank : X.1.1.rank = 2 * q₂ + 6 := by
    rw [hXeq, map_add, rank_single, rank_single, one_smul, one_smul,
      hg_rank, hg₂_rank]
    omega
  have hm : m + 2 = 2 * q₂ + 6 := by
    rw [← X.2]
    exact hXrank
  have hg_eq :
      (Finsupp.single g 1 : Chromosome) = Gene.ofRank 2 g.type := by
    rw [← Gene.ofRank_eq_gene (g := g), hg_rank]
  have hg₂_eq :
      (Finsupp.single g₂ 1 : Chromosome) =
        Gene.ofRank (2 * q₂ + 4) (-g.type) := by
    rw [← Gene.ofRank_eq_gene (g := g₂), hg₂_rank, hg₂_neg]
  have hX1sig :
      signature (Chromosome.prime^[1] X.1.1) =
        (((q₂ + 2 : ℕ) : ℚ), ((q₂ + 2 : ℕ) : ℚ)) := by
    rw [hXeq, hg_eq, hg₂_eq, Function.iterate_one, map_add, prime_ofRank,
      prime_ofRank]
    have hsum := signature_ofRank_sum_even (ε := g.type)
      (m := 1) (n := 2 * q₂ + 3)
      (show Even (1 + (2 * q₂ + 3)) by exact ⟨q₂ + 2, by omega⟩)
    convert hsum using 1
    all_goals norm_num
    all_goals ring
  have hle1 := le_iff_dominates.mp hXY.le 1
  have hY1rank : (Chromosome.prime^[1] Y.1.1).rank = 2 * q₂ + 5 := by
    rcases hlow with ⟨hg_pos, hnot, _⟩ | ⟨hg_neg, hnot, _⟩
    · rcases hone with ⟨_, hone⟩ | ⟨hcontra, _⟩
      · have hsnd_eq :
            (signature (Chromosome.prime^[1] Y.1.1)).2 =
              (signature (Chromosome.prime^[1] X.1.1)).2 :=
          le_antisymm (le_of_not_gt hnot) hle1.2
        have hsum := @signature_sum_eq_rank (Chromosome.prime^[1] Y.1.1)
        have hcast :
            ((Chromosome.prime^[1] Y.1.1).rank : ℚ) = 2 * q₂ + 5 := by
          rw [← hsum]
          simp only [hX1sig] at hone hsnd_eq
          push_cast at hone hsnd_eq ⊢
          norm_num at hone hsnd_eq ⊢
          linarith
        exact_mod_cast hcast
      · simp [hg_pos] at hcontra
    · rcases hone with ⟨hcontra, _⟩ | ⟨_, hone⟩
      · simp [hg_neg] at hcontra
      · have hfst_eq :
            (signature (Chromosome.prime^[1] Y.1.1)).1 =
              (signature (Chromosome.prime^[1] X.1.1)).1 :=
          le_antisymm (le_of_not_gt hnot) hle1.1
        have hsum := @signature_sum_eq_rank (Chromosome.prime^[1] Y.1.1)
        have hcast :
            ((Chromosome.prime^[1] Y.1.1).rank : ℚ) = 2 * q₂ + 5 := by
          rw [← hsum]
          simp only [hX1sig] at hone hfst_eq
          push_cast at hone hfst_eq ⊢
          norm_num at hone hfst_eq ⊢
          linarith
        exact_mod_cast hcast
  have hYsumQ : Y.1.1.sum (fun _ n => (n : ℚ)) = 1 := by
    have hcells := MixLambdaPi.cells (Z := Y.1.1)
    have hYrank : Y.1.1.rank = 2 * q₂ + 6 := by rw [Y.2, hm]
    have hYprimeRank : Y.1.1.prime.rank = 2 * q₂ + 5 := by
      simpa [Function.iterate_one] using hY1rank
    rw [hYrank, hYprimeRank] at hcells
    norm_num at hcells ⊢
    exact hcells.symm
  have hYsum : Y.1.1.sum (fun _ n => n) = 1 := by
    exact_mod_cast hYsumQ
  obtain ⟨y, hYeq⟩ := eq_single_of_totalMult_eq_one hYsum
  have hyrank : y.rank = 2 * q₂ + 6 := by
    have h := Y.2
    rw [hYeq, rank_single, one_smul, hm] at h
    exact h
  have hy_eq :
      (Finsupp.single y 1 : Chromosome) = Gene.ofRank y.rank y.type :=
    Gene.ofRank_eq_gene.symm
  have hy_pol : y.type ≠ GeneType.NonPolarized := by
    have hy_pos : 0 < Y.1.1 y := by rw [hYeq]; simp
    have hy_even : Even y.rank := by rw [hyrank]; exact ⟨q₂ + 3, by omega⟩
    have hyeven : 0 < Y.1.1.evenPart y := by
      rw [evenPart_eq, Finsupp.filter_apply, if_pos hy_even]
      exact hy_pos
    exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.1) y
      (Finsupp.mem_support_iff.mpr hyeven.ne')
  rcases hone with ⟨hg_pos, hone⟩ | ⟨hg_neg, hone⟩
  · have hg₂_neg_type : g₂.type = GeneType.Negative := by
      rw [hg₂_neg, hg_pos, GeneType.neg_positive]
    rcases hpreferred with ⟨hcontra, _⟩ | ⟨_, hsnd⟩
    · simp [hg₂_neg_type] at hcontra
    · cases hy : y.type with
      | NonPolarized => exact hy_pol hy
      | Positive =>
          have hXsucc : Chromosome.prime^[2 * q₂ + 5] X.1.1 = 0 := by
            rw [hXeq, hg_eq, hg₂_eq, iterate_map_add]
            simp only [prime_iterate_ofRank]
            simp
          rw [hXsucc, map_zero, hYeq, hy_eq, prime_iterate_ofRank, hyrank, hy,
            show 2 * q₂ + 6 - (2 * q₂ + 5) = 1 by omega,
            signature_ofRank_one_positive] at hsnd
          norm_num at hsnd
      | Negative =>
          rw [hX1sig, hYeq, hy_eq, prime_iterate_ofRank, hyrank, hy,
            show 2 * q₂ + 6 - 1 = 2 * q₂ + 5 by omega] at hone
          simp only [signature_ofRank, show 2 * q₂ + 5 ≠ 0 by omega,
            ↓reduceDIte, Gene.signature_of_negative] at hone
          rw [if_neg (Nat.not_even_iff_odd.mpr ⟨q₂ + 2, by omega⟩)] at hone
          push_cast at hone
          linarith
  · have hg₂_pos_type : g₂.type = GeneType.Positive := by
      rw [hg₂_neg, hg_neg, GeneType.neg_negative]
    rcases hpreferred with ⟨_, hfst⟩ | ⟨hcontra, _⟩
    · cases hy : y.type with
      | NonPolarized => exact hy_pol hy
      | Positive =>
          rw [hX1sig, hYeq, hy_eq, prime_iterate_ofRank, hyrank, hy,
            show 2 * q₂ + 6 - 1 = 2 * q₂ + 5 by omega] at hone
          simp only [signature_ofRank, show 2 * q₂ + 5 ≠ 0 by omega,
            ↓reduceDIte, Gene.signature_of_positive] at hone
          rw [if_neg (Nat.not_even_iff_odd.mpr ⟨q₂ + 2, by omega⟩)] at hone
          push_cast at hone
          linarith
      | Negative =>
          have hXsucc : Chromosome.prime^[2 * q₂ + 5] X.1.1 = 0 := by
            rw [hXeq, hg_eq, hg₂_eq, iterate_map_add]
            simp only [prime_iterate_ofRank]
            simp
          rw [hXsucc, map_zero, hYeq, hy_eq, prime_iterate_ofRank, hyrank, hy,
            show 2 * q₂ + 6 - (2 * q₂ + 5) = 1 by omega,
            signature_ofRank_one_negative] at hfst
          norm_num at hfst
    · simp [hg₂_pos_type] at hcontra

/-- The coefficient-one successor-preferred branch reduced to a nonempty
remainder after removing `g` and `g₂`; the empty remainder is impossible. -/
lemma exists_mutation_le_no_pair_rank_two_single_preferred_one_of_nonempty
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1) (g g₂ : Gene)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hg₂_one : X.1.1 g₂ = 1)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hone : RankTwoSingleExactOne X Y g)
    (hpreferred : RankTwoSingleSuccPreferred (q₂ := q₂) X Y g₂)
    (nonempty :
      ∀ restAfterG₂ : Chromosome,
        restAfterG₂ =
          X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1 →
        restAfterG₂ ≠ 0 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restAfterG₂ : Chromosome :=
    X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1
  by_cases hrest : restAfterG₂ = 0
  · exact exists_mutation_le_no_pair_rank_two_single_preferred_one_empty
      X Y hXY g g₂ hg_rank hg₂_rank hg_one hg₂_one hne hg₂_neg
      hlow hone hpreferred restAfterG₂ rfl hrest
  · exact nonempty restAfterG₂ rfl hrest

/-- Exact-one singleton branch with every closed Type15/Type17/empty-remainder
subcase discharged.  The only remaining input is the nonempty third-gene
continuation. -/
lemma exists_mutation_le_no_pair_rank_two_single_exact_one_of_nonempty
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g g₂ : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hXg₂ : 0 < X.1.1 g₂)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
      2 * q₂ + 4 ≤ h.rank)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hone : RankTwoSingleExactOne X Y g)
    (hYsucc : Chromosome.prime^[2 * q₂ + 5] Y.1.1 ≠ 0)
    (nonempty :
      X.1.1 g₂ = 1 →
      RankTwoSingleSuccPreferred (q₂ := q₂) X Y g₂ →
      ∀ restAfterG₂ : Chromosome,
        restAfterG₂ =
          X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1 →
        restAfterG₂ ≠ 0 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_no_pair_rank_two_single_exact_one_of_preferred_one
    X Y hXY h17_1 hr1 g g₂ hg_pol hg₂_pol hg_rank hg₂_rank
      hg_one hXg₂ hne hg₂_neg h2nd hlow hone hYsucc
  intro hg₂_one hpreferred
  exact exists_mutation_le_no_pair_rank_two_single_preferred_one_of_nonempty
    X Y hXY g g₂ hg_rank hg₂_rank hg_one hg₂_one hne hg₂_neg
      hlow hone hpreferred (nonempty hg₂_one hpreferred)

/-- Select and normalize the third gene in the only remaining nonempty
remainder branch. -/
lemma no_pair_rank_two_single_third_gene_data
    {m q₂ : ℕ} (X : nMixPi2Lambda (m + 2))
    (hXpol : X.1.1.IsPolarized) (g g₂ : Gene)
    (hg_one : X.1.1 g = 1) (hg₂_one : X.1.1 g₂ = 1)
    (hne : g ≠ g₂)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
      2 * q₂ + 4 ≤ h.rank)
    (restAfterG₂ : Chromosome)
    (hrestAfterG₂ :
      restAfterG₂ = X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1)
    (hrest_ne : restAfterG₂ ≠ 0) :
    ∃ (g₃ : Gene) (q₃ : ℕ),
      0 < restAfterG₂ g₃ ∧
      (∀ h : Gene, 0 < restAfterG₂ h → g₃.rank ≤ h.rank) ∧
      0 < X.1.1 g₃ ∧ g₃ ≠ g ∧ g₃ ≠ g₂ ∧
      g₃.type ≠ GeneType.NonPolarized ∧
      g₃.rank = 2 * q₃ + 4 ∧ q₂ ≤ q₃ := by
  obtain ⟨g₃, hg₃_rest, hg₃min⟩ :=
    Mix2LambdaSection17.exists_min_rank_gene hrest_ne
  have hrest_eq :
      restAfterG₂ = X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1 :=
    hrestAfterG₂
  have hXg₃ : 0 < X.1.1 g₃ := by
    rw [hrest_eq, Finsupp.tsub_apply, Finsupp.tsub_apply] at hg₃_rest
    omega
  have hg₃_ne_g : g₃ ≠ g := by
    intro hsame
    subst g₃
    rw [hrest_eq, Finsupp.tsub_apply, Finsupp.tsub_apply,
      Finsupp.single_eq_same, hg_one] at hg₃_rest
    omega
  have hg₃_ne_g₂ : g₃ ≠ g₂ := by
    intro hsame
    subst g₃
    simp [hrest_eq, Finsupp.tsub_apply, hne, hg₂_one] at hg₃_rest
  have hg₃_first_rest :
      0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g₃ := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hg₃_ne_g.symm]
    exact hXg₃
  have hg₃_rank_ge : 2 * q₂ + 4 ≤ g₃.rank :=
    h2nd g₃ (Finsupp.mem_support_iff.mpr hg₃_first_rest.ne')
  have hg₃_pol : g₃.type ≠ GeneType.NonPolarized :=
    IsPolarized_def'.mp hXpol g₃
      (Finsupp.mem_support_iff.mpr hXg₃.ne')
  have hg₃_even :=
    Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
      X.1.2 hXg₃ hg₃_pol
  obtain ⟨r, hr⟩ := hg₃_even
  have hr_ge : q₂ + 2 ≤ r := by omega
  let q₃ := r - 2
  have hq₂q₃ : q₂ ≤ q₃ := by
    dsimp [q₃]
    omega
  have hg₃_rank : g₃.rank = 2 * q₃ + 4 := by
    dsimp [q₃]
    omega
  exact ⟨g₃, q₃, hg₃_rest, hg₃min, hXg₃, hg₃_ne_g,
    hg₃_ne_g₂, hg₃_pol, hg₃_rank, hq₂q₃⟩

end MixPi2Lambda
