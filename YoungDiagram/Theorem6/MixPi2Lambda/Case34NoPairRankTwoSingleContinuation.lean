import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleBoundary
import YoungDiagram.Theorem6.MixPi2Lambda.Case34Seed

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Third-gene continuation for the rank-two singleton branch

The selected third gene cannot lie at the same rank as the second gene: equal
type would make the genes equal, while opposite type would violate no-pair.
Thus the remaining continuation starts at a genuinely later even rank.
-/

/-- In the level-one fallback of §17 Case 2, `X` contains a gene of the sign
opposite to the minimal rank-two gene. -/
lemma no_pair_rank_two_single_exists_opposite_gene
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1) (hXpol : X.1.1.IsPolarized)
    (g : Gene) (hlow : RankTwoSingleLowFallback X Y g) :
    ∃ g₂ : Gene, g₂.type = -g.type ∧ 0 < X.1.1 g₂ := by
  have hXPi : X.1.1 ∈ Variety.Pi := Variety.mem_Pi_iff.mpr hXpol
  have hsig0 : signature X.1.1 = signature Y.1.1 := by
    simpa [Sigma.sigma] using sigma_zero_eq X Y hXY
  have hXeq : (signature X.1.1).1 = (signature X.1.1).2 := by
    simpa using
      Mix2LambdaSection17.signature_prime_iterate_even_eq_components_L4
        X.1.2 (i := 0) (by decide)
  have hYfst_le :
      (signature (Chromosome.prime^[1] Y.1.1)).1 ≤ (signature Y.1.1).1 := by
    simpa [Function.iterate_one] using
      (((signature_prime_le Y.1.1).trans inf_le_left).1)
  have hYsnd_le :
      (signature (Chromosome.prime^[1] Y.1.1)).2 ≤ (signature Y.1.1).2 := by
    simpa [Function.iterate_one] using
      (((signature_prime_le Y.1.1).trans inf_le_left).2)
  rcases hlow with ⟨hg_pos, _, hfst⟩ | ⟨hg_neg, _, hsnd⟩
  · have hmass :
        (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature X.1.1).2 := by
      linarith [hfst, hYfst_le, congrArg Prod.fst hsig0, hXeq]
    obtain ⟨g₂, hg₂_neg, hXg₂⟩ :=
      Sigma.neg_gene_of_b0_gt_a1 X.1.1 hXPi hmass
    exact ⟨g₂, by rw [hg₂_neg, hg_pos, GeneType.neg_positive], hXg₂⟩
  · have hmass :
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature X.1.1).1 := by
      linarith [hsnd, hYsnd_le, congrArg Prod.snd hsig0, hXeq]
    have hnegPi : (-X.1.1) ∈ Variety.Pi := by
      rw [Variety.mem_Pi_iff, ← IsPolarized_iff_neg_polarized]
      exact hXpol
    have hmass_neg :
        (signature (Chromosome.prime^[1] (-X.1.1))).1 <
          (signature (-X.1.1)).2 := by
      rw [← @prime_iterate_neg 1 X.1.1, signature_neg, signature_neg,
        Prod.fst_swap, Prod.snd_swap]
      exact hmass
    obtain ⟨w, hw_neg, hnegXw⟩ :=
      Sigma.neg_gene_of_b0_gt_a1 (-X.1.1) hnegPi hmass_neg
    refine ⟨-w, ?_, ?_⟩
    · rw [Gene.neg_type, hw_neg, GeneType.neg_negative, hg_neg,
        GeneType.neg_negative]
    · simpa using hnegXw

/-- Choose an opposite-sign X-gene of minimum rank among all opposite-sign
genes. -/
lemma no_pair_rank_two_single_min_opposite_gene
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1) (hXpol : X.1.1.IsPolarized)
    (g : Gene) (hlow : RankTwoSingleLowFallback X Y g) :
    ∃ g₂ : Gene,
      g₂.type = -g.type ∧ 0 < X.1.1 g₂ ∧
      ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h → g₂.rank ≤ h.rank := by
  obtain ⟨w, hw_type, hXw⟩ :=
    no_pair_rank_two_single_exists_opposite_gene X Y hXY hXpol g hlow
  let Xopp : Chromosome := X.1.1.filter (fun h => h.type = -g.type)
  have hXopp_ne : Xopp ≠ 0 := by
    intro hzero
    have hw_zero := DFunLike.congr_fun hzero w
    simp [Xopp, hw_type] at hw_zero
    omega
  obtain ⟨g₂, hg₂_opp, hg₂min⟩ :=
    Mix2LambdaSection17.exists_min_rank_gene hXopp_ne
  have hg₂_type : g₂.type = -g.type := by
    by_contra hne
    simp [Xopp, hne] at hg₂_opp
  have hXg₂ : 0 < X.1.1 g₂ := by
    simpa [Xopp, Finsupp.filter_apply, hg₂_type] using hg₂_opp
  refine ⟨g₂, hg₂_type, hXg₂, ?_⟩
  intro h hh_type hXh
  apply hg₂min h
  simpa [Xopp, Finsupp.filter_apply, hh_type] using hXh

/-- The minimum opposite-sign gene lies at a normalized even rank at least
four. -/
lemma no_pair_rank_two_single_min_opposite_gene_data
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1) (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ h : Gene, 0 < X.1.1 h → g.rank ≤ h.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized) (hg_rank : g.rank = 2)
    (hlow : RankTwoSingleLowFallback X Y g) :
    ∃ (g₂ : Gene) (q₂ : ℕ),
      g₂.type = -g.type ∧ 0 < X.1.1 g₂ ∧
      (∀ h : Gene, h.type = -g.type → 0 < X.1.1 h → g₂.rank ≤ h.rank) ∧
      g₂.type ≠ GeneType.NonPolarized ∧ g₂.rank = 2 * q₂ + 4 := by
  obtain ⟨g₂, hg₂_type, hXg₂, hg₂min⟩ :=
    no_pair_rank_two_single_min_opposite_gene X Y hXY hXpol g hlow
  have hg₂_pol : g₂.type ≠ GeneType.NonPolarized := by
    rw [hg₂_type]
    cases ht : g.type <;> simp [ht] at hg_pol ⊢
  have hg₂_even : Even g₂.rank :=
    Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
      X.1.2 hXg₂ hg₂_pol
  have hg₂_ge : 2 ≤ g₂.rank := by
    simpa [hg_rank] using hgmin g₂ hXg₂
  have hg₂_ne : g₂.rank ≠ 2 := by
    intro hrank₂
    have hrank : g.rank = g₂.rank := by omega
    cases hg_type : g.type with
    | NonPolarized => exact hg_pol hg_type
    | Positive =>
        have hg₂_neg : g₂.type = GeneType.Negative := by
          rw [hg₂_type, hg_type, GeneType.neg_positive]
        exact hno_pair ⟨g, g₂, hrank, hg_type, hg₂_neg, hgX, hXg₂⟩
    | Negative =>
        have hg₂_pos : g₂.type = GeneType.Positive := by
          rw [hg₂_type, hg_type, GeneType.neg_negative]
        exact hno_pair ⟨g₂, g, hrank.symm, hg₂_pos, hg_type, hXg₂, hgX⟩
  obtain ⟨r, hr⟩ := hg₂_even
  have hr_ge : 2 ≤ r := by omega
  let q₂ := r - 2
  have hg₂_rank : g₂.rank = 2 * q₂ + 4 := by
    dsimp [q₂]
    omega
  exact ⟨g₂, q₂, hg₂_type, hXg₂, hg₂min, hg₂_pol, hg₂_rank⟩

/-- Distinct polarized no-pair genes of normalized even ranks cannot have equal
rank parameters. -/
lemma no_pair_rank_two_single_third_gene_strict
    {N q₂ q₃ : ℕ} (X : nMixPi2Lambda N)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g₂ g₃ : Gene) (hXg₂ : 0 < X.1.1 g₂) (hXg₃ : 0 < X.1.1 g₃)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₃_pol : g₃.type ≠ GeneType.NonPolarized)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg₃_rank : g₃.rank = 2 * q₃ + 4)
    (hne : g₃ ≠ g₂) (hq : q₂ ≤ q₃) :
    q₂ < q₃ := by
  apply lt_of_le_of_ne hq
  intro heq
  have hrank : g₂.rank = g₃.rank := by omega
  rcases no_pair_rank_two_single_later_type_split g₂ g₃ hg₂_pol hg₃_pol with
    hsame | hopp
  · exact hne (Gene.ext hrank.symm hsame)
  · cases hg₂_type : g₂.type with
    | NonPolarized => exact False.elim (hg₂_pol hg₂_type)
    | Positive =>
        have hg₃_neg : g₃.type = GeneType.Negative := by
          rw [hopp, hg₂_type, GeneType.neg_positive]
        exact hno_pair ⟨g₂, g₃, hrank, hg₂_type, hg₃_neg, hXg₂, hXg₃⟩
    | Negative =>
        have hg₃_pos : g₃.type = GeneType.Positive := by
          rw [hopp, hg₂_type, GeneType.neg_negative]
        exact hno_pair ⟨g₃, g₂, hrank.symm, hg₃_pos, hg₂_type, hXg₃, hXg₂⟩

/-- Across the two-step edge containing `g₂`, the exact-one two-cell gap loses
at most one cell.  Hence the component opposite to the successor preference is
still strict at level `2*q₂+5`. -/
lemma no_pair_rank_two_single_third_succ_other_component
    {m q₂ q₃ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g g₂ : Gene) (hg_rank : g.rank = 2)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hg₂_one : X.1.1 g₂ = 1)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (hpred :
      (g.type = GeneType.Positive →
        ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 → ¬ Even j →
          ((2 : ℚ), (0 : ℚ)) +
              signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1)) ∧
      (g.type = GeneType.Negative →
        ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 → ¬ Even j →
          ((0 : ℚ), (2 : ℚ)) +
              signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1)))
    (hone : RankTwoSingleExactOne X Y g)
    (restAfterG₂ : Chromosome)
    (hrest : restAfterG₂ =
      X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1)
    (hthird : ∀ h : Gene, 0 < restAfterG₂ h → 2 * q₃ + 4 ≤ h.rank)
    (hq : q₂ < q₃) :
    (g₂.type = GeneType.Positive →
      (signature (Chromosome.prime^[2 * q₂ + 5] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q₂ + 5] Y.1.1)).2) ∧
    (g₂.type = GeneType.Negative →
      (signature (Chromosome.prime^[2 * q₂ + 5] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q₂ + 5] Y.1.1)).1) := by
  have hg₂_after_g :
      (X.1.1 - Finsupp.single g 1 : Chromosome) g₂ = 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne]
    exact hg₂_one
  have hrest_sum :
      restAfterG₂.sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 2 := by
    rw [hrest]
    exact totalMult_sub_two_single_one_cast hg_one hg₂_after_g
  have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
  have htail_decomp :
      restAfterG₂ + Finsupp.single g₂ 1 =
        (X.1.1 - Finsupp.single g 1 : Chromosome) := by
    rw [hrest]
    exact sub_single_add_single_eq (by rw [hg₂_after_g]; norm_num)
  have hsig_pred :
      Sigma.sigma X.1.1 (2 * q₂ + 3) =
        Sigma.sigma restAfterG₂ (2 * q₂ + 3) +
          signature (Gene.ofRank 1 g₂.type) := by
    have hprime :
        Chromosome.prime^[2 * q₂ + 3] X.1.1 =
          Chromosome.prime^[2 * q₂ + 3] restAfterG₂ +
            Gene.ofRank 1 g₂.type := by
      rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by omega)]
      conv_lhs => rw [← htail_decomp]
      rw [iterate_map_add]
      have hsingle :
          Chromosome.prime^[2 * q₂ + 3]
              (Finsupp.single g₂ 1 : Chromosome) =
            Gene.ofRank 1 g₂.type := by
        rw [← Gene.ofRank_eq_gene (g := g₂), prime_iterate_ofRank,
          hg₂_rank, show 2 * q₂ + 4 - (2 * q₂ + 3) = 1 by omega]
      rw [hsingle]
    simp [Sigma.sigma, hprime]
  have hsig_succ :
      Sigma.sigma X.1.1 (2 * q₂ + 5) =
        Sigma.sigma restAfterG₂ (2 * q₂ + 5) := by
    have hprime :
        Chromosome.prime^[2 * q₂ + 5] X.1.1 =
          Chromosome.prime^[2 * q₂ + 5] restAfterG₂ := by
      rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by omega)]
      rw [prime_iterate_eq_sub_single_of_rank_le
        (X := (X.1.1 - Finsupp.single g 1 : Chromosome)) (gm := g₂)
        hg₂_after_g (by rw [hg₂_rank]; omega)]
      rw [← hrest]
    simp [Sigma.sigma, hprime]
  have htail_min : ∀ h ∈ restAfterG₂.support, 2 * q₂ + 5 ≤ h.rank := by
    intro h hh
    have hpos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have := hthird h hpos
    omega
  have hdrop_fst := MixLambdaPi.twostep
    (W := restAfterG₂) (i := 2 * q₂ + 3) htail_min
  have hdrop_snd := MixLambdaPi.twostep_snd
    (W := restAfterG₂) (i := 2 * q₂ + 3) htail_min
  have hXdrop_fst_neg : g₂.type = GeneType.Negative →
      (Sigma.sigma X.1.1 (2 * q₂ + 3)).1 -
          (Sigma.sigma X.1.1 (2 * q₂ + 5)).1 =
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro htype
    have hp := congrArg Prod.fst hsig_pred
    have hs := congrArg Prod.fst hsig_succ
    rw [htype, signature_ofRank_one_negative] at hp
    norm_num at hp
    rw [hp, hs, hdrop_fst, hrest_sum, hD]
  have hXdrop_snd_pos : g₂.type = GeneType.Positive →
      (Sigma.sigma X.1.1 (2 * q₂ + 3)).2 -
          (Sigma.sigma X.1.1 (2 * q₂ + 5)).2 =
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro htype
    have hp := congrArg Prod.snd hsig_pred
    have hs := congrArg Prod.snd hsig_succ
    rw [htype, signature_ofRank_one_positive] at hp
    norm_num at hp
    rw [hp, hs, hdrop_snd, hrest_sum, hD]
  constructor
  · intro hg₂_pos
    have hg_neg : g.type = GeneType.Negative := by
      rcases hone with ⟨hg_pos, _⟩ | ⟨hg_neg, _⟩
      · have h := hg₂_neg
        rw [hg_pos, GeneType.neg_positive, hg₂_pos] at h
        contradiction
      · exact hg_neg
    have hgap := (hpred.2 hg_neg (2 * q₂ + 3) (by omega) (by omega)
      (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by ring⟩)).2
    simp only [Prod.snd_add] at hgap
    change 2 + (Sigma.sigma X.1.1 (2 * q₂ + 3)).2 ≤
      (Sigma.sigma Y.1.1 (2 * q₂ + 3)).2 at hgap
    have hXdrop := hXdrop_snd_pos hg₂_pos
    have hYdrop := KEY_Y_snd_odd X Y hr1 (i := 2 * q₂ + 3)
      (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by ring⟩)
    have hYdrop' :
        (Sigma.sigma Y.1.1 (2 * q₂ + 3)).2 -
            (Sigma.sigma Y.1.1 (2 * q₂ + 5)).2 ≤
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
      simpa [show 2 * q₂ + 3 + 2 = 2 * q₂ + 5 by omega] using hYdrop
    simpa [Sigma.sigma] using (by linarith :
      (Sigma.sigma X.1.1 (2 * q₂ + 5)).2 <
        (Sigma.sigma Y.1.1 (2 * q₂ + 5)).2)
  · intro hg₂_neg_type
    have hg_pos : g.type = GeneType.Positive := by
      rcases hone with ⟨hg_pos, _⟩ | ⟨hg_neg, _⟩
      · exact hg_pos
      · have h := hg₂_neg
        rw [hg_neg, GeneType.neg_negative, hg₂_neg_type] at h
        contradiction
    have hgap := (hpred.1 hg_pos (2 * q₂ + 3) (by omega) (by omega)
      (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by ring⟩)).1
    simp only [Prod.fst_add] at hgap
    change 2 + (Sigma.sigma X.1.1 (2 * q₂ + 3)).1 ≤
      (Sigma.sigma Y.1.1 (2 * q₂ + 3)).1 at hgap
    have hXdrop := hXdrop_fst_neg hg₂_neg_type
    have hYdrop := KEY_Y_fst_odd X Y hr1 (i := 2 * q₂ + 3)
      (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by ring⟩)
    have hYdrop' :
        (Sigma.sigma Y.1.1 (2 * q₂ + 3)).1 -
            (Sigma.sigma Y.1.1 (2 * q₂ + 5)).1 ≤
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
      simpa [show 2 * q₂ + 3 + 2 = 2 * q₂ + 5 by omega] using hYdrop
    simpa [Sigma.sigma] using (by linarith :
      (Sigma.sigma X.1.1 (2 * q₂ + 5)).1 <
        (Sigma.sigma Y.1.1 (2 * q₂ + 5)).1)

/-- The coefficient-one successor-aligned branch from §17 Case 2 is complete.
If the other successor component is strict, Type15 applies directly.  If it is
not strict, the Case 2 drop calculation forces a contradiction, whether or not
the remainder after `g₂` is empty. -/
lemma exists_mutation_le_no_pair_rank_two_single_preferred_one
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hg₂_one : X.1.1 g₂ = 1)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
      2 * q₂ + 4 ≤ h.rank)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hone : RankTwoSingleExactOne X Y g)
    (hYsucc : Chromosome.prime^[2 * q₂ + 5] Y.1.1 ≠ 0)
    (hpreferred : RankTwoSingleSuccPreferred (q₂ := q₂) X Y g₂) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hYtop : Chromosome.prime^[2 * q₂ + 4] Y.1.1 ≠ 0 :=
    Chromosome.prime_iterate_ne_zero_if_prime_ne (j := 2 * q₂ + 4)
      (k := 2 * q₂ + 5) (by omega) hYsucc
  by_cases htype15 : RankTwoSingleType15Succ (q₂ := q₂) X Y g
  · exact exists_mutation_le_no_pair_rank_two_single_type15_exact_one
      X Y hXY h17_1 hr1 g g₂ hg_pol hg_rank hg₂_rank hg_one
      (by omega) hne hg₂_neg h2nd hlow hone hYtop htype15
  let restAfterG₂ : Chromosome :=
    X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1
  by_cases hrest : restAfterG₂ = 0
  · exact exists_mutation_le_no_pair_rank_two_single_preferred_one_empty
      X Y hXY g g₂ hg_rank hg₂_rank hg_one hg₂_one hne hg₂_neg
      hlow hone hpreferred restAfterG₂ rfl hrest
  · obtain ⟨g₃, q₃, hg₃_rest, hg₃min, hXg₃, _hg₃_ne_g,
      hg₃_ne_g₂, hg₃_pol, hg₃_rank, hq_le⟩ :=
      no_pair_rank_two_single_third_gene_data X hXpol g g₂ hg_one
        hg₂_one hne h2nd restAfterG₂ rfl hrest
    have hq : q₂ < q₃ :=
      no_pair_rank_two_single_third_gene_strict X hno_pair g₂ g₃
        (by omega) hXg₃ hg₂_pol hg₃_pol hg₂_rank hg₃_rank
          hg₃_ne_g₂ hq_le
    have hthird : ∀ h : Gene, 0 < restAfterG₂ h → 2 * q₃ + 4 ≤ h.rank := by
      intro h hh
      simpa [hg₃_rank] using hg₃min h hh
    have hpred := no_pair_rank_two_single_type17_odd_mid_gaps
      X Y hXY hr1 g hg_rank hg_one h2nd hone
    have hother := no_pair_rank_two_single_third_succ_other_component
      X Y hr1 g g₂ hg_rank hg₂_rank hg_one hg₂_one hne
        hg₂_neg hpred hone restAfterG₂ rfl hthird hq
    apply False.elim
    apply htype15
    rcases hpreferred with ⟨hg₂_pos, _⟩ | ⟨hg₂_neg_type, _⟩
    · have hg_neg : g.type = GeneType.Negative := by
        cases ht : g.type with
        | NonPolarized => exact False.elim (hg_pol ht)
        | Positive =>
            have h := hg₂_neg
            rw [ht, GeneType.neg_positive, hg₂_pos] at h
            contradiction
        | Negative => rfl
      exact Or.inr ⟨hg_neg, hother.1 hg₂_pos⟩
    · have hg_pos : g.type = GeneType.Positive := by
        cases ht : g.type with
        | NonPolarized => exact False.elim (hg_pol ht)
        | Positive => rfl
        | Negative =>
            have h := hg₂_neg
            rw [ht, GeneType.neg_negative, hg₂_neg_type] at h
            contradiction
      exact Or.inl ⟨hg_pos, hother.2 hg₂_neg_type⟩

/-- Callback-free exact-one dispatcher for the opposite-type Case 2 branch. -/
lemma exists_mutation_le_no_pair_rank_two_single_exact_one
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hXg₂ : 0 < X.1.1 g₂)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
      2 * q₂ + 4 ≤ h.rank)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hone : RankTwoSingleExactOne X Y g)
    (hYsucc : Chromosome.prime^[2 * q₂ + 5] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_no_pair_rank_two_single_exact_one_of_preferred_one
    X Y hXY h17_1 hr1 g g₂ hg_pol hg₂_pol hg_rank hg₂_rank
      hg_one hXg₂ hne hg₂_neg h2nd hlow hone hYsucc
  intro hg₂_one hpreferred
  exact exists_mutation_le_no_pair_rank_two_single_preferred_one
    X Y hXY h17_1 hr1 hXpol hno_pair g g₂ hg_pol hg₂_pol
      hg_rank hg₂_rank hg_one hg₂_one hne hg₂_neg h2nd hlow hone
      hYsucc hpreferred

end MixPi2Lambda
