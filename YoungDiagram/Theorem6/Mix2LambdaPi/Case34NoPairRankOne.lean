import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Seed
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34SecondDouble
import YoungDiagram.Theorem6.Mix2LambdaPi.Type14
import YoungDiagram.Theorem6.Mix2LambdaPi.Type16

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

private lemma type16_rank_one_double_tail_gap_pack
    {m p q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (_hXY : X.1 < Y.1)
    (_hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (_h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (_hXpol : X.1.1.IsPolarized)
    (_hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene)
    (_hgX : 0 < X.1.1 g)
    (_hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (_hg_pol : g.type ≠ .NonPolarized)
    (_hp : g.rank = 2 * p + 1) (_hp0 : p = 0)
    (_hg_rank_one : g.rank = 1)
    (_hXneg_zero : X.1.1 (-g) = 0)
    (_hg_two : 2 ≤ X.1.1 g)
    (_hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (_restAfterDouble restAfterType16 : Chromosome)
    (_hg₂_rest : 0 < _restAfterDouble g₂)
    (_hg₂min : ∀ g' : Gene, 0 < _restAfterDouble g' → g₂.rank ≤ g'.rank)
    (_hXg₂ : 0 < X.1.1 g₂)
    (_hg₂_pol : g₂.type ≠ .NonPolarized)
    (_hsame : ¬g₂ = g)
    (_hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (_hopp : g₂.type = -g.type)
    (_hg₂_one : X.1.1 g₂ = 1)
    (_htail_after_double :
      ∀ h ∈ _restAfterDouble.support, 2 * q₂ + 3 ≤ h.rank)
    (_hrestAfterType16_eq :
      restAfterType16 =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
          Finsupp.single g₂ 1)
    (_hg₂_rest_one : _restAfterDouble g₂ = 1)
    (_htail_after_type16 :
      ∀ h ∈ restAfterType16.support, 2 * q₂ + 3 ≤ h.rank)
    (_htype16_rest_total :
      restAfterType16.sum (fun _ n => n) + 3 =
        X.1.1.sum (fun _ n => n)) :
    (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1)) ∧
    (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → Even j →
      (signature (Gene.ofRank 1 g.type) +
            signature (Gene.ofRank 1 g.type)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1)) ∧
    (signature (Gene.ofRank 1 g.type) +
          signature (Chromosome.prime^[2 * q₂ + 4] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)) := by
  sorry

private lemma case4_Ydrop_fst_strong_even
    {m i : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hi : Even i) :
    (Sigma.sigma Y.1.1 i).1 - (Sigma.sigma Y.1.1 (i + 2)).1 ≤
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
  have hcond7 := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi Y.1.2 i
  rw [if_pos hi] at hcond7
  have hdrop := rank_drop_le Y.1.2 i
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
      ((m + 2 : ℕ) : ℚ) := by
    simpa [Sigma.sigma, X.2] using (@signature_sum_eq_rank (Chromosome.prime^[0] X.1.1))
  have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
      ((m + 2 : ℕ) : ℚ) := by
    simpa [Sigma.sigma, Y.2] using (@signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1))
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by exact_mod_cast case4_gap2 X Y hseed1
  linarith

private lemma case4_Ydrop_snd_strong_even
    {m i : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hi : Even i) :
    (Sigma.sigma Y.1.1 i).2 - (Sigma.sigma Y.1.1 (i + 2)).2 ≤
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
  have hcond6 := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi Y.1.2 i
  rw [if_pos hi] at hcond6
  have hdrop := rank_drop_le Y.1.2 i
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
      ((m + 2 : ℕ) : ℚ) := by
    simpa [Sigma.sigma, X.2] using (@signature_sum_eq_rank (Chromosome.prime^[0] X.1.1))
  have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
      ((m + 2 : ℕ) : ℚ) := by
    simpa [Sigma.sigma, Y.2] using (@signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1))
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by exact_mod_cast case4_gap2 X Y hseed1
  linarith

private lemma exists_mutation_le_no_pair_rank_one_double
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_two : 2 ≤ X.1.1 g) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hYprime1_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
    intro hYzero
    have hYrank : ∀ h : Gene, 0 < Y.1.1 h → h.rank ≤ 1 := by
      intro h hh
      have hall :=
        (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := 1)).2 hYzero
      exact hall h (Finsupp.mem_support_iff.mpr (ne_of_gt hh))
    have hYpol_top : ∀ h : Gene, 0 < Y.1.1 h → h.rank = 1 →
        h.type ≠ GeneType.NonPolarized := by
      intro h hh hhrank
      have hhodd : Odd h.rank := by
        rw [hhrank]
        decide
      have hodd_part : 0 < Y.1.1.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]
        exact hh
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
        (Finsupp.mem_support_iff.mpr hodd_part.ne')
    cases htype : g.type with
    | NonPolarized => exact absurd htype hg_pol
    | Positive =>
        have hno_pos : Y.1.1 ⟨1, GeneType.Positive, le_rfl⟩ = 0 := by
          have htop_eq_g : (⟨1, GeneType.Positive, le_rfl⟩ : Gene) = g :=
            Gene.ext (by rw [hg_rank_one]) htype.symm
          have hle := hcommon g hgX
          rw [htop_eq_g]
          omega
        have hYfst0 :=
          signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
            (W := Y.1.1) (p := 0) hYpol_top hYrank hno_pos
        have hYfst0' : (signature Y.1.1).1 = 0 := by
          simpa using hYfst0
        have hXfst1 :=
          one_le_signature_prime_pred_fst_of_positive (X := X.1.1)
            (gpos := g) htype hgX
        have hXfst1' : 1 ≤ (signature X.1.1).1 := by
          simpa [hg_rank_one] using hXfst1
        have hdom := (le_iff_dominates.mp hXY.le 0).1
        simp only [Function.iterate_zero, id_eq] at hdom
        linarith
    | Negative =>
        have hno_neg : Y.1.1 ⟨1, GeneType.Negative, le_rfl⟩ = 0 := by
          have htop_eq_g : (⟨1, GeneType.Negative, le_rfl⟩ : Gene) = g :=
            Gene.ext (by rw [hg_rank_one]) htype.symm
          have hle := hcommon g hgX
          rw [htop_eq_g]
          omega
        have hYsnd0 :=
          signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
            (W := Y.1.1) (p := 0) hYpol_top hYrank hno_neg
        have hYsnd0' : (signature Y.1.1).2 = 0 := by
          simpa using hYsnd0
        have hXsnd1 :=
          one_le_signature_prime_pred_snd_of_negative (X := X.1.1)
            (gneg := g) htype hgX
        have hXsnd1' : 1 ≤ (signature X.1.1).2 := by
          simpa [hg_rank_one] using hXsnd1
        have hdom := (le_iff_dominates.mp hXY.le 0).2
        simp only [Function.iterate_zero, id_eq] at hdom
        linarith
  have hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank :=
    h17_1 1 (by omega) hYprime1_ne
  have hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2 := by
    exact Mix2LambdaSection17.seed_strict_lt_at_odd
      X.1.2 Y.1.2 (i := 1) (by decide) hr1
  have hXsig1_eq :
      (signature (Chromosome.prime^[1] X.1.1)).1 =
        (signature (Chromosome.prime^[1] X.1.1)).2 :=
    Mix2LambdaSection17.signature_prime_iterate_odd_eq_components_L3
      X.1.2 (i := 1) (by decide)
  have hYsig1_eq :
      (signature (Chromosome.prime^[1] Y.1.1)).1 =
        (signature (Chromosome.prime^[1] Y.1.1)).2 :=
    Mix2LambdaSection17.signature_prime_iterate_odd_eq_components_L3
      Y.1.2 (i := 1) (by decide)
  have hgap1 :
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[1] X.1.1) ≤
        signature (Chromosome.prime^[1] Y.1.1) :=
    Mix2LambdaSection17.one_one_le_of_both_lt X.1.2 Y.1.2 hseed1.1 hseed1.2
  let restAfterDouble : Chromosome :=
    X.1.1 - Finsupp.single g 1 - Finsupp.single g 1
  have hrestAfterDouble_ne : restAfterDouble ≠ 0 := by
    intro hzero
    have hXprime_zero : Chromosome.prime^[1] X.1.1 = 0 := by
      rw [prime_iterate_eq_sub_double_single_of_rank_le
        (X := X.1.1) (gm := g) hg_two (i := 1) (by rw [hg_rank_one])]
      dsimp [restAfterDouble] at hzero
      rw [hzero, iterate_map_zero]
    have hgap_rank := case4_gap2 X Y hseed1
    have hYprime_rank_ge_two :
        2 ≤ (Chromosome.prime^[1] Y.1.1).rank := by
      rw [hXprime_zero, map_zero] at hgap_rank
      exact hgap_rank
    have hXrank_two : X.1.1.rank = 2 := by
      have hXeq :=
        Mix2LambdaSection17.double_single_add_rest (X := X.1.1) (g := g) hg_two
      have hrank :
          X.1.1.rank = 1 • g.rank + 1 • g.rank := by
        rw [← hXeq]
        dsimp [restAfterDouble] at hzero
        rw [hzero, add_zero, map_add]
        simp [rank_single]
      rw [hrank, hg_rank_one]
      norm_num
    have hYrank_two : Y.1.1.rank = 2 := by
      rw [Y.2, ← X.2, hXrank_two]
    have hYne : Y.1.1 ≠ 0 := by
      intro hYzero
      rw [hYzero, map_zero] at hYrank_two
      omega
    have hYprime_rank_lt_two :
        (Chromosome.prime^[1] Y.1.1).rank < 2 := by
      change Y.1.1.prime.rank < 2
      have hlt := prime_rank_lt hYne
      rwa [hYrank_two] at hlt
    omega
  have hg_odd : Odd g.rank := by
    rw [hg_rank_one]
    decide
  have hrestAfterDouble_mem : restAfterDouble ∈ Mix (2 • Lambda, Pi) := by
    dsimp [restAfterDouble]
    exact sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hg_odd) hg_odd
  have hprimeX_eq_restAfterDouble :
      Chromosome.prime^[1] X.1.1 =
        Chromosome.prime^[1] restAfterDouble := by
    dsimp [restAfterDouble]
    exact prime_iterate_eq_sub_double_single_of_rank_le
      (X := X.1.1) (gm := g) hg_two (i := 1) (by rw [hg_rank_one])
  have hrestAfterDouble_total :
      restAfterDouble.sum (fun _ n => n) + 2 =
        X.1.1.sum (fun _ n => n) := by
    dsimp [restAfterDouble]
    exact totalMult_sub_double_single (X := X.1.1) (gm := g) hg_two
  obtain ⟨g₂, hg₂_rest, hg₂min⟩ :=
    Mix2LambdaSection17.exists_min_rank_gene hrestAfterDouble_ne
  have hXg₂ : 0 < X.1.1 g₂ := by
    dsimp [restAfterDouble] at hg₂_rest
    exact lt_of_lt_of_le hg₂_rest (by omega)
  have hg₂_pol : g₂.type ≠ GeneType.NonPolarized :=
    IsPolarized_def'.mp hXpol g₂ (Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂))
  have hg₂_odd : Odd g₂.rank :=
    Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi X.1.2 hXg₂ hg₂_pol
  have hX_rank_ge_three_of_ne_g :
      ∀ h : Gene, 0 < X.1.1 h → h ≠ g → 3 ≤ h.rank := by
    intro h hXh hne_h_g
    have hmin_le := hgmin h hXh
    rw [hg_rank_one] at hmin_le
    have hpol : h.type ≠ GeneType.NonPolarized :=
      IsPolarized_def'.mp hXpol h (Finsupp.mem_support_iff.mpr (ne_of_gt hXh))
    have hodd : Odd h.rank :=
      Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi X.1.2 hXh hpol
    obtain ⟨nh, h_rank_raw⟩ := hodd
    by_contra hnot
    have h_rank_one : h.rank = 1 := by omega
    have hrank_eq : h.rank = g.rank := by omega
    cases hg_type : g.type with
    | NonPolarized => exact hg_pol hg_type
    | Positive =>
        cases hh_type : h.type with
        | NonPolarized => exact hpol hh_type
        | Positive =>
            exact hne_h_g (Gene.ext hrank_eq (by rw [hh_type, hg_type]))
        | Negative =>
            exact hno_pair ⟨g, h, hrank_eq.symm, hg_type, hh_type, hgX, hXh⟩
    | Negative =>
        cases hh_type : h.type with
        | NonPolarized => exact hpol hh_type
        | Positive =>
            exact hno_pair ⟨h, g, hrank_eq, hh_type, hg_type, hXh, hgX⟩
        | Negative =>
            exact hne_h_g (Gene.ext hrank_eq (by rw [hh_type, hg_type]))
  have hg₂min_X_ne_g :
      ∀ h : Gene, 0 < X.1.1 h → h ≠ g → g₂.rank ≤ h.rank := by
    intro h hXh hne_h_g
    have hrest_h : 0 < restAfterDouble h := by
      dsimp [restAfterDouble]
      simp [hne_h_g.symm, hXh]
    exact hg₂min h hrest_h
  have hg₂_same_extra : g₂ = g → 3 ≤ X.1.1 g := by
    intro hsame
    subst hsame
    dsimp [restAfterDouble] at hg₂_rest
    simp at hg₂_rest
    omega
  have hg₂_rank_ge_three_of_ne_g : g₂ ≠ g → 3 ≤ g₂.rank := by
    intro hne_g₂_g
    exact hX_rank_ge_three_of_ne_g g₂ hXg₂ hne_g₂_g
  have htype16_boundary :
      ∀ {q : ℕ} (gsingle : Gene),
        gsingle.type = -g.type →
        gsingle.rank = 2 * q + 1 →
        1 ≤ X.1.1 gsingle →
        (Y16 (Nat.zero_le q) hg_pol).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
              Finsupp.single gsingle 1) ≤ Y.1.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
    intro q gsingle hsingle_type hsingle_rank hsingle hZle
    have hne : g ≠ gsingle := by
      intro h
      have htype_eq : g.type = -g.type := by
        rwa [← h] at hsingle_type
      cases htype : g.type with
      | NonPolarized => exact hg_pol htype
      | Positive => simp [htype] at htype_eq
      | Negative => simp [htype] at htype_eq
    exact exists_mutation_le_type16_of_genes (ε := g.type)
      hg_pol (Nat.zero_le q) X Y g gsingle rfl hsingle_type
      (by simpa using hg_rank_one) hsingle_rank hg_two hsingle hne hZle
  have htype14_boundary :
      ∀ {q : ℕ} (gopp : Gene),
        gopp.type = -g.type →
        gopp.rank = 2 * q + 1 →
        2 ≤ X.1.1 gopp →
        (Y14 (Nat.zero_le q) hg_pol).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
              Finsupp.single gopp 1 - Finsupp.single gopp 1) ≤ Y.1.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
    intro q gopp hopp_type hopp_rank hopp hZle
    have hne : g ≠ gopp := by
      intro h
      have htype_eq : g.type = -g.type := by
        rwa [← h] at hopp_type
      cases htype : g.type with
      | NonPolarized => exact hg_pol htype
      | Positive => simp [htype] at htype_eq
      | Negative => simp [htype] at htype_eq
    exact exists_mutation_le_type14_of_genes (ε := g.type)
      hg_pol (Nat.zero_le q) X Y g gopp rfl hopp_type
      (by simpa using hg_rank_one) hopp_rank hg_two hopp hne hZle
  by_cases hsame : g₂ = g
  · have hg_extra : 3 ≤ X.1.1 g := hg₂_same_extra hsame
    -- Boundary subcase: after removing the two source copies of the minimal
    -- rank-one gene, the residue-minimal gene is again `g`.
    -- This is the formal `same-gene extra multiplicity` branch.
    sorry
  · have hg₂_rank_ge_three : 3 ≤ g₂.rank :=
      hg₂_rank_ge_three_of_ne_g hsame
    obtain ⟨n₂, hg₂_rank_raw⟩ := hg₂_odd
    have hn₂_pos : 0 < n₂ := by
      rw [hg₂_rank_raw] at hg₂_rank_ge_three
      omega
    let q₂ := n₂ - 1
    have hn₂_eq : n₂ = q₂ + 1 := by omega
    have hg₂_rank_q : g₂.rank = 2 * q₂ + 3 := by omega
    have hg₂min_X_tail :
        ∀ h : Gene, 0 < X.1.1 h → h ≠ g → g₂.rank ≤ h.rank :=
      hg₂min_X_ne_g
    by_cases hopp : g₂.type = -g.type
    · by_cases hg₂_two : 2 ≤ X.1.1 g₂
      · -- Type14 boundary candidate:
        -- `2g + 2g₂ → 2g(0) + 2g(q₂+2)`.
        have htail_after_double :
            ∀ h ∈ restAfterDouble.support, 2 * q₂ + 3 ≤ h.rank := by
          intro h hh
          have hhpos : 0 < restAfterDouble h :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
          have hle := hg₂min h hhpos
          rwa [hg₂_rank_q] at hle
        let restAfterType14 : Chromosome :=
          restAfterDouble - Finsupp.single g₂ 1 - Finsupp.single g₂ 1
        have hrestAfterType14_eq :
            restAfterType14 =
              X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
                Finsupp.single g₂ 1 - Finsupp.single g₂ 1 := by
          rfl
        have hg₂_rest_two : 2 ≤ restAfterDouble g₂ := by
          dsimp [restAfterDouble]
          have hne_g_g₂ : g ≠ g₂ := by
            intro h
            exact hsame h.symm
          simp [hne_g_g₂]
          exact hg₂_two
        have htail_after_type14 :
            ∀ h ∈ restAfterType14.support, 2 * q₂ + 3 ≤ h.rank := by
          intro h hh
          have hhpos : 0 < restAfterType14 h :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
          have hrest_pos : 0 < restAfterDouble h := by
            dsimp [restAfterType14] at hhpos
            exact lt_of_lt_of_le hhpos (by omega)
          exact htail_after_double h
            (Finsupp.mem_support_iff.mpr (ne_of_gt hrest_pos))
        have htype14_rest_total :
            restAfterType14.sum (fun _ n => n) + 4 =
              X.1.1.sum (fun _ n => n) := by
          have hdrop_last :
              restAfterType14.sum (fun _ n => n) + 2 =
                restAfterDouble.sum (fun _ n => n) := by
            dsimp [restAfterType14]
            exact totalMult_sub_double_single hg₂_rest_two
          omega
        have hcandidate :=
          htype14_boundary (q := q₂ + 1) g₂ hopp
            (by rw [hg₂_rank_q]; omega) hg₂_two
        exact hcandidate (by
          -- Remaining Type14 dominance boundary:
          -- `Y14 + (X - 2g - 2g₂) ≤ Y`.
          sorry)
      · have hg₂_one : X.1.1 g₂ = 1 := by omega
        -- Type16 boundary candidate:
        -- `2g + g₂ → 2g(0) + g(q₂+2)`.
        have htail_after_double :
            ∀ h ∈ restAfterDouble.support, 2 * q₂ + 3 ≤ h.rank := by
          intro h hh
          have hhpos : 0 < restAfterDouble h :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
          have hle := hg₂min h hhpos
          rwa [hg₂_rank_q] at hle
        let restAfterType16 : Chromosome :=
          restAfterDouble - Finsupp.single g₂ 1
        have hrestAfterType16_eq :
            restAfterType16 =
              X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
                Finsupp.single g₂ 1 := by
          rfl
        have hg₂_rest_one : restAfterDouble g₂ = 1 := by
          have hne_g_g₂ : g ≠ g₂ := by
            intro h
            exact hsame h.symm
          dsimp [restAfterDouble]
          simp [hne_g_g₂, hg₂_one]
        have htail_after_type16 :
            ∀ h ∈ restAfterType16.support, 2 * q₂ + 3 ≤ h.rank := by
          intro h hh
          have hhpos : 0 < restAfterType16 h :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
          have hrest_pos : 0 < restAfterDouble h := by
            dsimp [restAfterType16] at hhpos
            exact lt_of_lt_of_le hhpos (Nat.sub_le _ _)
          exact htail_after_double h
            (Finsupp.mem_support_iff.mpr (ne_of_gt hrest_pos))
        have htype16_rest_total :
            restAfterType16.sum (fun _ n => n) + 3 =
              X.1.1.sum (fun _ n => n) := by
          have hdrop_last :
              restAfterType16.sum (fun _ n => n) + 1 =
                restAfterDouble.sum (fun _ n => n) := by
            dsimp [restAfterType16]
            exact totalMult_sub_single_one hg₂_rest_one
          omega
        have hcandidate :=
          htype16_boundary (q := q₂ + 1) g₂ hopp
            (by rw [hg₂_rank_q]; omega) (by omega : 1 ≤ X.1.1 g₂)
        have hne_g_g₂ : g ≠ g₂ := by
          intro h
          exact hsame h.symm
        have hg_eq :
            Gene.ofRank 1 g.type = (Finsupp.single g 1 : Chromosome) := by
          have h := Gene.ofRank_eq_gene (g := g)
          rwa [hg_rank_one] at h
        have hg₂_eq :
            Gene.ofRank (2 * (q₂ + 1) + 1) (-g.type) =
              (Finsupp.single g₂ 1 : Chromosome) := by
          have h := Gene.ofRank_eq_gene (g := g₂)
          rw [hopp, hg₂_rank_q] at h
          convert h using 2 <;> omega
        have hX16val :
            (X16 (Nat.zero_le (q₂ + 1)) hg_pol).1 =
              Finsupp.single g 1 + Finsupp.single g 1 +
                Finsupp.single g₂ 1 := by
          rw [X16_eq, hg_eq, hg₂_eq]
        have hXeq_type16 :
            (X16 (Nat.zero_le (q₂ + 1)) hg_pol).1 + restAfterType16 =
              X.1.1 := by
          rw [hX16val]
          dsimp [restAfterType16, restAfterDouble]
          exact Mix2LambdaSection17.double_single_pair_add_rest
            hg_two (by omega : 1 ≤ X.1.1 g₂) hne_g_g₂
        have hgap_tail_pack :
            (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
              ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[j] X.1.1) ≤
                signature (Chromosome.prime^[j] Y.1.1)) ∧
            (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → Even j →
              (signature (Gene.ofRank 1 g.type) +
                    signature (Gene.ofRank 1 g.type)) +
                  signature (Chromosome.prime^[j] X.1.1) ≤
                signature (Chromosome.prime^[j] Y.1.1)) ∧
            (signature (Gene.ofRank 1 g.type) +
                  signature (Chromosome.prime^[2 * q₂ + 4] X.1.1) ≤
                signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)) :=
          type16_rank_one_double_tail_gap_pack X Y hXY hcommon h17_1
            hXpol hno_pair g g₂ hgX hgmin hg_pol hp hp0 hg_rank_one
            hXneg_zero hg_two hseed1 restAfterDouble restAfterType16
            hg₂_rest hg₂min hXg₂ hg₂_pol hsame hg₂_rank_q hopp hg₂_one
            htail_after_double hrestAfterType16_eq hg₂_rest_one
            htail_after_type16 htype16_rest_total
        have hgap_odd :
            ∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j →
              ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[j] X.1.1) ≤
                signature (Chromosome.prime^[j] Y.1.1) := by
          intro j hjlo hjhi hjodd
          by_cases hj1 : j = 1
          · subst j
            simpa using hgap1
          · exact hgap_tail_pack.1 j hjlo hjhi hjodd hj1
        have hgap_pack :
            (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j →
              ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[j] X.1.1) ≤
                signature (Chromosome.prime^[j] Y.1.1)) ∧
            (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → Even j →
              (signature (Gene.ofRank 1 g.type) +
                    signature (Gene.ofRank 1 g.type)) +
                  signature (Chromosome.prime^[j] X.1.1) ≤
                signature (Chromosome.prime^[j] Y.1.1)) ∧
            (signature (Gene.ofRank 1 g.type) +
                  signature (Chromosome.prime^[2 * q₂ + 4] X.1.1) ≤
                signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)) :=
          ⟨hgap_odd, hgap_tail_pack.2⟩
        have hZle16 :
            (Y16 (Nat.zero_le (q₂ + 1)) hg_pol).1 + restAfterType16 ≤
              Y.1.1 :=
          Mix2LambdaPi.type16_rank_one_target_add_rest_le_of_gaps hg_pol X Y hXY
            restAfterType16 hXeq_type16 hgap_pack.1 hgap_pack.2.1
            hgap_pack.2.2
        exact hcandidate (by
          simpa [hrestAfterType16_eq] using hZle16)
    · -- The residue-minimal later gene has the same sign as `g`; this branch
      -- must use the extra same-sign mass to find the next useful source.
      sorry

private lemma exists_mutation_le_no_pair_rank_one_singleton_second_double
    {m q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene)
    (hg_rank_one : g.rank = 1)
    (hg_one : X.1.1 g = 1)
    (hg₂min : ∀ g' : Gene,
      0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g' →
        g₂.rank ≤ g'.rank)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hg₂_two : 2 ≤ X.1.1 g₂) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 :=
  exists_mutation_le_second_double X Y hXY hcommon h17_1 hXpol hno_pair g g₂
    hg_one hg_rank_one hg₂min hg₂_pol hg₂_rank_q hseed1 hg₂_two

private lemma exists_mutation_le_no_pair_rank_one_singleton_later_distinct
    {m p q₂ q₃ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ g₃ : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_one : X.1.1 g = 1)
    (hg₂_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g₂)
    (hg₂min : ∀ g' : Gene,
      0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g' →
        g₂.rank ≤ g'.rank)
    (hXg₂ : 0 < X.1.1 g₂)
    (hne_g₂_g : g₂ ≠ g)
    (hne_g₂_neg : g₂ ≠ -g)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hg₂_one : X.1.1 g₂ = 1)
    (restAfterG₂ : Chromosome)
    (hrestAfterG₂ :
      restAfterG₂ = X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1)
    (hg₃_rest : 0 < restAfterG₂ g₃)
    (hg₃min : ∀ g' : Gene, 0 < restAfterG₂ g' → g₃.rank ≤ g'.rank)
    (hXg₃ : 0 < X.1.1 g₃)
    (hne_g₃_g : g₃ ≠ g)
    (hne_g₃_g₂ : g₃ ≠ g₂)
    (hg₃_pol : g₃.type ≠ GeneType.NonPolarized)
    (hg₂_le_g₃ : g₂.rank ≤ g₃.rank)
    (hg₃_rank_q : g₃.rank = 2 * q₃ + 3)
    (hq₂_le_q₃ : q₂ ≤ q₃) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, 2 * q₂ + 3 ≤ h.rank := by
    intro h hh
    have hhpos : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) h :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have hle := hg₂min h hhpos
    rwa [hg₂_rank_q] at hle
  have h3rd : ∀ h ∈ restAfterG₂.support, 2 * q₃ + 3 ≤ h.rank := by
    intro h hh
    have hhpos : 0 < restAfterG₂ h :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have hle := hg₃min h hhpos
    rwa [hg₃_rank_q] at hle
  have hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank := by
    have hx := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
    have hy := @signature_sum_eq_rank (Chromosome.prime^[1] Y.1.1)
    have : ((Chromosome.prime^[1] X.1.1).rank : ℚ) <
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
      rw [← hx, ← hy]; linarith [hseed1.1, hseed1.2]
    exact_mod_cast this
  have hgap_pred :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q₂ + 2] X.1.1) ≤
        signature (Gene.ofRank 1 g₂.type) +
          signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1) := by
    cases htype : g₂.type with
    | NonPolarized => exact absurd htype hg₂_pol
    | Positive =>
        refine type10_pred_gap_positive X Y hXY ?_
        have hw := case4_window_snd X Y hXY hr1 hseed1 hg_one h2nd
          (by omega) q₂ (by omega)
        simpa [Sigma.sigma, show 2 + 2 * q₂ = 2 * q₂ + 2 by omega] using hw
    | Negative =>
        refine type10_pred_gap_negative X Y hXY ?_
        have hw := case4_window_fst X Y hXY hr1 hseed1 hg_one h2nd
          (by omega) q₂ (by omega)
        simpa [Sigma.sigma, show 2 + 2 * q₂ = 2 * q₂ + 2 by omega] using hw
  have hq₂_ne_q₃ : q₂ ≠ q₃ := by
    intro hqeq
    have hrank_eq : g₂.rank = g₃.rank := by
      rw [hg₂_rank_q, hg₃_rank_q, hqeq]
    cases htype₂ : g₂.type with
    | NonPolarized => exact absurd htype₂ hg₂_pol
    | Positive =>
        cases htype₃ : g₃.type with
        | NonPolarized => exact absurd htype₃ hg₃_pol
        | Positive =>
            have heq : g₂ = g₃ := Gene.ext hrank_eq (by rw [htype₂, htype₃])
            exact hne_g₃_g₂ heq.symm
        | Negative =>
            exact absurd (hno_pair ⟨g₂, g₃, hrank_eq, htype₂, htype₃, hXg₂, hXg₃⟩)
              not_false
    | Negative =>
        cases htype₃ : g₃.type with
        | NonPolarized => exact absurd htype₃ hg₃_pol
        | Positive =>
            exact absurd (hno_pair ⟨g₃, g₂, hrank_eq.symm, htype₃, htype₂, hXg₃,
              hXg₂⟩) not_false
        | Negative =>
            have heq : g₂ = g₃ := Gene.ext hrank_eq (by rw [htype₂, htype₃])
            exact hne_g₃_g₂ heq.symm
  have hq₂_lt_q₃ : q₂ < q₃ := lt_of_le_of_ne hq₂_le_q₃ hq₂_ne_q₃
  have hgap_mid_lower :
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[2 * q₂ + 3] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 3] Y.1.1) := by
    refine type10_mid_gap_odd_of_Y_ne X Y h17_1
      (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by ring⟩) (by omega) ?_
    intro hYzero
    have hYrank : ∀ h : Gene, 0 < Y.1.1 h → h.rank ≤ 2 * q₂ + 3 := by
      intro h hh
      have hall :=
        (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := 2 * q₂ + 3)).2
          hYzero
      exact hall h (Finsupp.mem_support_iff.mpr (ne_of_gt hh))
    have hYpol_top : ∀ h : Gene, 0 < Y.1.1 h → h.rank = 2 * q₂ + 3 →
        h.type ≠ GeneType.NonPolarized := by
      intro h hh hhrank
      have hhodd : Odd h.rank := by rw [hhrank]; exact ⟨q₂ + 1, by ring⟩
      have hodd_part : 0 < Y.1.1.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]; exact hh
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
        (Finsupp.mem_support_iff.mpr hodd_part.ne')
    cases htype : g₂.type with
    | NonPolarized => exact absurd htype hg₂_pol
    | Positive =>
        have hno_pos : Y.1.1 ⟨2 * q₂ + 3, GeneType.Positive, by omega⟩ = 0 := by
          have htop_eq_g : (⟨2 * q₂ + 3, GeneType.Positive, by omega⟩ : Gene) = g₂ :=
            Gene.ext (by dsimp; rw [hg₂_rank_q]) htype.symm
          have hle := hcommon g₂ hXg₂
          rw [htop_eq_g]; omega
        have hYfst0 :=
          signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
            (W := Y.1.1) (p := q₂ + 1) hYpol_top hYrank hno_pos
        have hYfst0' : (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1 = 0 := by
          simpa [show 2 * (q₂ + 1) = 2 * q₂ + 2 by omega] using hYfst0
        have hXfst1 :=
          one_le_signature_prime_pred_fst_of_positive (X := X.1.1) (gpos := g₂) htype hXg₂
        have hXfst1' : 1 ≤ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 := by
          simpa [hg₂_rank_q, show 2 * q₂ + 3 - 1 = 2 * q₂ + 2 by omega] using hXfst1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).1
        linarith
    | Negative =>
        have hno_neg : Y.1.1 ⟨2 * q₂ + 3, GeneType.Negative, by omega⟩ = 0 := by
          have htop_eq_g : (⟨2 * q₂ + 3, GeneType.Negative, by omega⟩ : Gene) = g₂ :=
            Gene.ext (by dsimp; rw [hg₂_rank_q]) htype.symm
          have hle := hcommon g₂ hXg₂
          rw [htop_eq_g]; omega
        have hYsnd0 :=
          signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
            (W := Y.1.1) (p := q₂ + 1) hYpol_top hYrank hno_neg
        have hYsnd0' : (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2 = 0 := by
          simpa [show 2 * (q₂ + 1) = 2 * q₂ + 2 by omega] using hYsnd0
        have hXsnd1 :=
          one_le_signature_prime_pred_snd_of_negative (X := X.1.1) (gneg := g₂) htype hXg₂
        have hXsnd1' : 1 ≤ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 := by
          simpa [hg₂_rank_q, show 2 * q₂ + 3 - 1 = 2 * q₂ + 2 by omega] using hXsnd1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).2
        linarith
  have hg₂_rest_one_mid : (X.1.1 - Finsupp.single g 1 : Chromosome) g₂ = 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne_g₂_g.symm]
    exact hg₂_one
  have hrest_sum_mid :
      restAfterG₂.sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 2 := by
    rw [hrestAfterG₂]
    exact totalMult_sub_two_single_one_cast hg_one hg₂_rest_one_mid
  have hD_mid := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
  have htail_sigma_eq : ∀ i, 2 * q₂ + 3 ≤ i →
      Sigma.sigma X.1.1 i = Sigma.sigma restAfterG₂ i := by
    intro i hi
    have hprime :
        Chromosome.prime^[i] X.1.1 = Chromosome.prime^[i] restAfterG₂ := by
      rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by rw [hg_rank_one]; omega)]
      rw [prime_iterate_eq_sub_single_of_rank_le
        (X := (X.1.1 - Finsupp.single g 1 : Chromosome)) (gm := g₂)
        hg₂_rest_one_mid (by rw [hg₂_rank_q]; omega)]
      rw [← hrestAfterG₂]
    simp [Sigma.sigma, hprime]
  have hXtail_drop_fst :
      ∀ i, 2 * q₂ + 3 ≤ i → i + 2 ≤ 2 * q₃ + 3 →
        (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro i hi hi2
    have hsig_i := htail_sigma_eq i hi
    have hsig_i2 := htail_sigma_eq (i + 2) (by omega)
    have h2 : ∀ h ∈ restAfterG₂.support, i + 2 ≤ h.rank := by
      intro h hh
      have hle := h3rd h hh
      omega
    have hdrop := MixLambdaPi.twostep h2
    have hfst_i := congrArg Prod.fst hsig_i
    have hfst_i2 := congrArg Prod.fst hsig_i2
    rw [hfst_i, hfst_i2, hdrop, hrest_sum_mid, hD_mid]
  have hXtail_drop_snd :
      ∀ i, 2 * q₂ + 3 ≤ i → i + 2 ≤ 2 * q₃ + 3 →
        (Sigma.sigma X.1.1 i).2 - (Sigma.sigma X.1.1 (i + 2)).2 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro i hi hi2
    have hsig_i := htail_sigma_eq i hi
    have hsig_i2 := htail_sigma_eq (i + 2) (by omega)
    have h2 : ∀ h ∈ restAfterG₂.support, i + 2 ≤ h.rank := by
      intro h hh
      have hle := h3rd h hh
      omega
    have hdrop := MixLambdaPi.twostep_snd h2
    have hsnd_i := congrArg Prod.snd hsig_i
    have hsnd_i2 := congrArg Prod.snd hsig_i2
    rw [hsnd_i, hsnd_i2, hdrop, hrest_sum_mid, hD_mid]
  have hYdrop_fst_strong_even :
      ∀ i, Even i →
        (Sigma.sigma Y.1.1 i).1 - (Sigma.sigma Y.1.1 (i + 2)).1 ≤
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro i hi
    exact case4_Ydrop_fst_strong_even X Y hseed1 hi
  have hYdrop_snd_strong_even :
      ∀ i, Even i →
        (Sigma.sigma Y.1.1 i).2 - (Sigma.sigma Y.1.1 (i + 2)).2 ≤
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro i hi
    exact case4_Ydrop_snd_strong_even X Y hseed1 hi
  have hgap_mid_non_top_odd :
      ∀ j, 2 * q₂ + 3 ≤ j → j ≤ 2 * q₃ + 3 → ¬ Even j →
        j ≠ 2 * q₃ + 3 →
          ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hodd hjtop
    exact type10_mid_gap_odd_of_Y_ne X Y h17_1 hodd (by omega) (by
      have hjlt : j < 2 * q₃ + 3 := by omega
      have hXj_ne : Chromosome.prime^[j] X.1.1 ≠ 0 := by
        intro hzero
        have hall :=
          (Chromosome.prime_iterate_eq_zero_rank_le (X := X.1.1) (k := j)).2
            hzero
        have hg₃_support : g₃ ∈ X.1.1.support :=
          Finsupp.mem_support_iff.mpr (ne_of_gt hXg₃)
        have hle_g₃ := hall g₃ hg₃_support
        rw [hg₃_rank_q] at hle_g₃
        omega
      intro hYzero
      have hle := le_iff_dominates.mp hXY.le j
      rw [hYzero, map_zero] at hle
      exact hXj_ne
        (signature_eq_zero (le_antisymm hle (signature_nonneg _))))
  have hW₂top : ∀ z ∈ (Chromosome.prime^[2 * q₂ + 1] X.1.1).support,
      2 ≤ z.rank ∧ (z.rank = 2 → z.type = g₂.type) := by
    intro z hz
    have hzpos : 0 < (Chromosome.prime^[2 * q₂ + 1] X.1.1) z :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
    let z0 : Gene :=
      ⟨z.rank + (2 * q₂ + 1), z.type,
        Nat.le_add_right_of_le z.rank_pos⟩
    have hz0X : 0 < X.1.1 z0 := by
      have hcoeff := prime_iterate_coeff (2 * q₂ + 1) X.1.1 z
      change (Chromosome.prime^[2 * q₂ + 1] X.1.1) z = X.1.1 z0 at hcoeff
      rwa [← hcoeff]
    have hz0_ne_g : z0 ≠ g := by
      intro hzg
      have hrank := congrArg Gene.rank hzg
      dsimp [z0] at hrank
      rw [hg_rank_one] at hrank
      have zpos := z.rank_pos
      omega
    have hz0_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) z0 := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hz0_ne_g.symm]
      exact hz0X
    have hz0_rank_le := h2nd z0 (Finsupp.mem_support_iff.mpr (ne_of_gt hz0_rest))
    constructor
    · dsimp [z0] at hz0_rank_le
      omega
    · intro hz_rank
      have hz0_support : z0 ∈ X.1.1.support :=
        Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
      have hz0_rank_eq : z0.rank = g₂.rank := by
        dsimp [z0]
        rw [hz_rank, hg₂_rank_q]
        omega
      cases hz_type : z.type with
      | NonPolarized =>
          have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
          exact False.elim (hpol0 (by simpa [z0] using hz_type))
      | Positive =>
          cases htype₂ : g₂.type with
          | NonPolarized => exact False.elim (hg₂_pol htype₂)
          | Positive => rfl
          | Negative =>
              exact False.elim (hno_pair ⟨z0, g₂, hz0_rank_eq,
                by simpa [z0] using hz_type, htype₂, hz0X, hXg₂⟩)
      | Negative =>
          cases htype₂ : g₂.type with
          | NonPolarized => exact False.elim (hg₂_pol htype₂)
          | Positive =>
              exact False.elim (hno_pair ⟨g₂, z0, hz0_rank_eq.symm, htype₂,
                by simpa [z0] using hz_type, hXg₂, hz0X⟩)
          | Negative => rfl
  have hW₂sum_nat :
      (Chromosome.prime^[2 * q₂ + 1] X.1.1).sum (fun _ n => n) =
        (X.1.1 - Finsupp.single g 1 : Chromosome).sum (fun _ n => n) := by
    rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by omega)]
    exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
      (X.1.1 - Finsupp.single g 1 : Chromosome) (2 * q₂ + 1) (by
        intro h hh
        have hle := h2nd h hh
        omega)
  have hW₂sumD1 :
      (Chromosome.prime^[2 * q₂ + 1] X.1.1).sum (fun _ n => (n : ℚ)) =
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
    have hW₂sum : (Chromosome.prime^[2 * q₂ + 1] X.1.1).sum (fun _ n => (n : ℚ)) =
        (X.1.1 - Finsupp.single g 1 : Chromosome).sum (fun _ n => (n : ℚ)) :=
      totalMult_cast_eq_of_nat_eq hW₂sum_nat
    have hrest1 : (X.1.1 - Finsupp.single g 1 : Chromosome).sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 1 :=
      totalMult_sub_single_one_cast hg_one
    rw [hW₂sum, hrest1, hD_mid]
  have hbase_g₂_match_fst :
      g₂.type = GeneType.Positive →
        (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).1 := by
    intro htype₂
    have hWpos : ∀ z ∈ (Chromosome.prime^[2 * q₂ + 1] X.1.1).support,
        2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
      intro z hz
      exact ⟨(hW₂top z hz).1, by intro hzrank; rw [(hW₂top z hz).2 hzrank, htype₂]⟩
    have hXdrop_raw :=
      edge_drop_fst_eq_totalMult_positive_iterate
        (W := X.1.1) (i := 2 * q₂ + 1) hWpos
    have hXdrop :
        (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 -
            (Sigma.sigma X.1.1 (2 * q₂ + 4)).1 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
      rw [show 1 + (2 * q₂ + 1) = 2 * q₂ + 2 by omega,
        show 3 + (2 * q₂ + 1) = 2 * q₂ + 4 by omega] at hXdrop_raw
      rw [hXdrop_raw, hW₂sumD1]
    have hYdrop := hYdrop_fst_strong_even (2 * q₂ + 2) ⟨q₂ + 1, by ring⟩
    have hYdrop' :
        (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 -
            (Sigma.sigma Y.1.1 (2 * q₂ + 4)).1 ≤
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
      simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hYdrop
    have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).1
    have hdom' : (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 ≤
        (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 := by
      simpa [Sigma.sigma] using hdom
    simpa [Sigma.sigma] using (by
      linarith : (Sigma.sigma X.1.1 (2 * q₂ + 4)).1 <
        (Sigma.sigma Y.1.1 (2 * q₂ + 4)).1)
  have hbase_g₂_match_snd :
      g₂.type = GeneType.Negative →
        (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).2 := by
    intro htype₂
    have hWneg : ∀ z ∈ (Chromosome.prime^[2 * q₂ + 1] X.1.1).support,
        2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
      intro z hz
      exact ⟨(hW₂top z hz).1, by intro hzrank; rw [(hW₂top z hz).2 hzrank, htype₂]⟩
    have hXdrop_raw :=
      edge_drop_snd_eq_totalMult_negative_iterate
        (W := X.1.1) (i := 2 * q₂ + 1) hWneg
    have hXdrop :
        (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 -
            (Sigma.sigma X.1.1 (2 * q₂ + 4)).2 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
      rw [show 1 + (2 * q₂ + 1) = 2 * q₂ + 2 by omega,
        show 3 + (2 * q₂ + 1) = 2 * q₂ + 4 by omega] at hXdrop_raw
      rw [hXdrop_raw, hW₂sumD1]
    have hYdrop := hYdrop_snd_strong_even (2 * q₂ + 2) ⟨q₂ + 1, by ring⟩
    have hYdrop' :
        (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 -
            (Sigma.sigma Y.1.1 (2 * q₂ + 4)).2 ≤
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
      simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hYdrop
    have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).2
    have hdom' : (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 ≤
        (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 := by
      simpa [Sigma.sigma] using hdom
    simpa [Sigma.sigma] using (by
      linarith : (Sigma.sigma X.1.1 (2 * q₂ + 4)).2 <
        (Sigma.sigma Y.1.1 (2 * q₂ + 4)).2)
  have htail_decomp :
      restAfterG₂ + Finsupp.single g₂ 1 =
        (X.1.1 - Finsupp.single g 1 : Chromosome) := by
    rw [hrestAfterG₂]
    exact sub_single_add_single_eq (by rw [hg₂_rest_one_mid]; norm_num)
  have hsig_pred_decomp :
      Sigma.sigma X.1.1 (2 * q₂ + 2) =
        Sigma.sigma restAfterG₂ (2 * q₂ + 2) +
          signature (Gene.ofRank 1 g₂.type) := by
    have hprime :
        Chromosome.prime^[2 * q₂ + 2] X.1.1 =
          Chromosome.prime^[2 * q₂ + 2] restAfterG₂ +
            Gene.ofRank 1 g₂.type := by
      rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by rw [hg_rank_one]; omega)]
      conv_lhs => rw [← htail_decomp]
      rw [iterate_map_add]
      have hsingle :
          Chromosome.prime^[2 * q₂ + 2] (Finsupp.single g₂ 1 : Chromosome) =
            Gene.ofRank 1 g₂.type := by
        rw [← Gene.ofRank_eq_gene (g := g₂), prime_iterate_ofRank, hg₂_rank_q,
          show 2 * q₂ + 3 - (2 * q₂ + 2) = 1 by omega]
      rw [hsingle]
    simp [Sigma.sigma, hprime]
  have hXedge_g₂_nonmatch_snd :
      g₂.type = GeneType.Positive →
        (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 -
            (Sigma.sigma X.1.1 (2 * q₂ + 4)).2 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro htype₂
    have hpred := congrArg Prod.snd hsig_pred_decomp
    have hsucc := congrArg Prod.snd (htail_sigma_eq (2 * q₂ + 4) (by omega))
    have h2 : ∀ h ∈ restAfterG₂.support, 2 * q₂ + 4 ≤ h.rank := by
      intro h hh
      have hle := h3rd h hh
      omega
    have hdrop := MixLambdaPi.twostep_snd (W := restAfterG₂) (i := 2 * q₂ + 2) h2
    have hdrop' :
        (Sigma.sigma restAfterG₂ (2 * q₂ + 2)).2 -
            (Sigma.sigma restAfterG₂ (2 * q₂ + 4)).2 =
          restAfterG₂.sum (fun _ n => (n : ℚ)) := by
      simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hdrop
    simp [htype₂, signature_ofRank_one_positive] at hpred
    rw [hpred, hsucc, hdrop', hrest_sum_mid, hD_mid]
  have hXedge_g₂_nonmatch_fst :
      g₂.type = GeneType.Negative →
        (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 -
            (Sigma.sigma X.1.1 (2 * q₂ + 4)).1 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro htype₂
    have hpred := congrArg Prod.fst hsig_pred_decomp
    have hsucc := congrArg Prod.fst (htail_sigma_eq (2 * q₂ + 4) (by omega))
    have h2 : ∀ h ∈ restAfterG₂.support, 2 * q₂ + 4 ≤ h.rank := by
      intro h hh
      have hle := h3rd h hh
      omega
    have hdrop := MixLambdaPi.twostep (W := restAfterG₂) (i := 2 * q₂ + 2) h2
    have hdrop' :
        (Sigma.sigma restAfterG₂ (2 * q₂ + 2)).1 -
            (Sigma.sigma restAfterG₂ (2 * q₂ + 4)).1 =
          restAfterG₂.sum (fun _ n => (n : ℚ)) := by
      simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hdrop
    simp [htype₂, signature_ofRank_one_negative] at hpred
    rw [hpred, hsucc, hdrop', hrest_sum_mid, hD_mid]
  have hbase_g₂_nonmatch_snd :
      g₂.type = GeneType.Positive →
        (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).2 := by
    intro htype₂
    have hpred_strict :
        (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 <
          (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 := by
      have h := hgap_pred.2
      rw [htype₂] at h
      have h' : 1 + (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 ≤
          (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 := by
        simpa [Sigma.sigma, signature_ofRank_one_positive] using h
      linarith
    have hXdrop := hXedge_g₂_nonmatch_snd htype₂
    have hYdrop := hYdrop_snd_strong_even (2 * q₂ + 2) ⟨q₂ + 1, by ring⟩
    have hYdrop' :
        (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 -
            (Sigma.sigma Y.1.1 (2 * q₂ + 4)).2 ≤
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
      simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hYdrop
    simpa [Sigma.sigma] using (by
      linarith : (Sigma.sigma X.1.1 (2 * q₂ + 4)).2 <
        (Sigma.sigma Y.1.1 (2 * q₂ + 4)).2)
  have hbase_g₂_nonmatch_fst :
      g₂.type = GeneType.Negative →
        (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).1 := by
    intro htype₂
    have hpred_strict :
        (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 <
          (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 := by
      have h := hgap_pred.1
      rw [htype₂] at h
      have h' : 1 + (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 ≤
          (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 := by
        simpa [Sigma.sigma, signature_ofRank_one_negative] using h
      linarith
    have hXdrop := hXedge_g₂_nonmatch_fst htype₂
    have hYdrop := hYdrop_fst_strong_even (2 * q₂ + 2) ⟨q₂ + 1, by ring⟩
    have hYdrop' :
        (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 -
            (Sigma.sigma Y.1.1 (2 * q₂ + 4)).1 ≤
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
      simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hYdrop
    simpa [Sigma.sigma] using (by
      linarith : (Sigma.sigma X.1.1 (2 * q₂ + 4)).1 <
        (Sigma.sigma Y.1.1 (2 * q₂ + 4)).1)
  have hbase_even_fst :
      (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).1 := by
    cases htype₂ : g₂.type with
    | NonPolarized => exact False.elim (hg₂_pol htype₂)
    | Positive => exact hbase_g₂_match_fst htype₂
    | Negative => exact hbase_g₂_nonmatch_fst htype₂
  have hbase_even_snd :
      (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).2 := by
    cases htype₂ : g₂.type with
    | NonPolarized => exact False.elim (hg₂_pol htype₂)
    | Positive => exact hbase_g₂_nonmatch_snd htype₂
    | Negative => exact hbase_g₂_match_snd htype₂
  let dmid := q₃ - q₂ - 1
  have hwin_mid : 2 * q₂ + 4 + 2 * dmid ≤ 2 * q₃ + 3 := by
    dsimp [dmid]
    omega
  have hfst_window_mid :
      ∀ t, t ≤ dmid →
        (signature (Chromosome.prime^[2 * q₂ + 4 + 2 * t] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * q₂ + 4 + 2 * t] Y.1.1)).1 := by
    apply Mix2LambdaSection17.fst_propagate_window_lt
      (X := X.1.1) (Y := Y.1.1) (j0 := 2 * q₂ + 4) (d := dmid)
      hbase_even_fst
    intro t ht
    have heven : Even (2 * q₂ + 4 + 2 * t) := ⟨q₂ + 2 + t, by ring⟩
    have hYdrop := hYdrop_fst_strong_even (2 * q₂ + 4 + 2 * t) heven
    have hXdrop := hXtail_drop_fst (2 * q₂ + 4 + 2 * t) (by omega) (by
      dsimp [dmid] at ht ⊢
      omega)
    simp only [Sigma.sigma] at hYdrop hXdrop ⊢
    linarith
  have hsnd_window_mid :
      ∀ t, t ≤ dmid →
        (signature (Chromosome.prime^[2 * q₂ + 4 + 2 * t] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * q₂ + 4 + 2 * t] Y.1.1)).2 := by
    apply Mix2LambdaSection17.snd_propagate_window_lt
      (X := X.1.1) (Y := Y.1.1) (j0 := 2 * q₂ + 4) (d := dmid)
      hbase_even_snd
    intro t ht
    have heven : Even (2 * q₂ + 4 + 2 * t) := ⟨q₂ + 2 + t, by ring⟩
    have hYdrop := hYdrop_snd_strong_even (2 * q₂ + 4 + 2 * t) heven
    have hXdrop := hXtail_drop_snd (2 * q₂ + 4 + 2 * t) (by omega) (by
      dsimp [dmid] at ht ⊢
      omega)
    simp only [Sigma.sigma] at hYdrop hXdrop ⊢
    linarith
  have hgap_mid_even :
      ∀ j, 2 * q₂ + 3 ≤ j → j ≤ 2 * q₃ + 3 → Even j →
        ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hjeven
    rcases hjeven with ⟨u, hu⟩
    let t := u - (q₂ + 2)
    have hj_eq : j = 2 * q₂ + 4 + 2 * t := by
      rw [hu]
      dsimp [t]
      omega
    have ht_le : t ≤ dmid := by
      rw [hu] at hjhi
      dsimp [t, dmid]
      omega
    exact Mix2LambdaSection17.one_one_le_of_both_lt X.1.2 Y.1.2
      (by simpa [hj_eq] using hfst_window_mid t ht_le)
      (by simpa [hj_eq] using hsnd_window_mid t ht_le)
  have hgap_mid : ∀ j, 2 * q₂ + 3 ≤ j → j ≤ 2 * q₃ + 3 →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi
    by_cases hjlower : j = 2 * q₂ + 3
    · subst j
      exact hgap_mid_lower
    · by_cases hjeven : Even j
      · exact hgap_mid_even j hjlo hjhi hjeven
      · by_cases hjtop : j = 2 * q₃ + 3
        · subst j
          exact type10_mid_gap_odd_of_Y_ne X Y h17_1 hjeven (by omega) (by
            intro hYzero
            have hgap_even_top :=
              hgap_mid_even (2 * q₃ + 2) (by omega) (by omega) ⟨q₃ + 1, by ring⟩
            have hYtop_rank_le :
                (Chromosome.prime^[2 * q₃ + 2] Y.1.1).rank ≤
                  Y.1.1.rank - Y.1.1.prime.rank := by
              have hdrop :=
                Mix2LambdaSection17.rank_prime_iterate_drop_le_zero
                  Y.1.1 (2 * q₃ + 2)
              simpa [show 2 * q₃ + 2 + 1 = 2 * q₃ + 3 by omega,
                hYzero] using hdrop
            have hrank_top_gap :
                (Chromosome.prime^[2 * q₃ + 2] X.1.1).rank + 2 ≤
                  (Chromosome.prime^[2 * q₃ + 2] Y.1.1).rank := by
              have hsumX :
                  (signature (Chromosome.prime^[2 * q₃ + 2] X.1.1)).1 +
                      (signature (Chromosome.prime^[2 * q₃ + 2] X.1.1)).2 =
                    ((Chromosome.prime^[2 * q₃ + 2] X.1.1).rank : ℚ) :=
                signature_sum_eq_rank
              have hsumY :
                  (signature (Chromosome.prime^[2 * q₃ + 2] Y.1.1)).1 +
                      (signature (Chromosome.prime^[2 * q₃ + 2] Y.1.1)).2 =
                    ((Chromosome.prime^[2 * q₃ + 2] Y.1.1).rank : ℚ) :=
                signature_sum_eq_rank
              have hfst := hgap_even_top.1
              have hsnd := hgap_even_top.2
              simp only [Prod.fst_add, Prod.snd_add] at hfst hsnd
              have hq :
                  ((Chromosome.prime^[2 * q₃ + 2] X.1.1).rank : ℚ) + 2 ≤
                    ((Chromosome.prime^[2 * q₃ + 2] Y.1.1).rank : ℚ) := by
                linarith
              exact_mod_cast hq
            have hXtop_eq_rest :
                Chromosome.prime^[2 * q₃ + 2] X.1.1 =
                  Chromosome.prime^[2 * q₃ + 2] restAfterG₂ := by
              rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by
                rw [hg_rank_one]
                omega)]
              rw [prime_iterate_eq_sub_single_of_rank_le
                (X := (X.1.1 - Finsupp.single g 1 : Chromosome)) (gm := g₂)
                hg₂_rest_one_mid (by
                  rw [hg₂_rank_q]
                  omega)]
              rw [← hrestAfterG₂]
            have hrest_total_survives :
                (Chromosome.prime^[2 * q₃ + 2] restAfterG₂).sum (fun _ n => n) =
                  restAfterG₂.sum (fun _ n => n) :=
              Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
                restAfterG₂ (2 * q₃ + 2) (by
                  intro h hh
                  have hle := h3rd h hh
                  omega)
            have hXtop_total :
                (Chromosome.prime^[2 * q₃ + 2] X.1.1).sum (fun _ n => n) =
                  X.1.1.sum (fun _ n => n) - 2 := by
              rw [hXtop_eq_rest, hrest_total_survives]
              have hrest_nat : restAfterG₂.sum (fun _ n => n) + 2 =
                  X.1.1.sum (fun _ n => n) := by
                rw [hrestAfterG₂]
                exact totalMult_sub_two_single_one hg_one hg₂_rest_one_mid
              omega
            have hXtop_rank_ge :
                X.1.1.sum (fun _ n => n) - 2 ≤
                  (Chromosome.prime^[2 * q₃ + 2] X.1.1).rank := by
              have hle :=
                totalMult_le_rank (Chromosome.prime^[2 * q₃ + 2] X.1.1)
              rwa [hXtop_total] at hle
            have hXtotal_eq_drop :
                X.1.1.sum (fun _ n => n) =
                  X.1.1.rank - X.1.1.prime.rank := by
              have h := Mix2LambdaSection17.rank_eq_prime_rank_add_totalMult X.1.1
              omega
            have hr1' : X.1.1.prime.rank < Y.1.1.prime.rank := by
              simpa [Function.iterate_one] using hr1
            have hrank_eq : X.1.1.rank = Y.1.1.rank := by
              rw [X.2, Y.2]
            have hdrop_gap :
                Y.1.1.rank - Y.1.1.prime.rank + 1 ≤
                  X.1.1.rank - X.1.1.prime.rank := by
              omega
            omega)
        · exact hgap_mid_non_top_odd j hjlo hjhi hjeven hjtop
  have hWtop : ∀ z ∈ (Chromosome.prime^[2 * q₃ + 1] X.1.1).support,
      2 ≤ z.rank ∧ (z.rank = 2 → z.type = g₃.type) := by
    intro z hz
    have hzpos : 0 < (Chromosome.prime^[2 * q₃ + 1] X.1.1) z :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
    let z0 : Gene :=
      ⟨z.rank + (2 * q₃ + 1), z.type,
        Nat.le_add_right_of_le z.rank_pos⟩
    have hz0X : 0 < X.1.1 z0 := by
      have hcoeff := prime_iterate_coeff (2 * q₃ + 1) X.1.1 z
      change (Chromosome.prime^[2 * q₃ + 1] X.1.1) z = X.1.1 z0 at hcoeff
      rwa [← hcoeff]
    have hz0_ne_g : z0 ≠ g := by
      intro hzg
      have hrank := congrArg Gene.rank hzg
      dsimp [z0] at hrank
      rw [hg_rank_one] at hrank
      have zpos := z.rank_pos
      omega
    have hz0_ne_g₂ : z0 ≠ g₂ := by
      intro hzg
      have hrank := congrArg Gene.rank hzg
      dsimp [z0] at hrank
      rw [hg₂_rank_q] at hrank
      have zpos := z.rank_pos
      omega
    have hz0_rest : 0 < restAfterG₂ z0 := by
      rw [hrestAfterG₂]
      simp [hz0_ne_g.symm, hz0_ne_g₂.symm, hz0X]
    have hz0_rank_le := h3rd z0 (Finsupp.mem_support_iff.mpr (ne_of_gt hz0_rest))
    constructor
    · dsimp [z0] at hz0_rank_le
      omega
    · intro hz_rank
      have hz0_support : z0 ∈ X.1.1.support :=
        Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
      have hz0_rank_eq : z0.rank = g₃.rank := by
        dsimp [z0]
        rw [hz_rank, hg₃_rank_q]
        omega
      cases hz_type : z.type with
      | NonPolarized =>
          have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
          exact False.elim (hpol0 (by simpa [z0] using hz_type))
      | Positive =>
          cases htype₃ : g₃.type with
          | NonPolarized => exact False.elim (hg₃_pol htype₃)
          | Positive => rfl
          | Negative =>
              exact False.elim (hno_pair ⟨z0, g₃, hz0_rank_eq,
                by simpa [z0] using hz_type, htype₃, hz0X, hXg₃⟩)
      | Negative =>
          cases htype₃ : g₃.type with
          | NonPolarized => exact False.elim (hg₃_pol htype₃)
          | Positive =>
              exact False.elim (hno_pair ⟨g₃, z0, hz0_rank_eq.symm, htype₃,
                by simpa [z0] using hz_type, hXg₃, hz0X⟩)
          | Negative => rfl
  have hg₂_rest_one : (X.1.1 - Finsupp.single g 1 : Chromosome) g₂ = 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne_g₂_g.symm]
    exact hg₂_one
  have hWsum_nat :
      (Chromosome.prime^[2 * q₃ + 1] X.1.1).sum (fun _ n => n) =
        restAfterG₂.sum (fun _ n => n) := by
    rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by omega)]
    rw [prime_iterate_eq_sub_single_of_rank_le
      (X := (X.1.1 - Finsupp.single g 1 : Chromosome)) (gm := g₂)
      hg₂_rest_one (by rw [hg₂_rank_q]; omega)]
    rw [← hrestAfterG₂]
    exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
      restAfterG₂ (2 * q₃ + 1) (by
        intro h hh
        have hle := h3rd h hh
        omega)
  have hWsum := totalMult_cast_eq_of_nat_eq hWsum_nat
  have hrest_sum :
      restAfterG₂.sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 2 := by
    rw [hrestAfterG₂]
    exact totalMult_sub_two_single_one_cast hg_one hg₂_rest_one
  have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
  have hWsumD :
      (Chromosome.prime^[2 * q₃ + 1] X.1.1).sum (fun _ n => (n : ℚ)) =
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    rw [hWsum, hrest_sum, hD]
  have htop_gap :=
    hgap_mid (2 * q₃ + 2) (by omega) (by omega)
  have htop_fst :
      (signature (Chromosome.prime^[2 * q₃ + 2] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q₃ + 2] Y.1.1)).1 := by
    have h := htop_gap.1
    simp only [Prod.fst_add] at h
    linarith
  have htop_snd :
      (signature (Chromosome.prime^[2 * q₃ + 2] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q₃ + 2] Y.1.1)).2 := by
    have h := htop_gap.2
    simp only [Prod.snd_add] at h
    linarith
  have hYdrop_fst_strong :
      (Sigma.sigma Y.1.1 (2 * q₃ + 2)).1 - (Sigma.sigma Y.1.1 (2 * q₃ + 4)).1 ≤
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    simpa [show 2 * q₃ + 2 + 2 = 2 * q₃ + 4 by omega] using
      case4_Ydrop_fst_strong_even X Y hseed1 ⟨q₃ + 1, by ring⟩
  have hYdrop_snd_strong :
      (Sigma.sigma Y.1.1 (2 * q₃ + 2)).2 - (Sigma.sigma Y.1.1 (2 * q₃ + 4)).2 ≤
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    simpa [show 2 * q₃ + 2 + 2 = 2 * q₃ + 4 by omega] using
      case4_Ydrop_snd_strong_even X Y hseed1 ⟨q₃ + 1, by ring⟩
  have hgap_succ :
      signature (Gene.ofRank 1 g₃.type) +
          signature (Chromosome.prime^[2 * q₃ + 4] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₃ + 4] Y.1.1) := by
    cases htype : g₃.type with
    | NonPolarized => exact absurd htype hg₃_pol
    | Positive =>
        have hWpos : ∀ z ∈ (Chromosome.prime^[2 * q₃ + 1] X.1.1).support,
            2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
          intro z hz
          exact ⟨(hWtop z hz).1, by intro hzrank; rw [(hWtop z hz).2 hzrank, htype]⟩
        have hXdrop_raw :=
          edge_drop_fst_eq_totalMult_positive_iterate
            (W := X.1.1) (i := 2 * q₃ + 1) hWpos
        have hXdrop :
            (Sigma.sigma X.1.1 (2 * q₃ + 2)).1 -
                (Sigma.sigma X.1.1 (2 * q₃ + 4)).1 =
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
          rw [show 1 + (2 * q₃ + 1) = 2 * q₃ + 2 by omega,
            show 3 + (2 * q₃ + 1) = 2 * q₃ + 4 by omega] at hXdrop_raw
          rw [hXdrop_raw, hWsumD]
        have hsucc :
            (signature (Chromosome.prime^[2 * q₃ + 4] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * q₃ + 4] Y.1.1)).1 := by
          have htop :
              (Sigma.sigma X.1.1 (2 * q₃ + 2)).1 <
                (Sigma.sigma Y.1.1 (2 * q₃ + 2)).1 := by
            simpa [Sigma.sigma] using htop_fst
          simpa [Sigma.sigma] using (by
            linarith : (Sigma.sigma X.1.1 (2 * q₃ + 4)).1 <
              (Sigma.sigma Y.1.1 (2 * q₃ + 4)).1)
        simpa [htype, show 2 * (q₃ + 1) + 2 = 2 * q₃ + 4 by omega] using
          type16_succ_gap_positive X Y hXY (p := q₃ + 1)
            (by simpa [show 2 * (q₃ + 1) + 2 = 2 * q₃ + 4 by omega] using hsucc)
    | Negative =>
        have hWneg : ∀ z ∈ (Chromosome.prime^[2 * q₃ + 1] X.1.1).support,
            2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
          intro z hz
          exact ⟨(hWtop z hz).1, by intro hzrank; rw [(hWtop z hz).2 hzrank, htype]⟩
        have hXdrop_raw :=
          edge_drop_snd_eq_totalMult_negative_iterate
            (W := X.1.1) (i := 2 * q₃ + 1) hWneg
        have hXdrop :
            (Sigma.sigma X.1.1 (2 * q₃ + 2)).2 -
                (Sigma.sigma X.1.1 (2 * q₃ + 4)).2 =
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
          rw [show 1 + (2 * q₃ + 1) = 2 * q₃ + 2 by omega,
            show 3 + (2 * q₃ + 1) = 2 * q₃ + 4 by omega] at hXdrop_raw
          rw [hXdrop_raw, hWsumD]
        have hsucc :
            (signature (Chromosome.prime^[2 * q₃ + 4] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * q₃ + 4] Y.1.1)).2 := by
          have htop :
              (Sigma.sigma X.1.1 (2 * q₃ + 2)).2 <
                (Sigma.sigma Y.1.1 (2 * q₃ + 2)).2 := by
            simpa [Sigma.sigma] using htop_snd
          simpa [Sigma.sigma] using (by
            linarith : (Sigma.sigma X.1.1 (2 * q₃ + 4)).2 <
              (Sigma.sigma Y.1.1 (2 * q₃ + 4)).2)
        simpa [htype, show 2 * (q₃ + 1) + 2 = 2 * q₃ + 4 by omega] using
          type16_succ_gap_negative X Y hXY (p := q₃ + 1)
            (by simpa [show 2 * (q₃ + 1) + 2 = 2 * q₃ + 4 by omega] using hsucc)
  have hZle :
      (Y10 hq₂_le_q₃ hg₂_pol hg₃_pol).1 +
          (X.1.1 - Finsupp.single g₂ 1 - Finsupp.single g₃ 1) ≤ Y.1.1 :=
    type10_pair_target_add_rest_le_of_gaps hg₂_pol hg₃_pol hq₂_le_q₃
      X Y hXY g₂ g₃ rfl rfl hg₂_rank_q hg₃_rank_q (by omega) (by omega)
      (fun h => hne_g₃_g₂ h.symm) hgap_pred hgap_mid hgap_succ
  exact exists_mutation_le_type10_of_genes hg₂_pol hg₃_pol hq₂_le_q₃
    X Y g₂ g₃ rfl rfl hg₂_rank_q hg₃_rank_q (by omega) (by omega)
    (fun h => hne_g₃_g₂ h.symm) hZle

private lemma exists_mutation_le_no_pair_rank_one_singleton_multiplicity_boundary
    {m q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (g g₂ : Gene)
    (hg_rank_one : g.rank = 1)
    (hg_one : X.1.1 g = 1)
    (hne_g₂_g : g₂ ≠ g)
    (hg₂_one : X.1.1 g₂ = 1)
    (hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (restAfterG₂ : Chromosome)
    (hrest_def : restAfterG₂ = X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1)
    (hrest₂_empty : ¬ restAfterG₂ ≠ 0) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  -- §17 Case 4 needs `X` to have at least three genes (from `r₀-r₁ ≥ s₀-s₁+2`),
  -- but here `X = g + g₂` has exactly two.  So this boundary is vacuous.
  exfalso
  have hrest0 : X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1 = 0 := by
    rw [← hrest_def]; exact not_not.mp hrest₂_empty
  have hg_ne_g₂ : g ≠ g₂ := fun h => hne_g₂_g h.symm
  have hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g₂ 1 := by
    ext g'
    have hz := DFunLike.congr_fun hrest0 g'
    rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.tsub_apply, Finsupp.tsub_apply,
        Finsupp.single_apply, Finsupp.single_apply] at hz
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h1 : g = g'
    · subst h1
      rw [if_pos rfl, if_neg hne_g₂_g] at hz ⊢
      omega
    · by_cases h2 : g₂ = g'
      · subst h2
        rw [if_neg hg_ne_g₂, if_pos rfl] at hz ⊢
        omega
      · rw [if_neg h1, if_neg h2] at hz ⊢
        omega
  -- `rank X = 2q₂+4`, `rank (prime X) = 2q₂+2` (only `g₂` survives one `prime`).
  have hrankX : X.1.1.rank = 2 * q₂ + 4 := by
    rw [hXeq, map_add, rank_single, rank_single, one_smul, one_smul,
        hg_rank_one, hg₂_rank_q]; omega
  have hprimeX_eq : Chromosome.prime^[1] X.1.1 = Gene.ofRank (2 * q₂ + 2) g₂.type := by
    show X.1.1.prime = _
    rw [hXeq, map_add, prime_single, prime_single, one_smul, one_smul,
        hg_rank_one, hg₂_rank_q]
    simp [Gene.ofRank_zero, show 2 * q₂ + 3 - 1 = 2 * q₂ + 2 from by omega]
  have hrankprimeX : (Chromosome.prime^[1] X.1.1).rank = 2 * q₂ + 2 := by
    rw [hprimeX_eq, rank_ofRank]
  have hm : m + 2 = 2 * q₂ + 4 := by rw [← X.2]; exact hrankX
  -- Both `prime X` and `prime Y` lie in `Mix (Pi, 2 • Lambda)`, so their
  -- signature components are integers; `hseed1` then gives a `+2` rank gap.
  have hmemX : Chromosome.prime^[1] X.1.1 ∈ Mix (Pi, 2 • Lambda) := by
    have h := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 1
    rwa [if_neg (by decide)] at h
  have hmemY : Chromosome.prime^[1] Y.1.1 ∈ Mix (Pi, 2 • Lambda) := by
    have h := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 1
    rwa [if_neg (by decide)] at h
  obtain ⟨nx, hnx⟩ := Mix2LambdaSection17.signature_Mix_Pi_2Lambda_isNat hmemX
  obtain ⟨ny, hny⟩ := Mix2LambdaSection17.signature_Mix_Pi_2Lambda_isNat hmemY
  have hnx1 : (signature (Chromosome.prime^[1] X.1.1)).1 = (nx.1 : ℚ) := by rw [hnx]
  have hnx2 : (signature (Chromosome.prime^[1] X.1.1)).2 = (nx.2 : ℚ) := by rw [hnx]
  have hny1 : (signature (Chromosome.prime^[1] Y.1.1)).1 = (ny.1 : ℚ) := by rw [hny]
  have hny2 : (signature (Chromosome.prime^[1] Y.1.1)).2 = (ny.2 : ℚ) := by rw [hny]
  have hgap1 : nx.1 < ny.1 := by
    have h : (nx.1 : ℚ) < ny.1 := by rw [← hnx1, ← hny1]; exact hseed1.1
    exact_mod_cast h
  have hgap2 : nx.2 < ny.2 := by
    have h : (nx.2 : ℚ) < ny.2 := by rw [← hnx2, ← hny2]; exact hseed1.2
    exact_mod_cast h
  have hrx : (Chromosome.prime^[1] X.1.1).rank = nx.1 + nx.2 := by
    have h := signature_sum_eq_rank (X := Chromosome.prime^[1] X.1.1)
    rw [hnx1, hnx2] at h; exact_mod_cast h.symm
  have hry : (Chromosome.prime^[1] Y.1.1).rank = ny.1 + ny.2 := by
    have h := signature_sum_eq_rank (X := Chromosome.prime^[1] Y.1.1)
    rw [hny1, hny2] at h; exact_mod_cast h.symm
  have hYne : Y.1.1 ≠ 0 := by
    intro h; have h2 := Y.2; rw [h] at h2; simp at h2
  have hprimeYlt : (Chromosome.prime^[1] Y.1.1).rank < Y.1.1.rank := by
    show Y.1.1.prime.rank < Y.1.1.rank
    exact prime_rank_lt hYne
  rw [hrx] at hrankprimeX
  rw [hry, Y.2, hm] at hprimeYlt
  omega

private lemma exists_mutation_le_no_pair_rank_one_singleton
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_one : X.1.1 g = 1)
    (g₂ : Gene)
    (hg₂_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g₂)
    (hg₂min : ∀ g' : Gene,
      0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g' →
        g₂.rank ≤ g'.rank) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXg₂ : 0 < X.1.1 g₂ := by
    exact lt_of_lt_of_le hg₂_rest (Nat.sub_le _ _)
  have hne_g₂_g : g₂ ≠ g := by
    intro h
    subst h
    simp [hg_one] at hg₂_rest
  have hne_g₂_neg : g₂ ≠ -g := by
    intro h
    subst h
    rw [hXneg_zero] at hXg₂
    omega
  have hg₂_pol : g₂.type ≠ GeneType.NonPolarized :=
    IsPolarized_def'.mp hXpol g₂ (Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂))
  have hg₂_odd : Odd g₂.rank :=
    Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi X.1.2 hXg₂ hg₂_pol
  have hg₂_rank_ge_three : 3 ≤ g₂.rank := by
    have hmin_le := hgmin g₂ hXg₂
    rw [hg_rank_one] at hmin_le
    obtain ⟨n₂, hg₂_rank_raw⟩ := hg₂_odd
    by_contra hnot
    have hg₂_rank_one : g₂.rank = 1 := by omega
    have hrank_eq : g₂.rank = g.rank := by omega
    cases hg_type : g.type with
    | NonPolarized => exact hg_pol hg_type
    | Positive =>
        cases hg₂_type : g₂.type with
        | NonPolarized => exact hg₂_pol hg₂_type
        | Positive =>
            exact hne_g₂_g (Gene.ext hrank_eq (by rw [hg₂_type, hg_type]))
        | Negative =>
            exact hno_pair ⟨g, g₂, hrank_eq.symm, hg_type, hg₂_type, hgX, hXg₂⟩
    | Negative =>
        cases hg₂_type : g₂.type with
        | NonPolarized => exact hg₂_pol hg₂_type
        | Positive =>
            exact hno_pair ⟨g₂, g, hrank_eq, hg₂_type, hg_type, hXg₂, hgX⟩
        | Negative =>
            exact hne_g₂_g (Gene.ext hrank_eq (by rw [hg₂_type, hg_type]))
  obtain ⟨n₂, hg₂_rank_raw⟩ := hg₂_odd
  have hn₂_pos : 0 < n₂ := by
    rw [hg₂_rank_raw] at hg₂_rank_ge_three
    omega
  let q₂ := n₂ - 1
  have hn₂_eq : n₂ = q₂ + 1 := by omega
  have hg₂_rank_q : g₂.rank = 2 * q₂ + 3 := by omega
  have hXprime1_ne : Chromosome.prime^[1] X.1.1 ≠ 0 := by
    change X.1.1.prime ≠ 0
    intro hprime
    have hall :=
      (Chromosome.prime_iterate_eq_zero_rank_le (X := X.1.1) (k := 1)).2 hprime
    have hg₂_supp : g₂ ∈ X.1.1.support :=
      Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂)
    have hle := hall g₂ hg₂_supp
    omega
  have hYprime1_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
    intro hYzero
    have hle := le_iff_dominates.mp hXY.le 1
    rw [hYzero, map_zero] at hle
    exact hXprime1_ne (signature_eq_zero (le_antisymm hle (signature_nonneg _)))
  have hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank :=
    h17_1 1 (by omega) hYprime1_ne
  have hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2 := by
    exact Mix2LambdaSection17.seed_strict_lt_at_odd
      X.1.2 Y.1.2 (i := 1) (by decide) hr1
  by_cases hg₂_two : 2 ≤ X.1.1 g₂
  · -- There are already two later copies; the type10 source will use
    -- `g₂ + g₂`, with the rank-one gene left in the rest.
    exact exists_mutation_le_no_pair_rank_one_singleton_second_double
      X Y hXY hcommon h17_1 hXpol hno_pair g g₂ hg_rank_one hg_one hg₂min
      hg₂_pol hg₂_rank_q hseed1 hg₂_two
  · have hg₂_one : X.1.1 g₂ = 1 := by omega
    let restAfterG₂ : Chromosome :=
      X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1
    by_cases hrest₂_ne : restAfterG₂ ≠ 0
    · obtain ⟨g₃, hg₃_rest, hg₃min⟩ :=
        Mix2LambdaSection17.exists_min_rank_gene hrest₂_ne
      have hXg₃ : 0 < X.1.1 g₃ := by
        dsimp [restAfterG₂] at hg₃_rest
        exact lt_of_lt_of_le hg₃_rest (by
          omega)
      have hne_g₃_g : g₃ ≠ g := by
        intro h
        subst h
        dsimp [restAfterG₂] at hg₃_rest
        simp [hg_one, hne_g₂_g.symm] at hg₃_rest
      have hne_g₃_g₂ : g₃ ≠ g₂ := by
        intro h
        subst h
        dsimp [restAfterG₂] at hg₃_rest
        simp [hg₂_one, hne_g₂_g] at hg₃_rest
      have hg₃_pol : g₃.type ≠ GeneType.NonPolarized := by
        exact IsPolarized_def'.mp hXpol g₃
          (Finsupp.mem_support_iff.mpr (ne_of_gt hXg₃))
      have hg₃_odd : Odd g₃.rank := by
        exact Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
          X.1.2 hXg₃ hg₃_pol
      have hg₂_le_g₃ : g₂.rank ≤ g₃.rank := by
        have hg₃_restAfterG : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g₃ := by
          dsimp [restAfterG₂] at hg₃_rest
          exact lt_of_lt_of_le hg₃_rest (Nat.sub_le _ _)
        exact hg₂min g₃ hg₃_restAfterG
      obtain ⟨n₃, hg₃_rank_raw⟩ := hg₃_odd
      have hn₃_pos : 0 < n₃ := by
        rw [hg₃_rank_raw] at hg₂_le_g₃
        rw [hg₂_rank_q] at hg₂_le_g₃
        omega
      let q₃ := n₃ - 1
      have hn₃_eq : n₃ = q₃ + 1 := by omega
      have hg₃_rank_q : g₃.rank = 2 * q₃ + 3 := by omega
      have hq₂_le_q₃ : q₂ ≤ q₃ := by
        rw [hg₂_rank_q, hg₃_rank_q] at hg₂_le_g₃
        omega
      exact exists_mutation_le_no_pair_rank_one_singleton_later_distinct
        X Y hXY hcommon h17_1 hXpol hno_pair g g₂ g₃ hgX hgmin hg_pol hp hp0
        hg_rank_one hXneg_zero hg_one hg₂_rest hg₂min hXg₂ hne_g₂_g
        hne_g₂_neg hg₂_pol hg₂_rank_q hseed1 hg₂_one restAfterG₂
        rfl hg₃_rest hg₃min hXg₃ hne_g₃_g hne_g₃_g₂ hg₃_pol hg₂_le_g₃
        hg₃_rank_q hq₂_le_q₃
    · -- Boundary: after `g` and one copy of `g₂`, no later source remains.
      -- This is the formal place where the informal proof uses the
      -- `s₁-r₁ ≥ 2` multiplicity gap to rule the case out.
      exact exists_mutation_le_no_pair_rank_one_singleton_multiplicity_boundary
        X Y g g₂ hg_rank_one hg_one hne_g₂_g hg₂_one hg₂_rank_q hseed1 restAfterG₂
        rfl hrest₂_ne

lemma exists_mutation_le_no_pair_rank_one
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg_rank_one : g.rank = 1 := by omega
  have hXneg_zero : X.1.1 (-g) = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hnegX
    cases htype : g.type with
    | NonPolarized => exact hg_pol htype
    | Positive =>
        exact hno_pair ⟨g, -g, by simp, htype, by simp [htype], hgX, hnegX⟩
    | Negative =>
        exact hno_pair ⟨-g, g, by simp, by simp [htype], htype, hnegX, hgX⟩
  by_cases hg_two : 2 ≤ X.1.1 g
  · exact exists_mutation_le_no_pair_rank_one_double X Y hXY hcommon h17_1
      hXpol hno_pair g hgX hgmin hg_pol hp hp0 hg_rank_one hXneg_zero hg_two
  · have hg_one : X.1.1 g = 1 := by omega
    let restAfterG : Chromosome := X.1.1 - Finsupp.single g 1
    have hrest_ne : restAfterG ≠ 0 := by
      intro hzero
      change X.1.1 - Finsupp.single g 1 = 0 at hzero
      have hXeq : X.1.1 = Finsupp.single g 1 := by
        rw [← sub_single_add_single_eq hgX, hzero]
        simp
      have hrankX : X.1.1.rank = 1 := by
        rw [hXeq, rank_single, one_smul, hg_rank_one]
      rw [X.2] at hrankX
      omega
    obtain ⟨g₂, hg₂_rest, hg₂min⟩ :=
      Mix2LambdaSection17.exists_min_rank_gene hrest_ne
    exact exists_mutation_le_no_pair_rank_one_singleton X Y hXY hcommon h17_1
      hXpol hno_pair g hgX hgmin hg_pol hp hp0 hg_rank_one hXneg_zero
      hg_one g₂ hg₂_rest hg₂min

end Mix2LambdaPi
