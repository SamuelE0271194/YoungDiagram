import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Seed
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34SecondDouble

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

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
  sorry

private lemma exists_mutation_le_no_pair_rank_one_singleton_second_double
    {m p q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
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
    (g g₂ : Gene) (hgX : 0 < X.1.1 g)
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
    have hnat : restAfterG₂.sum (fun _ n => n) + 2 = X.1.1.sum (fun _ n => n) := by
      rw [hrestAfterG₂]
      have hrest1 := totalMult_sub_single_one hg_one
      have hrest2 := totalMult_sub_single_one
        (X := (X.1.1 - Finsupp.single g 1 : Chromosome)) (gm := g₂)
        hg₂_rest_one_mid
      omega
    have hq : restAfterG₂.sum (fun _ n => (n : ℚ)) + 2 =
        X.1.1.sum (fun _ n => (n : ℚ)) := by
      exact_mod_cast hnat
    linarith
  have hD_mid :
      X.1.1.sum (fun _ n => (n : ℚ)) =
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
        (X.1.1.rank : ℚ) := by
      simpa [Sigma.sigma] using (@signature_sum_eq_rank X.1.1)
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        (X.1.1.prime.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
      simpa [Sigma.sigma, Function.iterate_one] using this
    have hcells := MixLambdaPi.cells (Z := X.1.1)
    linarith
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
    simpa [Sigma.sigma, hprime]
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
    have hcond7 := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi Y.1.2 i
    rw [if_pos hi] at hcond7
    have hdrop := rank_drop_le Y.1.2 i
    have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
      simpa [Sigma.sigma, X.2] using this
    have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
      simpa [Sigma.sigma, Y.2] using this
    have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have hgap2 := case4_gap2 X Y hseed1
    have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
      exact_mod_cast hgap2
    linarith
  have hYdrop_snd_strong_even :
      ∀ i, Even i →
        (Sigma.sigma Y.1.1 i).2 - (Sigma.sigma Y.1.1 (i + 2)).2 ≤
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro i hi
    have hcond6 := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi Y.1.2 i
    rw [if_pos hi] at hcond6
    have hdrop := rank_drop_le Y.1.2 i
    have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
      simpa [Sigma.sigma, X.2] using this
    have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
      simpa [Sigma.sigma, Y.2] using this
    have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have hgap2 := case4_gap2 X Y hseed1
    have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
      exact_mod_cast hgap2
    linarith
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
  have hgap_mid : ∀ j, 2 * q₂ + 3 ≤ j → j ≤ 2 * q₃ + 3 →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi
    by_cases hjlower : j = 2 * q₂ + 3
    · subst j
      exact hgap_mid_lower
    · -- Remaining work: propagate the Case 4 window above the lower endpoint
      -- through the distinct top gene `g₃`, with odd levels discharged by the
      -- reduced rank gap.
      sorry
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
  have hWsum :
      (Chromosome.prime^[2 * q₃ + 1] X.1.1).sum (fun _ n => (n : ℚ)) =
        restAfterG₂.sum (fun _ n => (n : ℚ)) := by
    exact_mod_cast hWsum_nat
  have hrest_sum :
      restAfterG₂.sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 2 := by
    have hrest1 := totalMult_sub_single_one hg_one
    have hrest2 := totalMult_sub_single_one
      (X := (X.1.1 - Finsupp.single g 1 : Chromosome)) (gm := g₂) hg₂_rest_one
    have hnat : restAfterG₂.sum (fun _ n => n) + 2 = X.1.1.sum (fun _ n => n) := by
      rw [hrestAfterG₂]
      omega
    have hq : restAfterG₂.sum (fun _ n => (n : ℚ)) + 2 =
        X.1.1.sum (fun _ n => (n : ℚ)) := by
      exact_mod_cast hnat
    linarith
  have hD :
      X.1.1.sum (fun _ n => (n : ℚ)) =
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
        (X.1.1.rank : ℚ) := by
      simpa [Sigma.sigma] using (@signature_sum_eq_rank X.1.1)
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        (X.1.1.prime.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
      simpa [Sigma.sigma, Function.iterate_one] using this
    have hcells := MixLambdaPi.cells (Z := X.1.1)
    linarith
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
    have hi : Even (2 * q₃ + 2) := ⟨q₃ + 1, by ring⟩
    have hcond7 := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi
      Y.1.2 (2 * q₃ + 2)
    rw [if_pos hi] at hcond7
    have hdrop := rank_drop_le Y.1.2 (2 * q₃ + 2)
    have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
      simpa [Sigma.sigma, X.2] using this
    have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
      simpa [Sigma.sigma, Y.2] using this
    have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have hgap2 := case4_gap2 X Y hseed1
    have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
      exact_mod_cast hgap2
    have hidx : 2 * q₃ + 2 + 2 = 2 * q₃ + 4 := by omega
    rw [hidx] at hcond7
    linarith
  have hYdrop_snd_strong :
      (Sigma.sigma Y.1.1 (2 * q₃ + 2)).2 - (Sigma.sigma Y.1.1 (2 * q₃ + 4)).2 ≤
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    have hi : Even (2 * q₃ + 2) := ⟨q₃ + 1, by ring⟩
    have hcond6 := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi
      Y.1.2 (2 * q₃ + 2)
    rw [if_pos hi] at hcond6
    have hdrop := rank_drop_le Y.1.2 (2 * q₃ + 2)
    have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
      simpa [Sigma.sigma, X.2] using this
    have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
      simpa [Sigma.sigma, Y.2] using this
    have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have hgap2 := case4_gap2 X Y hseed1
    have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
      exact_mod_cast hgap2
    have hidx : 2 * q₃ + 2 + 2 = 2 * q₃ + 4 := by omega
    rw [hidx] at hcond6
    linarith
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
          have htmp := hXdrop_raw
          rw [show 1 + (2 * q₃ + 1) = 2 * q₃ + 2 by omega,
            show 3 + (2 * q₃ + 1) = 2 * q₃ + 4 by omega] at htmp
          rw [htmp, hWsumD]
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
          have htmp := hXdrop_raw
          rw [show 1 + (2 * q₃ + 1) = 2 * q₃ + 2 by omega,
            show 3 + (2 * q₃ + 1) = 2 * q₃ + 4 by omega] at htmp
          rw [htmp, hWsumD]
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
    {m p q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
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
    (g g₂ : Gene) (hgX : 0 < X.1.1 g)
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
  rw [hry, Y.2] at hprimeYlt
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
  have hg₂_pol : g₂.type ≠ GeneType.NonPolarized := by
    exact IsPolarized_def'.mp hXpol g₂
      (Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂))
  have hg₂_odd : Odd g₂.rank := by
    exact Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
      X.1.2 hXg₂ hg₂_pol
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
      X Y hXY hcommon h17_1 hXpol hno_pair g g₂ hgX hgmin hg_pol hp hp0
      hg_rank_one hXneg_zero hg_one hg₂_rest hg₂min hXg₂ hne_g₂_g
      hne_g₂_neg hg₂_pol hg₂_rank_q hseed1 hg₂_two
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
        X Y hXY hcommon h17_1 hXpol hno_pair g g₂ hgX hgmin hg_pol hp hp0
        hg_rank_one hXneg_zero hg_one hg₂_rest hg₂min hXg₂ hne_g₂_g
        hne_g₂_neg hg₂_pol hg₂_rank_q hseed1 hg₂_one restAfterG₂ rfl hrest₂_ne

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
