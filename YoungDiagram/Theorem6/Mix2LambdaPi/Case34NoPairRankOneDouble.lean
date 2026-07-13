import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34NoPairRankOneDoubleSameGene
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34NoPairRankOneDoubleSameSign
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Seed
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34SecondDouble
import YoungDiagram.Theorem6.Mix2LambdaPi.Type14
import YoungDiagram.Theorem6.Mix2LambdaPi.Type16

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

private lemma prime_iterate_Y_ne_of_X_gene_above
    {N j : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (g : Gene) (hgX : 0 < X.1.1 g) (hj : j < g.rank) :
    Chromosome.prime^[j] Y.1.1 ≠ 0 := by
  intro hYzero
  let z : Gene := ⟨g.rank - j, g.type, by omega⟩
  have hXj_pos : 0 < (Chromosome.prime^[j] X.1.1) z := by
    have hcoeff := prime_iterate_coeff j X.1.1 z
    change (Chromosome.prime^[j] X.1.1) z =
      X.1.1 ⟨z.rank + j, z.type, Nat.le_add_right_of_le z.rank_pos⟩ at hcoeff
    have hz_eq :
        (⟨z.rank + j, z.type, Nat.le_add_right_of_le z.rank_pos⟩ : Gene) = g := by
      apply Gene.ext
      · dsimp [z]
        omega
      · rfl
    rwa [hcoeff, hz_eq]
  have hle := le_iff_dominates.mp hXY.le j
  rw [hYzero, map_zero] at hle
  have hsig_zero :=
    signature_eq_zero (le_antisymm hle (signature_nonneg _))
  have hcoeff_zero : (Chromosome.prime^[j] X.1.1) z = 0 := by
    rw [hsig_zero]
    rfl
  omega

private lemma add_two_le_of_window_step (f c : ℕ → ℚ) (j0 d : ℕ)
    (hseed : f j0 + 2 ≤ c j0)
    (hstep : ∀ t, t < d →
      c (j0 + 2 * t) - c (j0 + 2 * t + 2) ≤
        f (j0 + 2 * t) - f (j0 + 2 * t + 2)) :
    ∀ t, t ≤ d → f (j0 + 2 * t) + 2 ≤ c (j0 + 2 * t) := by
  have hprop :=
    Mix2LambdaSection17.le_of_window_step
      (fun i => f i + 2) c j0 d hseed
      (by
        intro t ht
        have h := hstep t ht
        linarith)
  intro t ht
  simpa [add_assoc] using hprop t ht

private lemma single_rank_one_drop_fst_positive {g : Gene}
    (hg_rank_one : g.rank = 1) (hg_pos : g.type = GeneType.Positive) :
    (Sigma.sigma (Finsupp.single g 1 : Chromosome) 0).1 -
        (Sigma.sigma (Finsupp.single g 1 : Chromosome) 2).1 = 1 := by
  have hsingle : (Finsupp.single g 1 : Chromosome) = Gene.ofRank g.rank g.type :=
    Gene.ofRank_eq_gene.symm
  rw [hsingle, Sigma.sigma, Sigma.sigma, prime_iterate_ofRank,
    prime_iterate_ofRank, hg_rank_one, hg_pos, signature_ofRank_one_positive]
  simp

private lemma single_rank_one_drop_snd_negative {g : Gene}
    (hg_rank_one : g.rank = 1) (hg_neg : g.type = GeneType.Negative) :
    (Sigma.sigma (Finsupp.single g 1 : Chromosome) 0).2 -
        (Sigma.sigma (Finsupp.single g 1 : Chromosome) 2).2 = 1 := by
  have hsingle : (Finsupp.single g 1 : Chromosome) = Gene.ofRank g.rank g.type :=
    Gene.ofRank_eq_gene.symm
  rw [hsingle, Sigma.sigma, Sigma.sigma, prime_iterate_ofRank,
    prime_iterate_ofRank, hg_rank_one, hg_neg, signature_ofRank_one_negative]
  simp

private lemma rank_one_double_drop_fst_positive
    {N : ℕ} (X : nMix2LambdaPi N) {g : Gene} (_restAfterDouble : Chromosome)
    (hg_rank_one : g.rank = 1) (hg_pos : g.type = GeneType.Positive)
    (hg_two : 2 ≤ X.1.1 g)
    (hrest_eq :
      _restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (htail_after_double : ∀ h ∈ _restAfterDouble.support, 3 ≤ h.rank)
    (hrest_total :
      _restAfterDouble.sum (fun _ n => n) + 2 =
        X.1.1.sum (fun _ n => n)) :
    (Sigma.sigma X.1.1 0).1 - (Sigma.sigma X.1.1 2).1 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
  have hdecomp :
      Finsupp.single g 1 + Finsupp.single g 1 + _restAfterDouble = X.1.1 := by
    rw [hrest_eq]
    exact Mix2LambdaSection17.double_single_add_rest hg_two
  have hsig0 :
      Sigma.sigma X.1.1 0 =
        Sigma.sigma (Finsupp.single g 1 : Chromosome) 0 +
          Sigma.sigma (Finsupp.single g 1 : Chromosome) 0 +
          Sigma.sigma _restAfterDouble 0 := by
    rw [← hdecomp, Sigma.sigma_linearity, Sigma.sigma_linearity]
  have hsig2 :
      Sigma.sigma X.1.1 2 =
        Sigma.sigma (Finsupp.single g 1 : Chromosome) 2 +
          Sigma.sigma (Finsupp.single g 1 : Chromosome) 2 +
          Sigma.sigma _restAfterDouble 2 := by
    rw [← hdecomp, Sigma.sigma_linearity, Sigma.sigma_linearity]
  have hrest_drop :
      (Sigma.sigma _restAfterDouble 0).1 -
          (Sigma.sigma _restAfterDouble 2).1 =
        _restAfterDouble.sum (fun _ n => (n : ℚ)) := by
    have htail : ∀ h ∈ _restAfterDouble.support, 0 + 2 ≤ h.rank := by
      intro h hh
      have := htail_after_double h hh
      omega
    simpa using MixLambdaPi.twostep (W := _restAfterDouble) (i := 0) htail
  have hsingle_drop := single_rank_one_drop_fst_positive hg_rank_one hg_pos
  have hrest_sum :
      _restAfterDouble.sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 2 := by
    have hq :
        _restAfterDouble.sum (fun _ n => (n : ℚ)) + 2 =
          X.1.1.sum (fun _ n => (n : ℚ)) := by
      exact_mod_cast hrest_total
    linarith
  have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
  have hsig0_fst := congrArg Prod.fst hsig0
  have hsig2_fst := congrArg Prod.fst hsig2
  simp only [Prod.fst_add] at hsig0_fst hsig2_fst
  rw [hsig0_fst, hsig2_fst]
  linarith [hrest_drop, hsingle_drop, hrest_sum, hD]

private lemma rank_one_double_drop_snd_negative
    {N : ℕ} (X : nMix2LambdaPi N) {g : Gene} (_restAfterDouble : Chromosome)
    (hg_rank_one : g.rank = 1) (hg_neg : g.type = GeneType.Negative)
    (hg_two : 2 ≤ X.1.1 g)
    (hrest_eq :
      _restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (htail_after_double : ∀ h ∈ _restAfterDouble.support, 3 ≤ h.rank)
    (hrest_total :
      _restAfterDouble.sum (fun _ n => n) + 2 =
        X.1.1.sum (fun _ n => n)) :
    (Sigma.sigma X.1.1 0).2 - (Sigma.sigma X.1.1 2).2 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
  have hdecomp :
      Finsupp.single g 1 + Finsupp.single g 1 + _restAfterDouble = X.1.1 := by
    rw [hrest_eq]
    exact Mix2LambdaSection17.double_single_add_rest hg_two
  have hsig0 :
      Sigma.sigma X.1.1 0 =
        Sigma.sigma (Finsupp.single g 1 : Chromosome) 0 +
          Sigma.sigma (Finsupp.single g 1 : Chromosome) 0 +
          Sigma.sigma _restAfterDouble 0 := by
    rw [← hdecomp, Sigma.sigma_linearity, Sigma.sigma_linearity]
  have hsig2 :
      Sigma.sigma X.1.1 2 =
        Sigma.sigma (Finsupp.single g 1 : Chromosome) 2 +
          Sigma.sigma (Finsupp.single g 1 : Chromosome) 2 +
          Sigma.sigma _restAfterDouble 2 := by
    rw [← hdecomp, Sigma.sigma_linearity, Sigma.sigma_linearity]
  have hrest_drop :
      (Sigma.sigma _restAfterDouble 0).2 -
          (Sigma.sigma _restAfterDouble 2).2 =
        _restAfterDouble.sum (fun _ n => (n : ℚ)) := by
    have htail : ∀ h ∈ _restAfterDouble.support, 0 + 2 ≤ h.rank := by
      intro h hh
      have := htail_after_double h hh
      omega
    simpa using MixLambdaPi.twostep_snd (W := _restAfterDouble) (i := 0) htail
  have hsingle_drop := single_rank_one_drop_snd_negative hg_rank_one hg_neg
  have hrest_sum :
      _restAfterDouble.sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 2 := by
    have hq :
        _restAfterDouble.sum (fun _ n => (n : ℚ)) + 2 =
          X.1.1.sum (fun _ n => (n : ℚ)) := by
      exact_mod_cast hrest_total
    linarith
  have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
  have hsig0_snd := congrArg Prod.snd hsig0
  have hsig2_snd := congrArg Prod.snd hsig2
  simp only [Prod.snd_add] at hsig0_snd hsig2_snd
  rw [hsig0_snd, hsig2_snd]
  linarith [hrest_drop, hsingle_drop, hrest_sum, hD]

private lemma rank_one_double_seed_fst_add_two_positive
    {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    {g : Gene} (_restAfterDouble : Chromosome)
    (hg_rank_one : g.rank = 1) (hg_pos : g.type = GeneType.Positive)
    (hg_two : 2 ≤ X.1.1 g)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hrest_eq :
      _restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (htail_after_double : ∀ h ∈ _restAfterDouble.support, 3 ≤ h.rank)
    (hrest_total :
      _restAfterDouble.sum (fun _ n => n) + 2 =
        X.1.1.sum (fun _ n => n)) :
    (Sigma.sigma X.1.1 2).1 + 2 ≤ (Sigma.sigma Y.1.1 2).1 := by
  have hXdrop :=
    rank_one_double_drop_fst_positive X _restAfterDouble hg_rank_one hg_pos
      hg_two hrest_eq htail_after_double hrest_total
  have hYdrop := case4_Ydrop_fst_strong_even X Y hseed1 (by decide : Even 0)
  have h0fst : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 :=
    congrArg Prod.fst (sigma_zero_eq X Y hXY)
  simp only [Nat.zero_add] at hYdrop
  linarith

private lemma rank_one_double_seed_snd_add_two_negative
    {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    {g : Gene} (_restAfterDouble : Chromosome)
    (hg_rank_one : g.rank = 1) (hg_neg : g.type = GeneType.Negative)
    (hg_two : 2 ≤ X.1.1 g)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hrest_eq :
      _restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (htail_after_double : ∀ h ∈ _restAfterDouble.support, 3 ≤ h.rank)
    (hrest_total :
      _restAfterDouble.sum (fun _ n => n) + 2 =
        X.1.1.sum (fun _ n => n)) :
    (Sigma.sigma X.1.1 2).2 + 2 ≤ (Sigma.sigma Y.1.1 2).2 := by
  have hXdrop :=
    rank_one_double_drop_snd_negative X _restAfterDouble hg_rank_one hg_neg
      hg_two hrest_eq htail_after_double hrest_total
  have hYdrop := case4_Ydrop_snd_strong_even X Y hseed1 (by decide : Even 0)
  have h0snd : (Sigma.sigma X.1.1 0).2 = (Sigma.sigma Y.1.1 0).2 :=
    congrArg Prod.snd (sigma_zero_eq X Y hXY)
  simp only [Nat.zero_add] at hYdrop
  linarith

private lemma rank_one_double_middle_gap_pack
    {m q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (_hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g g₂ : Gene)
    (_hg_pol : g.type ≠ .NonPolarized)
    (_hg_rank_one : g.rank = 1)
    (_hg_two : 2 ≤ X.1.1 g)
    (_hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (_restAfterDouble : Chromosome)
    (_hXg₂ : 0 < X.1.1 g₂)
    (_hg₂_pol : g₂.type ≠ .NonPolarized)
    (_hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (_htail_after_double :
      ∀ h ∈ _restAfterDouble.support, 2 * q₂ + 3 ≤ h.rank)
    (_hrestAfterDouble_eq :
      _restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) :
    (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1)) ∧
    (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → Even j →
      (signature (Gene.ofRank 1 g.type) +
            signature (Gene.ofRank 1 g.type)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1)) := by
  have hgap_odd_non_top :
      ∀ j, 1 ≤ j → j < 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
        ((1 : ℚ), (1 : ℚ)) +
            signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjlt hjodd _hj1
    exact type10_mid_gap_odd_of_Y_ne X Y h17_1 hjodd (by omega)
      (prime_iterate_Y_ne_of_X_gene_above X Y hXY g₂ _hXg₂ (by
        rw [_hg₂_rank_q]
        omega))
  have hrestAfterDouble_total :
      _restAfterDouble.sum (fun _ n => n) + 2 =
        X.1.1.sum (fun _ n => n) := by
    rw [_hrestAfterDouble_eq]
    exact totalMult_sub_double_single (X := X.1.1) (gm := g) _hg_two
  have hrestAfterDouble_sum_cast :
      _restAfterDouble.sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 2 := by
    have hq :
        _restAfterDouble.sum (fun _ n => (n : ℚ)) + 2 =
          X.1.1.sum (fun _ n => (n : ℚ)) := by
      exact_mod_cast hrestAfterDouble_total
    linarith
  have htail_sigma_double_eq : ∀ i, 1 ≤ i →
      Sigma.sigma X.1.1 i = Sigma.sigma _restAfterDouble i := by
    intro i hi
    have hprime :
        Chromosome.prime^[i] X.1.1 =
          Chromosome.prime^[i] _restAfterDouble := by
      rw [prime_iterate_eq_sub_double_single_of_rank_le
        (X := X.1.1) (gm := g) _hg_two (i := i) (by rw [_hg_rank_one]; exact hi)]
      rw [← _hrestAfterDouble_eq]
    simp [Sigma.sigma, hprime]
  have hXdouble_window_drop_fst :
      ∀ i, 1 ≤ i → i + 2 ≤ 2 * q₂ + 3 →
        (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro i hi htop
    have hsig_i := htail_sigma_double_eq i hi
    have hsig_i2 := htail_sigma_double_eq (i + 2) (by omega)
    have htail :
        ∀ h ∈ _restAfterDouble.support, i + 2 ≤ h.rank := by
      intro h hh
      have := _htail_after_double h hh
      omega
    have hdrop := MixLambdaPi.twostep (W := _restAfterDouble) (i := i) htail
    have hfst_i := congrArg Prod.fst hsig_i
    have hfst_i2 := congrArg Prod.fst hsig_i2
    rw [hfst_i, hfst_i2, hdrop, hrestAfterDouble_sum_cast]
    have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
    rw [hD]
  have hXdouble_window_drop_snd :
      ∀ i, 1 ≤ i → i + 2 ≤ 2 * q₂ + 3 →
        (Sigma.sigma X.1.1 i).2 - (Sigma.sigma X.1.1 (i + 2)).2 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro i hi htop
    have hsig_i := htail_sigma_double_eq i hi
    have hsig_i2 := htail_sigma_double_eq (i + 2) (by omega)
    have htail :
        ∀ h ∈ _restAfterDouble.support, i + 2 ≤ h.rank := by
      intro h hh
      have := _htail_after_double h hh
      omega
    have hdrop := MixLambdaPi.twostep_snd (W := _restAfterDouble) (i := i) htail
    have hsnd_i := congrArg Prod.snd hsig_i
    have hsnd_i2 := congrArg Prod.snd hsig_i2
    rw [hsnd_i, hsnd_i2, hdrop, hrestAfterDouble_sum_cast]
    have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
    rw [hD]
  have htail_after_double_three :
      ∀ h ∈ _restAfterDouble.support, 3 ≤ h.rank := by
    intro h hh
    have := _htail_after_double h hh
    omega
  have hgap_even_pos_fst :
      g.type = GeneType.Positive →
        ∀ t, t ≤ q₂ →
          (Sigma.sigma X.1.1 (2 + 2 * t)).1 + 2 ≤
            (Sigma.sigma Y.1.1 (2 + 2 * t)).1 := by
    intro hg_pos
    have hseed2 :=
      rank_one_double_seed_fst_add_two_positive X Y hXY _restAfterDouble
        _hg_rank_one hg_pos _hg_two _hseed1 _hrestAfterDouble_eq
        htail_after_double_three hrestAfterDouble_total
    apply add_two_le_of_window_step
      (fun i => (Sigma.sigma X.1.1 i).1)
      (fun i => (Sigma.sigma Y.1.1 i).1) 2 q₂ hseed2
    intro t ht
    have heven : Even (2 + 2 * t) := ⟨t + 1, by ring⟩
    have hYdrop := case4_Ydrop_fst_strong_even X Y _hseed1 heven
    have hXdrop := hXdouble_window_drop_fst (2 + 2 * t) (by omega) (by omega)
    linarith
  have hgap_even_neg_snd :
      g.type = GeneType.Negative →
        ∀ t, t ≤ q₂ →
          (Sigma.sigma X.1.1 (2 + 2 * t)).2 + 2 ≤
            (Sigma.sigma Y.1.1 (2 + 2 * t)).2 := by
    intro hg_neg
    have hseed2 :=
      rank_one_double_seed_snd_add_two_negative X Y hXY _restAfterDouble
        _hg_rank_one hg_neg _hg_two _hseed1 _hrestAfterDouble_eq
        htail_after_double_three hrestAfterDouble_total
    apply add_two_le_of_window_step
      (fun i => (Sigma.sigma X.1.1 i).2)
      (fun i => (Sigma.sigma Y.1.1 i).2) 2 q₂ hseed2
    intro t ht
    have heven : Even (2 + 2 * t) := ⟨t + 1, by ring⟩
    have hYdrop := case4_Ydrop_snd_strong_even X Y _hseed1 heven
    have hXdrop := hXdouble_window_drop_snd (2 + 2 * t) (by omega) (by omega)
    linarith
  have hgap_odd_top :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q₂ + 3] X.1.1) ≤
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
      have hhodd : Odd h.rank := by
        rw [hhrank]
        exact ⟨q₂ + 1, by ring⟩
      have hodd_part : 0 < Y.1.1.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]
        exact hh
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
        (Finsupp.mem_support_iff.mpr hodd_part.ne')
    cases htype : g₂.type with
    | NonPolarized => exact absurd htype _hg₂_pol
    | Positive =>
        have hno_pos : Y.1.1 ⟨2 * q₂ + 3, GeneType.Positive, by omega⟩ = 0 := by
          have htop_eq_g : (⟨2 * q₂ + 3, GeneType.Positive, by omega⟩ : Gene) = g₂ :=
            Gene.ext (by dsimp; rw [_hg₂_rank_q]) htype.symm
          have hle := _hcommon g₂ _hXg₂
          rw [htop_eq_g]
          omega
        have hYfst0 :=
          signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
            (W := Y.1.1) (p := q₂ + 1) hYpol_top hYrank hno_pos
        have hYfst0' : (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1 = 0 := by
          simpa [show 2 * (q₂ + 1) = 2 * q₂ + 2 by omega] using hYfst0
        have hXfst1 :=
          one_le_signature_prime_pred_fst_of_positive (X := X.1.1) (gpos := g₂)
            htype _hXg₂
        have hXfst1' : 1 ≤ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 := by
          simpa [_hg₂_rank_q, show 2 * q₂ + 3 - 1 = 2 * q₂ + 2 by omega] using hXfst1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).1
        linarith
    | Negative =>
        have hno_neg : Y.1.1 ⟨2 * q₂ + 3, GeneType.Negative, by omega⟩ = 0 := by
          have htop_eq_g : (⟨2 * q₂ + 3, GeneType.Negative, by omega⟩ : Gene) = g₂ :=
            Gene.ext (by dsimp; rw [_hg₂_rank_q]) htype.symm
          have hle := _hcommon g₂ _hXg₂
          rw [htop_eq_g]
          omega
        have hYsnd0 :=
          signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
            (W := Y.1.1) (p := q₂ + 1) hYpol_top hYrank hno_neg
        have hYsnd0' : (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2 = 0 := by
          simpa [show 2 * (q₂ + 1) = 2 * q₂ + 2 by omega] using hYsnd0
        have hXsnd1 :=
          one_le_signature_prime_pred_snd_of_negative (X := X.1.1) (gneg := g₂)
            htype _hXg₂
        have hXsnd1' : 1 ≤ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 := by
          simpa [_hg₂_rank_q, show 2 * q₂ + 3 - 1 = 2 * q₂ + 2 by omega] using hXsnd1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).2
        linarith
  have hgap_odd :
      ∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
        ((1 : ℚ), (1 : ℚ)) +
            signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hjodd hj1
    by_cases hjtop : j = 2 * q₂ + 3
    · subst j
      exact hgap_odd_top
    · exact hgap_odd_non_top j hjlo (by omega) hjodd hj1
  have hgap_even :
      ∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → Even j →
        (signature (Gene.ofRank 1 g.type) +
              signature (Gene.ofRank 1 g.type)) +
            signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hjeven
    obtain ⟨s, hs⟩ := hjeven
    subst j
    cases s with
    | zero => omega
    | succ t =>
        have hidx : t + 1 + (t + 1) = 2 + 2 * t := by ring
        have htq : t ≤ q₂ := by omega
        rw [hidx]
        cases hg_type : g.type with
        | NonPolarized => exact absurd hg_type _hg_pol
        | Positive =>
            have hf := hgap_even_pos_fst hg_type t htq
            have hf' :
                (signature (Chromosome.prime^[2 + 2 * t] X.1.1)).1 + 2 ≤
                  (signature (Chromosome.prime^[2 + 2 * t] Y.1.1)).1 := by
              simpa [Sigma.sigma] using hf
            have hdom := (le_iff_dominates.mp hXY.le (2 + 2 * t)).2
            constructor
            · simp [signature_ofRank_one_positive]
              linarith
            · simpa [Sigma.sigma, hg_type, signature_ofRank_one_positive] using hdom
        | Negative =>
            have hsnd := hgap_even_neg_snd hg_type t htq
            have hsnd' :
                (signature (Chromosome.prime^[2 + 2 * t] X.1.1)).2 + 2 ≤
                  (signature (Chromosome.prime^[2 + 2 * t] Y.1.1)).2 := by
              simpa [Sigma.sigma] using hsnd
            have hdom := (le_iff_dominates.mp hXY.le (2 + 2 * t)).1
            constructor
            · simpa [Sigma.sigma, hg_type, signature_ofRank_one_negative] using hdom
            · simp [signature_ofRank_one_negative]
              linarith
  exact ⟨hgap_odd, hgap_even⟩

private lemma type16_rank_one_double_tail_gap_pack
    {m p q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (_hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
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
    (_hrestAfterDouble_eq :
      _restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
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
  have hgap_odd_non_top :
      ∀ j, 1 ≤ j → j < 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
        ((1 : ℚ), (1 : ℚ)) +
            signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjlt hjodd _hj1
    exact type10_mid_gap_odd_of_Y_ne X Y h17_1 hjodd (by omega)
      (prime_iterate_Y_ne_of_X_gene_above X Y hXY g₂ _hXg₂ (by
        rw [_hg₂_rank_q]
        omega))
  have htail_after_type16_strict :
      ∀ h ∈ restAfterType16.support, 2 * q₂ + 3 < h.rank := by
    intro h hh
    have hhpos : 0 < restAfterType16 h :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have htail := _htail_after_type16 h hh
    have hXh : 0 < X.1.1 h := by
      have hle : restAfterType16 h ≤ X.1.1 h := by
        rw [_hrestAfterType16_eq]
        simp only [Finsupp.tsub_apply]
        omega
      exact lt_of_lt_of_le hhpos hle
    have hpol : h.type ≠ GeneType.NonPolarized :=
      IsPolarized_def'.mp _hXpol h (Finsupp.mem_support_iff.mpr (ne_of_gt hXh))
    by_contra hnot
    have hrank : h.rank = g₂.rank := by
      rw [_hg₂_rank_q]
      omega
    have hrest_g₂_zero : restAfterType16 g₂ = 0 := by
      rw [_hrestAfterType16_eq]
      have hne_g_g₂ : g ≠ g₂ := by
        intro hgg₂
        exact _hsame hgg₂.symm
      simp [hne_g_g₂, _hg₂_one]
    cases hg₂_type : g₂.type with
    | NonPolarized => exact _hg₂_pol hg₂_type
    | Positive =>
        cases htype : h.type with
        | NonPolarized => exact hpol htype
        | Positive =>
            have heq : h = g₂ := Gene.ext hrank (htype.trans hg₂_type.symm)
            subst h
            rw [hrest_g₂_zero] at hhpos
            omega
        | Negative =>
            exact _hno_pair ⟨g₂, h, hrank.symm, hg₂_type, htype, _hXg₂, hXh⟩
    | Negative =>
        cases htype : h.type with
        | NonPolarized => exact hpol htype
        | Positive =>
            exact _hno_pair ⟨h, g₂, hrank, htype, hg₂_type, hXh, _hXg₂⟩
        | Negative =>
            have heq : h = g₂ := Gene.ext hrank (htype.trans hg₂_type.symm)
            subst h
            rw [hrest_g₂_zero] at hhpos
            omega
  have htail_after_type16_two_step :
      ∀ h ∈ restAfterType16.support, (2 * q₂ + 3) + 2 ≤ h.rank := by
    intro h hh
    have hle := htail_after_type16_strict h hh
    have hXh : 0 < X.1.1 h := by
      have hhpos : 0 < restAfterType16 h :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      have hmono : restAfterType16 h ≤ X.1.1 h := by
        rw [_hrestAfterType16_eq]
        simp only [Finsupp.tsub_apply]
        omega
      exact lt_of_lt_of_le hhpos hmono
    have hpol : h.type ≠ GeneType.NonPolarized :=
      IsPolarized_def'.mp _hXpol h (Finsupp.mem_support_iff.mpr (ne_of_gt hXh))
    have hodd :=
      Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
        X.1.2 hXh hpol
    obtain ⟨nh, hhrank⟩ := hodd
    rw [hhrank] at hle ⊢
    omega
  have hrestAfterType16_sum_cast :
      restAfterType16.sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 3 := by
    have hq :
        restAfterType16.sum (fun _ n => (n : ℚ)) + 3 =
          X.1.1.sum (fun _ n => (n : ℚ)) := by
      exact_mod_cast _htype16_rest_total
    linarith
  have hrestAfterDouble_total :
      _restAfterDouble.sum (fun _ n => n) + 2 =
        X.1.1.sum (fun _ n => n) := by
    rw [_hrestAfterDouble_eq]
    exact totalMult_sub_double_single (X := X.1.1) (gm := g) _hg_two
  have hrestAfterDouble_sum_cast :
      _restAfterDouble.sum (fun _ n => (n : ℚ)) =
        X.1.1.sum (fun _ n => (n : ℚ)) - 2 := by
    have hq :
        _restAfterDouble.sum (fun _ n => (n : ℚ)) + 2 =
          X.1.1.sum (fun _ n => (n : ℚ)) := by
      exact_mod_cast hrestAfterDouble_total
    linarith
  have htail_sigma_double_eq : ∀ i, 1 ≤ i →
      Sigma.sigma X.1.1 i = Sigma.sigma _restAfterDouble i := by
    intro i hi
    have hprime :
        Chromosome.prime^[i] X.1.1 =
          Chromosome.prime^[i] _restAfterDouble := by
      rw [prime_iterate_eq_sub_double_single_of_rank_le
        (X := X.1.1) (gm := g) _hg_two (i := i) (by rw [_hg_rank_one]; exact hi)]
      rw [← _hrestAfterDouble_eq]
    simp [Sigma.sigma, hprime]
  have hXdouble_window_drop_fst :
      ∀ i, 1 ≤ i → i + 2 ≤ 2 * q₂ + 3 →
        (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro i hi htop
    have hsig_i := htail_sigma_double_eq i hi
    have hsig_i2 := htail_sigma_double_eq (i + 2) (by omega)
    have htail :
        ∀ h ∈ _restAfterDouble.support, i + 2 ≤ h.rank := by
      intro h hh
      have := _htail_after_double h hh
      omega
    have hdrop := MixLambdaPi.twostep (W := _restAfterDouble) (i := i) htail
    have hfst_i := congrArg Prod.fst hsig_i
    have hfst_i2 := congrArg Prod.fst hsig_i2
    rw [hfst_i, hfst_i2, hdrop, hrestAfterDouble_sum_cast]
    have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
    rw [hD]
  have hXdouble_window_drop_snd :
      ∀ i, 1 ≤ i → i + 2 ≤ 2 * q₂ + 3 →
        (Sigma.sigma X.1.1 i).2 - (Sigma.sigma X.1.1 (i + 2)).2 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
    intro i hi htop
    have hsig_i := htail_sigma_double_eq i hi
    have hsig_i2 := htail_sigma_double_eq (i + 2) (by omega)
    have htail :
        ∀ h ∈ _restAfterDouble.support, i + 2 ≤ h.rank := by
      intro h hh
      have := _htail_after_double h hh
      omega
    have hdrop := MixLambdaPi.twostep_snd (W := _restAfterDouble) (i := i) htail
    have hsnd_i := congrArg Prod.snd hsig_i
    have hsnd_i2 := congrArg Prod.snd hsig_i2
    rw [hsnd_i, hsnd_i2, hdrop, hrestAfterDouble_sum_cast]
    have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
    rw [hD]
  have htail_after_double_three :
      ∀ h ∈ _restAfterDouble.support, 3 ≤ h.rank := by
    intro h hh
    have := _htail_after_double h hh
    omega
  have hgap_even_pos_fst :
      g.type = GeneType.Positive →
        ∀ t, t ≤ q₂ →
          (Sigma.sigma X.1.1 (2 + 2 * t)).1 + 2 ≤
            (Sigma.sigma Y.1.1 (2 + 2 * t)).1 := by
    intro hg_pos
    have hseed2 :=
      rank_one_double_seed_fst_add_two_positive X Y hXY _restAfterDouble
        _hg_rank_one hg_pos _hg_two _hseed1 _hrestAfterDouble_eq
        htail_after_double_three hrestAfterDouble_total
    apply add_two_le_of_window_step
      (fun i => (Sigma.sigma X.1.1 i).1)
      (fun i => (Sigma.sigma Y.1.1 i).1) 2 q₂ hseed2
    intro t ht
    have heven : Even (2 + 2 * t) := ⟨t + 1, by ring⟩
    have hYdrop := case4_Ydrop_fst_strong_even X Y _hseed1 heven
    have hXdrop := hXdouble_window_drop_fst (2 + 2 * t) (by omega) (by omega)
    linarith
  have hgap_even_neg_snd :
      g.type = GeneType.Negative →
        ∀ t, t ≤ q₂ →
          (Sigma.sigma X.1.1 (2 + 2 * t)).2 + 2 ≤
            (Sigma.sigma Y.1.1 (2 + 2 * t)).2 := by
    intro hg_neg
    have hseed2 :=
      rank_one_double_seed_snd_add_two_negative X Y hXY _restAfterDouble
        _hg_rank_one hg_neg _hg_two _hseed1 _hrestAfterDouble_eq
        htail_after_double_three hrestAfterDouble_total
    apply add_two_le_of_window_step
      (fun i => (Sigma.sigma X.1.1 i).2)
      (fun i => (Sigma.sigma Y.1.1 i).2) 2 q₂ hseed2
    intro t ht
    have heven : Even (2 + 2 * t) := ⟨t + 1, by ring⟩
    have hYdrop := case4_Ydrop_snd_strong_even X Y _hseed1 heven
    have hXdrop := hXdouble_window_drop_snd (2 + 2 * t) (by omega) (by omega)
    linarith
  have htail_sigma_eq : ∀ i, 2 * q₂ + 3 ≤ i →
      Sigma.sigma X.1.1 i = Sigma.sigma restAfterType16 i := by
    intro i hi
    have hprime :
        Chromosome.prime^[i] X.1.1 =
          Chromosome.prime^[i] restAfterType16 := by
      rw [prime_iterate_eq_sub_double_single_of_rank_le
        (X := X.1.1) (gm := g) _hg_two (i := i) (by rw [_hg_rank_one]; omega)]
      rw [prime_iterate_eq_sub_single_of_rank_le
        (X := (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 : Chromosome))
        (gm := g₂) (by
          have hne_g_g₂ : g ≠ g₂ := by
            intro hgg₂
            exact _hsame hgg₂.symm
          simp [hne_g_g₂, _hg₂_one]) (by rw [_hg₂_rank_q]; exact hi)]
      rw [← _hrestAfterType16_eq]
    simp [Sigma.sigma, hprime]
  have hXtail_drop_fst :
      (Sigma.sigma X.1.1 (2 * q₂ + 3)).1 -
          (Sigma.sigma X.1.1 (2 * q₂ + 5)).1 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 3 := by
    have hsig_i := htail_sigma_eq (2 * q₂ + 3) (by omega)
    have hsig_i2 := htail_sigma_eq (2 * q₂ + 5) (by omega)
    have hdrop := MixLambdaPi.twostep htail_after_type16_two_step
    have hfst_i := congrArg Prod.fst hsig_i
    have hfst_i2 := congrArg Prod.fst hsig_i2
    rw [hfst_i, hfst_i2, hdrop]
    have hrest_sum :
        restAfterType16.sum (fun _ n => (n : ℚ)) =
          X.1.1.sum (fun _ n => (n : ℚ)) - 3 := by
      have hq :
          restAfterType16.sum (fun _ n => (n : ℚ)) + 3 =
            X.1.1.sum (fun _ n => (n : ℚ)) := by
        exact_mod_cast _htype16_rest_total
      linarith
    have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
    rw [hrest_sum, hD]
  have hXtail_drop_snd :
      (Sigma.sigma X.1.1 (2 * q₂ + 3)).2 -
          (Sigma.sigma X.1.1 (2 * q₂ + 5)).2 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 3 := by
    have hsig_i := htail_sigma_eq (2 * q₂ + 3) (by omega)
    have hsig_i2 := htail_sigma_eq (2 * q₂ + 5) (by omega)
    have hdrop := MixLambdaPi.twostep_snd htail_after_type16_two_step
    have hsnd_i := congrArg Prod.snd hsig_i
    have hsnd_i2 := congrArg Prod.snd hsig_i2
    rw [hsnd_i, hsnd_i2, hdrop]
    have hrest_sum :
        restAfterType16.sum (fun _ n => (n : ℚ)) =
          X.1.1.sum (fun _ n => (n : ℚ)) - 3 := by
      have hq :
          restAfterType16.sum (fun _ n => (n : ℚ)) + 3 =
            X.1.1.sum (fun _ n => (n : ℚ)) := by
        exact_mod_cast _htype16_rest_total
      linarith
    have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
    rw [hrest_sum, hD]
  have hrestAfterType16_from_double :
      restAfterType16 = _restAfterDouble - Finsupp.single g₂ 1 := by
    rw [_hrestAfterType16_eq, _hrestAfterDouble_eq]
  have hrestAfterDouble_decomp :
      Finsupp.single g₂ 1 + restAfterType16 = _restAfterDouble := by
    have h :=
      sub_single_add_single_eq
        (X := _restAfterDouble) (g := g₂) (by rw [_hg₂_rest_one]; norm_num)
    rw [← hrestAfterType16_from_double] at h
    rwa [add_comm] at h
  have hXsucc_drop_fst_of_pos :
      g.type = GeneType.Positive →
        (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 -
            (Sigma.sigma X.1.1 (2 * q₂ + 4)).1 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 3 := by
    intro hg_pos
    have hg₂_neg : g₂.type = GeneType.Negative := by
      rw [_hopp, hg_pos]
      rfl
    have hsig_pred := htail_sigma_double_eq (2 * q₂ + 2) (by omega)
    have hsig_succ := htail_sigma_double_eq (2 * q₂ + 4) (by omega)
    rw [← hrestAfterDouble_decomp, Sigma.sigma_linearity] at hsig_pred hsig_succ
    have hsingle_drop :=
      single_pred_succ_drop_fst_negative _hg₂_rank_q hg₂_neg
    have hrest_drop :
        (Sigma.sigma restAfterType16 (2 * q₂ + 2)).1 -
            (Sigma.sigma restAfterType16 (2 * q₂ + 4)).1 =
          restAfterType16.sum (fun _ n => (n : ℚ)) := by
      have htail :
          ∀ h ∈ restAfterType16.support, (2 * q₂ + 2) + 2 ≤ h.rank := by
        intro h hh
        have := htail_after_type16_two_step h hh
        omega
      simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using
        MixLambdaPi.twostep (W := restAfterType16) (i := 2 * q₂ + 2) htail
    have hpred_fst := congrArg Prod.fst hsig_pred
    have hsucc_fst := congrArg Prod.fst hsig_succ
    simp only [Prod.fst_add] at hpred_fst hsucc_fst
    rw [hpred_fst, hsucc_fst]
    have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
    linarith [hsingle_drop, hrest_drop, hrestAfterType16_sum_cast, hD]
  have hXsucc_drop_snd_of_neg :
      g.type = GeneType.Negative →
        (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 -
            (Sigma.sigma X.1.1 (2 * q₂ + 4)).2 =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 3 := by
    intro hg_neg
    have hg₂_pos : g₂.type = GeneType.Positive := by
      rw [_hopp, hg_neg]
      rfl
    have hsig_pred := htail_sigma_double_eq (2 * q₂ + 2) (by omega)
    have hsig_succ := htail_sigma_double_eq (2 * q₂ + 4) (by omega)
    rw [← hrestAfterDouble_decomp, Sigma.sigma_linearity] at hsig_pred hsig_succ
    have hsingle_drop :=
      single_pred_succ_drop_snd_positive _hg₂_rank_q hg₂_pos
    have hrest_drop :
        (Sigma.sigma restAfterType16 (2 * q₂ + 2)).2 -
            (Sigma.sigma restAfterType16 (2 * q₂ + 4)).2 =
          restAfterType16.sum (fun _ n => (n : ℚ)) := by
      have htail :
          ∀ h ∈ restAfterType16.support, (2 * q₂ + 2) + 2 ≤ h.rank := by
        intro h hh
        have := htail_after_type16_two_step h hh
        omega
      simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using
        MixLambdaPi.twostep_snd (W := restAfterType16) (i := 2 * q₂ + 2) htail
    have hpred_snd := congrArg Prod.snd hsig_pred
    have hsucc_snd := congrArg Prod.snd hsig_succ
    simp only [Prod.snd_add] at hpred_snd hsucc_snd
    rw [hpred_snd, hsucc_snd]
    have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
    linarith [hsingle_drop, hrest_drop, hrestAfterType16_sum_cast, hD]
  have hgap_odd_top :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q₂ + 3] X.1.1) ≤
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
      have hhodd : Odd h.rank := by
        rw [hhrank]
        exact ⟨q₂ + 1, by ring⟩
      have hodd_part : 0 < Y.1.1.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]
        exact hh
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
        (Finsupp.mem_support_iff.mpr hodd_part.ne')
    cases htype : g₂.type with
    | NonPolarized => exact absurd htype _hg₂_pol
    | Positive =>
        have hno_pos : Y.1.1 ⟨2 * q₂ + 3, GeneType.Positive, by omega⟩ = 0 := by
          have htop_eq_g : (⟨2 * q₂ + 3, GeneType.Positive, by omega⟩ : Gene) = g₂ :=
            Gene.ext (by dsimp; rw [_hg₂_rank_q]) htype.symm
          have hle := _hcommon g₂ _hXg₂
          rw [htop_eq_g]
          omega
        have hYfst0 :=
          signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
            (W := Y.1.1) (p := q₂ + 1) hYpol_top hYrank hno_pos
        have hYfst0' : (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1 = 0 := by
          simpa [show 2 * (q₂ + 1) = 2 * q₂ + 2 by omega] using hYfst0
        have hXfst1 :=
          one_le_signature_prime_pred_fst_of_positive (X := X.1.1) (gpos := g₂)
            htype _hXg₂
        have hXfst1' : 1 ≤ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 := by
          simpa [_hg₂_rank_q, show 2 * q₂ + 3 - 1 = 2 * q₂ + 2 by omega] using hXfst1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).1
        linarith
    | Negative =>
        have hno_neg : Y.1.1 ⟨2 * q₂ + 3, GeneType.Negative, by omega⟩ = 0 := by
          have htop_eq_g : (⟨2 * q₂ + 3, GeneType.Negative, by omega⟩ : Gene) = g₂ :=
            Gene.ext (by dsimp; rw [_hg₂_rank_q]) htype.symm
          have hle := _hcommon g₂ _hXg₂
          rw [htop_eq_g]
          omega
        have hYsnd0 :=
          signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
            (W := Y.1.1) (p := q₂ + 1) hYpol_top hYrank hno_neg
        have hYsnd0' : (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2 = 0 := by
          simpa [show 2 * (q₂ + 1) = 2 * q₂ + 2 by omega] using hYsnd0
        have hXsnd1 :=
          one_le_signature_prime_pred_snd_of_negative (X := X.1.1) (gneg := g₂)
            htype _hXg₂
        have hXsnd1' : 1 ≤ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 := by
          simpa [_hg₂_rank_q, show 2 * q₂ + 3 - 1 = 2 * q₂ + 2 by omega] using hXsnd1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).2
        linarith
  have hgap_odd :
      ∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
        ((1 : ℚ), (1 : ℚ)) +
            signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hjodd hj1
    by_cases hjtop : j = 2 * q₂ + 3
    · subst j
      exact hgap_odd_top
    · exact hgap_odd_non_top j hjlo (by omega) hjodd hj1
  have hgap_even :
      ∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → Even j →
        (signature (Gene.ofRank 1 g.type) +
              signature (Gene.ofRank 1 g.type)) +
            signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hjeven
    obtain ⟨s, hs⟩ := hjeven
    subst j
    cases s with
    | zero => omega
    | succ t =>
        have hidx : t + 1 + (t + 1) = 2 + 2 * t := by ring
        have htq : t ≤ q₂ := by omega
        rw [hidx]
        cases hg_type : g.type with
        | NonPolarized => exact absurd hg_type _hg_pol
        | Positive =>
            have hf := hgap_even_pos_fst hg_type t htq
            have hf' :
                (signature (Chromosome.prime^[2 + 2 * t] X.1.1)).1 + 2 ≤
                  (signature (Chromosome.prime^[2 + 2 * t] Y.1.1)).1 := by
              simpa [Sigma.sigma] using hf
            have hdom := (le_iff_dominates.mp hXY.le (2 + 2 * t)).2
            constructor
            · simp [signature_ofRank_one_positive]
              linarith
            · simpa [Sigma.sigma, hg_type, signature_ofRank_one_positive] using hdom
        | Negative =>
            have hsnd := hgap_even_neg_snd hg_type t htq
            have hsnd' :
                (signature (Chromosome.prime^[2 + 2 * t] X.1.1)).2 + 2 ≤
                  (signature (Chromosome.prime^[2 + 2 * t] Y.1.1)).2 := by
              simpa [Sigma.sigma] using hsnd
            have hdom := (le_iff_dominates.mp hXY.le (2 + 2 * t)).1
            constructor
            · simpa [Sigma.sigma, hg_type, signature_ofRank_one_negative] using hdom
            · simp [signature_ofRank_one_negative]
              linarith
  refine ⟨hgap_odd, hgap_even, ?_⟩
  cases hg_type : g.type with
  | NonPolarized => exact False.elim (_hg_pol hg_type)
  | Positive =>
      have hpred := hgap_even_pos_fst hg_type q₂ (le_refl q₂)
      have hpred' :
          (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 + 2 ≤
            (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 := by
        simpa [show 2 + 2 * q₂ = 2 * q₂ + 2 by omega] using hpred
      have hYdrop :=
        case4_Ydrop_fst_strong_even X Y _hseed1 (i := 2 * q₂ + 2)
          ⟨q₂ + 1, by ring⟩
      have hXdrop := hXsucc_drop_fst_of_pos hg_type
      have hsucc :
          (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).1 <
            (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).1 := by
        have hYdrop' :
            (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 -
                (Sigma.sigma Y.1.1 (2 * q₂ + 4)).1 ≤
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
          simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hYdrop
        simpa [Sigma.sigma] using (by
          linarith [hpred'] : (Sigma.sigma X.1.1 (2 * q₂ + 4)).1 <
            (Sigma.sigma Y.1.1 (2 * q₂ + 4)).1)
      simpa [hg_type, show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using
        type16_succ_gap_positive X Y hXY (p := q₂ + 1)
          (by simpa [show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using hsucc)
  | Negative =>
      have hpred := hgap_even_neg_snd hg_type q₂ (le_refl q₂)
      have hpred' :
          (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 + 2 ≤
            (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 := by
        simpa [show 2 + 2 * q₂ = 2 * q₂ + 2 by omega] using hpred
      have hYdrop :=
        case4_Ydrop_snd_strong_even X Y _hseed1 (i := 2 * q₂ + 2)
          ⟨q₂ + 1, by ring⟩
      have hXdrop := hXsucc_drop_snd_of_neg hg_type
      have hsucc :
          (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).2 <
            (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).2 := by
        have hYdrop' :
            (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 -
                (Sigma.sigma Y.1.1 (2 * q₂ + 4)).2 ≤
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
          simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hYdrop
        simpa [Sigma.sigma] using (by
          linarith [hpred'] : (Sigma.sigma X.1.1 (2 * q₂ + 4)).2 <
            (Sigma.sigma Y.1.1 (2 * q₂ + 4)).2)
      simpa [hg_type, show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using
        type16_succ_gap_negative X Y hXY (p := q₂ + 1)
          (by simpa [show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using hsucc)

lemma exists_mutation_le_no_pair_rank_one_double
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
  · exact rank_one_double_same_gene_extra X Y hXY hcommon h17_1 hXpol
      hno_pair g g₂ hgX hgmin hg_pol hp hp0 hg_rank_one hXneg_zero
      hg_two hseed1 hXsig1_eq hYsig1_eq hgap1 restAfterDouble rfl
      hrestAfterDouble_ne hrestAfterDouble_mem hprimeX_eq_restAfterDouble
      hrestAfterDouble_total hg₂_rest hg₂min hXg₂ hg₂_pol hg₂_odd
      hX_rank_ge_three_of_ne_g hg₂min_X_ne_g hg₂_same_extra
      hg₂_rank_ge_three_of_ne_g htype16_boundary htype14_boundary hsame
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
    have hrestAfterDouble_g₂_eq_X : restAfterDouble g₂ = X.1.1 g₂ := by
      dsimp [restAfterDouble]
      simp [hsame]
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
        have hcandidate :=
          htype14_boundary (q := q₂ + 1) g₂ hopp
            (by rw [hg₂_rank_q]; omega) hg₂_two
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
          convert h using 2
          omega
        have hX14val :
            (X14 (Nat.zero_le (q₂ + 1)) hg_pol).1 =
              Finsupp.single g 1 + Finsupp.single g 1 +
                Finsupp.single g₂ 1 + Finsupp.single g₂ 1 := by
          rw [X14_eq, hg_eq, hg₂_eq]
        have hXeq_type14 :
            (X14 (Nat.zero_le (q₂ + 1)) hg_pol).1 + restAfterType14 =
              X.1.1 := by
          rw [hX14val]
          dsimp [restAfterType14, restAfterDouble]
          exact Mix2LambdaSection17.double_pair_add_rest
            hg_two hg₂_two hne_g_g₂
        have hgap_middle :
            (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
              ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[j] X.1.1) ≤
                signature (Chromosome.prime^[j] Y.1.1)) ∧
            (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → Even j →
              (signature (Gene.ofRank 1 g.type) +
                    signature (Gene.ofRank 1 g.type)) +
                  signature (Chromosome.prime^[j] X.1.1) ≤
                signature (Chromosome.prime^[j] Y.1.1)) :=
          rank_one_double_middle_gap_pack X Y hXY hcommon h17_1
            g g₂ hg_pol hg_rank_one hg_two hseed1 restAfterDouble
            hXg₂ hg₂_pol hg₂_rank_q htail_after_double rfl
        have hgap_odd :
            ∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j →
              ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[j] X.1.1) ≤
                signature (Chromosome.prime^[j] Y.1.1) := by
          intro j hjlo hjhi hjodd
          by_cases hj1 : j = 1
          · subst j
            simpa using hgap1
          · exact hgap_middle.1 j hjlo hjhi hjodd hj1
        have hZle14 :
            (Y14 (Nat.zero_le (q₂ + 1)) hg_pol).1 + restAfterType14 ≤
              Y.1.1 :=
          Mix2LambdaPi.type14_rank_one_target_add_rest_le_of_gaps hg_pol X Y hXY
            restAfterType14 hXeq_type14 hgap_odd hgap_middle.2
        exact hcandidate (by
          simpa [hrestAfterType14_eq] using hZle14)
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
          convert h using 2
          omega
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
            htail_after_double rfl hrestAfterType16_eq hg₂_rest_one
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
      have hg₂_same_type : g₂.type = g.type :=
        polarized_same_type_of_not_neg hg_pol hg₂_pol hopp
      have hXneg_g₂_zero : X.1.1 (-g₂) = 0 :=
        no_pair_neg_gene_zero hno_pair hg₂_pol hXg₂
      have hneg_g₂_ne_g : -g₂ ≠ g := by
        intro h
        have hr : g₂.rank = g.rank := by
          rw [← Gene.neg_rank g₂, h]
        rw [hg₂_rank_q, hg_rank_one] at hr
        omega
      have hrestAfterDouble_neg_g₂_zero : restAfterDouble (-g₂) = 0 := by
        dsimp [restAfterDouble]
        rw [hXneg_g₂_zero]
        simp [hneg_g₂_ne_g]
      have hg₂_single_or_double : X.1.1 g₂ = 1 ∨ 2 ≤ X.1.1 g₂ := by
        omega
      have htail_after_double_same :
          ∀ h ∈ restAfterDouble.support, 2 * q₂ + 3 ≤ h.rank := by
        intro h hh
        have hhpos : 0 < restAfterDouble h :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
        have hle := hg₂min h hhpos
        rwa [hg₂_rank_q] at hle
      have hgap_middle_same :
          (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
            ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] X.1.1) ≤
              signature (Chromosome.prime^[j] Y.1.1)) ∧
          (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → Even j →
            (signature (Gene.ofRank 1 g.type) +
                  signature (Gene.ofRank 1 g.type)) +
                signature (Chromosome.prime^[j] X.1.1) ≤
              signature (Chromosome.prime^[j] Y.1.1)) :=
        rank_one_double_middle_gap_pack X Y hXY hcommon h17_1
          g g₂ hg_pol hg_rank_one hg_two hseed1 restAfterDouble
          hXg₂ hg₂_pol hg₂_rank_q htail_after_double_same rfl
      have htype10_same_double_boundary :
          2 ≤ X.1.1 g₂ →
            (Y10 (le_refl q₂) hg₂_pol hg₂_pol).1 +
                (X.1.1 - Finsupp.single g₂ 1 - Finsupp.single g₂ 1) ≤
              Y.1.1 →
            ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
        intro hg₂_two hZle
        exact exists_mutation_le_type10_of_double (ε := g₂.type) hg₂_pol
          X Y g₂ rfl hg₂_rank_q hg₂_two hZle
      have hgap_mid_same_double :
          ∀ j, 2 * q₂ + 3 ≤ j → j ≤ 2 * q₂ + 3 →
            ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] X.1.1) ≤
              signature (Chromosome.prime^[j] Y.1.1) := by
        intro j hjlo hjhi
        have hj : j = 2 * q₂ + 3 := by omega
        subst j
        exact hgap_middle_same.1 (2 * q₂ + 3) (by omega) (by omega)
          (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by ring⟩) (by omega)
      have hgap_pred_even_same :
          (signature (Gene.ofRank 1 g₂.type) +
                signature (Gene.ofRank 1 g₂.type)) +
              signature (Chromosome.prime^[2 * q₂ + 2] X.1.1) ≤
            signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1) := by
        simpa [hg₂_same_type] using
          hgap_middle_same.2 (2 * q₂ + 2) (by omega) (by omega)
            ⟨q₂ + 1, by ring⟩
      have hgap_succ_same_double :
          signature (Gene.ofRank 1 g₂.type) +
              signature (Chromosome.prime^[2 * q₂ + 4] X.1.1) ≤
            signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1) := by
        cases htype : g₂.type with
        | NonPolarized => exact False.elim (hg₂_pol htype)
        | Positive =>
            simpa [htype, show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using
              type16_succ_gap_positive X Y hXY (p := q₂ + 1) (by
                have hWpos :
                    ∀ z ∈ (Chromosome.prime^[2 * q₂ + 1] X.1.1).support,
                      2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
                  intro z hz
                  have hzpos : 0 < (Chromosome.prime^[2 * q₂ + 1] X.1.1) z :=
                    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
                  let z0 : Gene :=
                    ⟨z.rank + (2 * q₂ + 1), z.type,
                      Nat.le_add_right_of_le z.rank_pos⟩
                  have hz0X : 0 < X.1.1 z0 := by
                    have hcoeff := prime_iterate_coeff (2 * q₂ + 1) X.1.1 z
                    change (Chromosome.prime^[2 * q₂ + 1] X.1.1) z =
                      X.1.1 z0 at hcoeff
                    rwa [← hcoeff]
                  have hz0_ne_g : z0 ≠ g := by
                    intro hzg
                    have hrank := congrArg Gene.rank hzg
                    dsimp [z0] at hrank
                    rw [hg_rank_one] at hrank
                    have zpos := z.rank_pos
                    omega
                  have hz0_rest : 0 < restAfterDouble z0 := by
                    dsimp [restAfterDouble]
                    simp [hz0_ne_g.symm, hz0X]
                  have hz0_rank_le :=
                    htail_after_double_same z0
                      (Finsupp.mem_support_iff.mpr (ne_of_gt hz0_rest))
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
                    | Positive => rfl
                    | Negative =>
                        have hz0_eq_neg : z0 = -g₂ := by
                          apply Gene.ext
                          · rw [Gene.neg_rank]
                            exact hz0_rank_eq
                          · rw [Gene.neg_type, htype]
                            simpa [z0] using hz_type
                        have hz0_zero : restAfterDouble z0 = 0 := by
                          rw [hz0_eq_neg]
                          exact hrestAfterDouble_neg_g₂_zero
                        omega
                have hXdrop_raw :=
                  edge_drop_fst_eq_totalMult_positive_iterate
                    (W := X.1.1) (i := 2 * q₂ + 1) hWpos
                have hWsum_nat :
                    (Chromosome.prime^[2 * q₂ + 1] X.1.1).sum (fun _ n => n) =
                      restAfterDouble.sum (fun _ n => n) := by
                  rw [prime_iterate_eq_sub_double_single_of_rank_le
                    (X := X.1.1) (gm := g) hg_two (by
                      rw [hg_rank_one]
                      omega)]
                  exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
                    restAfterDouble (2 * q₂ + 1) (by
                      intro h hh
                      have hle := htail_after_double_same h hh
                      omega)
                have hWsum := totalMult_cast_eq_of_nat_eq hWsum_nat
                have hrest := totalMult_cast_eq_sub_two_of_nat_add_two hrestAfterDouble_total
                have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
                have hXdrop :
                    (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 -
                        (Sigma.sigma X.1.1 (2 * q₂ + 4)).1 =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
                  rw [show 1 + (2 * q₂ + 1) = 2 * q₂ + 2 by omega,
                    show 3 + (2 * q₂ + 1) = 2 * q₂ + 4 by omega] at hXdrop_raw
                  linarith
                have hYdrop :=
                  KEY_Y_fst X Y hr1 (i := 2 * q₂ + 2) ⟨q₂ + 1, by ring⟩
                have htop :
                    (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 + 2 ≤
                      (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 := by
                  have h := hgap_pred_even_same.1
                  have h' :
                      1 + 1 + (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 ≤
                        (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 := by
                    simpa [Sigma.sigma, htype, signature_ofRank_one_positive] using h
                  linarith
                have hsucc :
                    (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).1 <
                      (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).1 := by
                  have hYdrop' :
                      (Sigma.sigma Y.1.1 (2 * q₂ + 2)).1 -
                          (Sigma.sigma Y.1.1 (2 * q₂ + 4)).1 ≤
                        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
                    simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hYdrop
                  simpa [Sigma.sigma] using (by
                    linarith : (Sigma.sigma X.1.1 (2 * q₂ + 4)).1 <
                      (Sigma.sigma Y.1.1 (2 * q₂ + 4)).1)
                simpa [show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using hsucc)
        | Negative =>
            simpa [htype, show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using
              type16_succ_gap_negative X Y hXY (p := q₂ + 1) (by
                have hWneg :
                    ∀ z ∈ (Chromosome.prime^[2 * q₂ + 1] X.1.1).support,
                      2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
                  intro z hz
                  have hzpos : 0 < (Chromosome.prime^[2 * q₂ + 1] X.1.1) z :=
                    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
                  let z0 : Gene :=
                    ⟨z.rank + (2 * q₂ + 1), z.type,
                      Nat.le_add_right_of_le z.rank_pos⟩
                  have hz0X : 0 < X.1.1 z0 := by
                    have hcoeff := prime_iterate_coeff (2 * q₂ + 1) X.1.1 z
                    change (Chromosome.prime^[2 * q₂ + 1] X.1.1) z =
                      X.1.1 z0 at hcoeff
                    rwa [← hcoeff]
                  have hz0_ne_g : z0 ≠ g := by
                    intro hzg
                    have hrank := congrArg Gene.rank hzg
                    dsimp [z0] at hrank
                    rw [hg_rank_one] at hrank
                    have zpos := z.rank_pos
                    omega
                  have hz0_rest : 0 < restAfterDouble z0 := by
                    dsimp [restAfterDouble]
                    simp [hz0_ne_g.symm, hz0X]
                  have hz0_rank_le :=
                    htail_after_double_same z0
                      (Finsupp.mem_support_iff.mpr (ne_of_gt hz0_rest))
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
                        have hz0_eq_neg : z0 = -g₂ := by
                          apply Gene.ext
                          · rw [Gene.neg_rank]
                            exact hz0_rank_eq
                          · rw [Gene.neg_type, htype]
                            simpa [z0] using hz_type
                        have hz0_zero : restAfterDouble z0 = 0 := by
                          rw [hz0_eq_neg]
                          exact hrestAfterDouble_neg_g₂_zero
                        omega
                    | Negative => rfl
                have hXdrop_raw :=
                  edge_drop_snd_eq_totalMult_negative_iterate
                    (W := X.1.1) (i := 2 * q₂ + 1) hWneg
                have hWsum_nat :
                    (Chromosome.prime^[2 * q₂ + 1] X.1.1).sum (fun _ n => n) =
                      restAfterDouble.sum (fun _ n => n) := by
                  rw [prime_iterate_eq_sub_double_single_of_rank_le
                    (X := X.1.1) (gm := g) hg_two (by
                      rw [hg_rank_one]
                      omega)]
                  exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
                    restAfterDouble (2 * q₂ + 1) (by
                      intro h hh
                      have hle := htail_after_double_same h hh
                      omega)
                have hWsum := totalMult_cast_eq_of_nat_eq hWsum_nat
                have hrest := totalMult_cast_eq_sub_two_of_nat_add_two hrestAfterDouble_total
                have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
                have hXdrop :
                    (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 -
                        (Sigma.sigma X.1.1 (2 * q₂ + 4)).2 =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
                  rw [show 1 + (2 * q₂ + 1) = 2 * q₂ + 2 by omega,
                    show 3 + (2 * q₂ + 1) = 2 * q₂ + 4 by omega] at hXdrop_raw
                  linarith
                have hYdrop :=
                  KEY_Y_snd X Y hr1 (i := 2 * q₂ + 2) ⟨q₂ + 1, by ring⟩
                have htop :
                    (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 + 2 ≤
                      (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 := by
                  have h := hgap_pred_even_same.2
                  have h' :
                      1 + 1 + (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 ≤
                        (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 := by
                    simpa [Sigma.sigma, htype, signature_ofRank_one_negative] using h
                  linarith
                have hsucc :
                    (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).2 <
                      (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).2 := by
                  have hYdrop' :
                      (Sigma.sigma Y.1.1 (2 * q₂ + 2)).2 -
                          (Sigma.sigma Y.1.1 (2 * q₂ + 4)).2 ≤
                        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
                    simpa [show 2 * q₂ + 2 + 2 = 2 * q₂ + 4 by omega] using hYdrop
                  simpa [Sigma.sigma] using (by
                    linarith : (Sigma.sigma X.1.1 (2 * q₂ + 4)).2 <
                      (Sigma.sigma Y.1.1 (2 * q₂ + 4)).2)
                simpa [show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using hsucc)
      have htype10_same_double_of_gaps :
          2 ≤ X.1.1 g₂ →
            (((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[2 * q₂ + 2] X.1.1) ≤
              signature (Gene.ofRank 1 g₂.type) +
                signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)) →
            (signature (Gene.ofRank 1 g₂.type) +
                signature (Chromosome.prime^[2 * q₂ + 4] X.1.1) ≤
              signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)) →
            ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
        intro hg₂_two hgap_pred hgap_succ
        have hZle :
            (Y10 (le_refl q₂) hg₂_pol hg₂_pol).1 +
                (X.1.1 - Finsupp.single g₂ 1 - Finsupp.single g₂ 1) ≤
              Y.1.1 :=
          type10_double_target_add_rest_le_of_gaps hg₂_pol X Y hXY
            g₂ rfl hg₂_rank_q hg₂_two hgap_pred hgap_mid_same_double
            hgap_succ
        exact htype10_same_double_boundary hg₂_two hZle
      have htype10_same_double_of_pred_gap :
          2 ≤ X.1.1 g₂ →
            (((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[2 * q₂ + 2] X.1.1) ≤
              signature (Gene.ofRank 1 g₂.type) +
                signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)) →
            ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
        intro hg₂_two hgap_pred
        exact htype10_same_double_of_gaps hg₂_two hgap_pred hgap_succ_same_double
      have hYpred_same_double_ne :
          Chromosome.prime^[2 * q₂ + 2] Y.1.1 ≠ 0 := by
        intro hYzero
        have hYsig :
            signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1) = 0 := by
          rw [hYzero, map_zero]
        cases htype : g₂.type with
        | NonPolarized => exact False.elim (hg₂_pol htype)
        | Positive =>
            have h := hgap_pred_even_same.1
            have hxnonneg :
                (0 : ℚ) ≤
                  (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 :=
              (signature_nonneg (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1
            rw [hYsig] at h
            simp only [htype, signature_ofRank_one_positive, Prod.mk_add_mk, add_zero,
              Function.iterate_succ, Function.comp_apply, Prod.fst_add, Prod.fst_zero] at h
            have hxnonneg' :
                (0 : ℚ) ≤
                  (signature
                    (Chromosome.prime^[2 * q₂]
                      (Chromosome.prime (Chromosome.prime X.1.1)))).1 :=
              (signature_nonneg _).1
            linarith
        | Negative =>
            have h := hgap_pred_even_same.2
            have hxnonneg :
                (0 : ℚ) ≤
                  (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 :=
              (signature_nonneg (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2
            rw [hYsig] at h
            simp only [htype, signature_ofRank_one_negative, Prod.mk_add_mk, add_zero,
              Function.iterate_succ, Function.comp_apply, Prod.snd_add, Prod.snd_zero] at h
            have hxnonneg' :
                (0 : ℚ) ≤
                  (signature
                    (Chromosome.prime^[2 * q₂]
                      (Chromosome.prime (Chromosome.prime X.1.1)))).2 :=
              (signature_nonneg _).2
            linarith
      have htype10_same_double_of_wrong_pred :
          2 ≤ X.1.1 g₂ →
            ((g₂.type = GeneType.Positive ∧
                (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2) ∨
              (g₂.type = GeneType.Negative ∧
                (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1)) →
            ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
        intro hg₂_two hwrong
        rcases hwrong with ⟨htype, hsnd⟩ | ⟨htype, hfst⟩
        · exact htype10_same_double_of_pred_gap hg₂_two (by
            simpa [htype] using type10_pred_gap_positive X Y hXY (p := q₂) hsnd)
        · exact htype10_same_double_of_pred_gap hg₂_two (by
            simpa [htype] using type10_pred_gap_negative X Y hXY (p := q₂) hfst)
      have hpred_same_double_split :
          (g₂.type = GeneType.Positive ∧
              ((signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2 ∨
                (¬ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 <
                    (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2 ∧
                  (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 <
                    (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1))) ∨
            (g₂.type = GeneType.Negative ∧
              ((signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1 ∨
                (¬ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 <
                    (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1 ∧
                  (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 <
                    (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2))) := by
        cases htype : g₂.type with
        | NonPolarized => exact False.elim (hg₂_pol htype)
        | Positive =>
            exact Or.inl ⟨rfl,
              prime_iterate_snd_or_fst_lt X Y hXY h17_1
                (k := 2 * q₂ + 2) (by omega) hYpred_same_double_ne⟩
        | Negative =>
            exact Or.inr ⟨rfl,
              prime_iterate_fst_or_snd_lt X Y hXY h17_1
                (k := 2 * q₂ + 2) (by omega) hYpred_same_double_ne⟩
      have hdouble_same_pred_or_done :
          2 ≤ X.1.1 g₂ →
            (∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∨
              (g₂.type = GeneType.Positive ∧
                (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1) ∨
              (g₂.type = GeneType.Negative ∧
                (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2) := by
        intro hg₂_two
        rcases hpred_same_double_split with ⟨htype, hsnd_or_fst⟩ | ⟨htype, hfst_or_snd⟩
        · rcases hsnd_or_fst with hsnd | ⟨_hnsnd, hfst⟩
          · exact Or.inl
              (htype10_same_double_of_wrong_pred hg₂_two (Or.inl ⟨htype, hsnd⟩))
          · exact Or.inr (Or.inl ⟨htype, hfst⟩)
        · rcases hfst_or_snd with hfst | ⟨_hnfst, hsnd⟩
          · exact Or.inl
              (htype10_same_double_of_wrong_pred hg₂_two (Or.inr ⟨htype, hfst⟩))
          · exact Or.inr (Or.inr ⟨htype, hsnd⟩)
      suffices hremaining :
          (X.1.1 g₂ = 1 →
            ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∧
          (2 ≤ X.1.1 g₂ → g₂.type = GeneType.Positive →
            (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1 →
            ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∧
          (2 ≤ X.1.1 g₂ → g₂.type = GeneType.Negative →
            (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2 →
            ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) by
        rcases hg₂_single_or_double with hg₂_one | hg₂_two
        · exact hremaining.1 hg₂_one
        · rcases hdouble_same_pred_or_done hg₂_two with hdone | hfallback
          · exact hdone
          · rcases hfallback with ⟨hpos, hfst⟩ | ⟨hneg, hsnd⟩
            · exact hremaining.2.1 hg₂_two hpos hfst
            · exact hremaining.2.2 hg₂_two hneg hsnd
      exact rank_one_double_same_sign_remaining X Y hXY hcommon h17_1
        hXpol hno_pair g g₂ hgX hgmin hg_pol hp hp0 hg_rank_one
        hXneg_zero hg_two hseed1 restAfterDouble rfl hrestAfterDouble_ne
        hrestAfterDouble_total hg₂_rest hg₂min hXg₂ hg₂_pol hsame
        hg₂_rank_q hopp hg₂_same_type hXneg_g₂_zero
        hrestAfterDouble_g₂_eq_X hrestAfterDouble_neg_g₂_zero
        htail_after_double_same hgap_middle_same hgap_pred_even_same
        hgap_succ_same_double htype10_same_double_of_pred_gap
        hdouble_same_pred_or_done


end Mix2LambdaPi
