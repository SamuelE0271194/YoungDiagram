import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleContinuation

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Opposite-sign Case 2 windows

These are the Label 4 parity mirrors of the negative-partner counting engine
for Label 3.  The selected gene is minimal only among opposite-sign genes.
-/

/-- Telescoped mixed-variety bound used by the positive-sign Case 2 window. -/
lemma case2_a1_ai_le_b0_bi
    {Y : Chromosome} (hY : Y ∈ Mix (Pi, 2 • Lambda))
    {i : ℕ} (hi : 1 ≤ i) :
    (Sigma.sigma Y 0).2 - (Sigma.sigma Y (i - 1)).2 ≥
      (Sigma.sigma Y 1).1 - (Sigma.sigma Y i).1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction j with
  | zero => simp
  | succ j ih =>
      induction j with
      | zero =>
          have h := Mix2LambdaSection17.cond_15_7_Mix_Pi_2Lambda hY 0
          rw [if_pos (by decide : Even 0)] at h
          simpa using h
      | succ j _ =>
          by_cases heven : Even (j + 2)
          · have hprev : ¬ Even (j + 1) := Nat.even_add_one.mp heven
            have hstep :
                (Sigma.sigma Y (j + 1)).2 - (Sigma.sigma Y (j + 2)).2 ≥
                  (Sigma.sigma Y (j + 2)).1 - (Sigma.sigma Y (j + 3)).1 := by
              have h :=
                Mix2LambdaSection17.cond_15_6_Mix_Pi_2Lambda hY (j + 1)
              rw [if_neg hprev] at h
              simpa using h
            have ih' := ih (by omega)
            simp only [show 1 + (j + 1) = j + 2 by omega,
              show j + 2 - 1 = j + 1 by omega] at ih'
            simp only [show 1 + (j + 1 + 1) = j + 3 by omega,
              show j + 3 - 1 = j + 2 by omega]
            linarith
          · have hprev : Even (j + 1) := by
              rwa [Nat.even_add_one, not_not] at heven
            have hstep :
                (Sigma.sigma Y (j + 1)).2 - (Sigma.sigma Y (j + 2)).2 ≥
                  (Sigma.sigma Y (j + 2)).1 - (Sigma.sigma Y (j + 3)).1 := by
              have h :=
                Mix2LambdaSection17.cond_15_7_Mix_Pi_2Lambda hY (j + 1)
              rw [if_pos hprev] at h
              simpa using h
            have ih' := ih (by omega)
            simp only [show 1 + (j + 1) = j + 2 by omega,
              show j + 2 - 1 = j + 1 by omega] at ih'
            simp only [show 1 + (j + 1 + 1) = j + 3 by omega,
              show j + 3 - 1 = j + 2 by omega]
            linarith

/-- Column-swapped telescoped bound for the negative normalization. -/
lemma case2_b1_bi_le_a0_ai
    {Y : Chromosome} (hY : Y ∈ Mix (Pi, 2 • Lambda))
    {i : ℕ} (hi : 1 ≤ i) :
    (Sigma.sigma Y 0).1 - (Sigma.sigma Y (i - 1)).1 ≥
      (Sigma.sigma Y 1).2 - (Sigma.sigma Y i).2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction j with
  | zero => simp
  | succ j ih =>
      induction j with
      | zero =>
          have h := Mix2LambdaSection17.cond_15_6_Mix_Pi_2Lambda hY 0
          rw [if_pos (by decide : Even 0)] at h
          simpa using h
      | succ j _ =>
          by_cases heven : Even (j + 2)
          · have hprev : ¬ Even (j + 1) := Nat.even_add_one.mp heven
            have hstep :
                (Sigma.sigma Y (j + 1)).1 - (Sigma.sigma Y (j + 2)).1 ≥
                  (Sigma.sigma Y (j + 2)).2 - (Sigma.sigma Y (j + 3)).2 := by
              have h :=
                Mix2LambdaSection17.cond_15_7_Mix_Pi_2Lambda hY (j + 1)
              rw [if_neg hprev] at h
              simpa using h
            have ih' := ih (by omega)
            simp only [show 1 + (j + 1) = j + 2 by omega,
              show j + 2 - 1 = j + 1 by omega] at ih'
            simp only [show 1 + (j + 1 + 1) = j + 3 by omega,
              show j + 3 - 1 = j + 2 by omega]
            linarith
          · have hprev : Even (j + 1) := by
              rwa [Nat.even_add_one, not_not] at heven
            have hstep :
                (Sigma.sigma Y (j + 1)).1 - (Sigma.sigma Y (j + 2)).1 ≥
                  (Sigma.sigma Y (j + 2)).2 - (Sigma.sigma Y (j + 3)).2 := by
              have h :=
                Mix2LambdaSection17.cond_15_6_Mix_Pi_2Lambda hY (j + 1)
              rw [if_pos hprev] at h
              simpa using h
            have ih' := ih (by omega)
            simp only [show 1 + (j + 1) = j + 2 by omega,
              show j + 2 - 1 = j + 1 by omega] at ih'
            simp only [show 1 + (j + 1 + 1) = j + 3 by omega,
              show j + 3 - 1 = j + 2 by omega]
            linarith

/-- Negative-family mirror of `Sigma.b0_bi_eq_a1_ai1`. -/
lemma case2_x_negative_identity
    {X : Chromosome} (hX : X ∈ Variety.Pi) (i : ℕ)
    (hneg : ∀ g ∈ X.support, g.rank ≤ i → g.type = GeneType.Negative) :
    (Sigma.sigma X 0).1 - (Sigma.sigma X i).1 =
      (Sigma.sigma X 1).2 - (Sigma.sigma X (i + 1)).2 := by
  have hnegX : (-X) ∈ Variety.Pi :=
    Variety.mem_Pi_iff.mpr
      (Chromosome.IsPolarized_iff_neg_polarized.mp
        (Variety.mem_Pi_iff.mp hX))
  have hpos : ∀ g ∈ (-X).support, g.rank ≤ i →
      g.type = GeneType.Positive := by
    intro g hg hrank
    rw [Finsupp.mem_support_iff, Chromosome.neg_apply] at hg
    have hXg : -g ∈ X.support := Finsupp.mem_support_iff.mpr hg
    have ht := hneg (-g) hXg (by rwa [Gene.neg_rank])
    have : -g.type = GeneType.Negative := by
      rw [← Gene.neg_type]
      exact ht
    cases hgt : g.type <;> simp_all
  have h := Sigma.b0_bi_eq_a1_ai1 (-X) hnegX i hpos
  simp only [Sigma.sigma, ← Chromosome.prime_iterate_neg, signature_neg,
    Prod.snd_swap, Prod.fst_swap] at h
  exact h

/-- Positive normalization: before the minimum negative rank, every odd level
has the two-cell first-component gap required by Type15/17. -/
lemma case2_positive_odd_gap
    {m i : ℕ} (X Y : nMixPi2Lambda (m + 2)) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hi_odd : ¬ Even i) (hi3 : 3 ≤ i)
    (hpos : ∀ g ∈ X.1.1.support, g.rank ≤ i - 1 →
      g.type = GeneType.Positive)
    (hfst1 : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (hYi1 : Chromosome.prime^[i - 1] Y.1.1 ≠ 0) :
    (Sigma.sigma X.1.1 i).1 + 2 ≤ (Sigma.sigma Y.1.1 i).1 := by
  have hi1_even : Even (i - 1) := by
    obtain ⟨q, hq⟩ := Nat.not_even_iff_odd.mp hi_odd
    exact ⟨q, by omega⟩
  have hXbob := Sigma.b0_bi_eq_a1_ai1 X.1.1 hXPi (i - 1) hpos
  rw [show i - 1 + 1 = i by omega] at hXbob
  have hYbob := case2_a1_ai_le_b0_bi Y.1.2 (i := i) (by omega)
  have h0 := sigma_zero_eq X Y hXY
  have h0b : (Sigma.sigma X.1.1 0).2 = (Sigma.sigma Y.1.1 0).2 :=
    congrArg Prod.snd h0
  have hgap1 := type15_pred_gap_positive X Y hXY (j := 1) (by decide) hfst1
  have hg1f :
      (1 : ℚ) + (Sigma.sigma X.1.1 1).1 ≤
        (Sigma.sigma Y.1.1 1).1 := by
    simpa [Sigma.sigma, signature_ofRank_one_positive] using hgap1.1
  have hgapi1 := type10_mid_gap_even_of_Y_ne X Y h17_1 hi1_even
    (by omega) hYi1
  have hgi1s :
      (1 : ℚ) + (Sigma.sigma X.1.1 (i - 1)).2 ≤
        (Sigma.sigma Y.1.1 (i - 1)).2 := by
    simpa [Sigma.sigma] using hgapi1.2
  linarith

/-- Negative normalization: before the minimum positive rank, every odd level
has the two-cell second-component gap required by Type15/17. -/
lemma case2_negative_odd_gap
    {m i : ℕ} (X Y : nMixPi2Lambda (m + 2)) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hi_odd : ¬ Even i) (hi3 : 3 ≤ i)
    (hneg : ∀ g ∈ X.1.1.support, g.rank ≤ i - 1 →
      g.type = GeneType.Negative)
    (hsnd1 : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2)
    (hYi1 : Chromosome.prime^[i - 1] Y.1.1 ≠ 0) :
    (Sigma.sigma X.1.1 i).2 + 2 ≤ (Sigma.sigma Y.1.1 i).2 := by
  have hi1_even : Even (i - 1) := by
    obtain ⟨q, hq⟩ := Nat.not_even_iff_odd.mp hi_odd
    exact ⟨q, by omega⟩
  have hXaoa := case2_x_negative_identity hXPi (i - 1) hneg
  rw [show i - 1 + 1 = i by omega] at hXaoa
  have hYaoa := case2_b1_bi_le_a0_ai Y.1.2 (i := i) (by omega)
  have h0 := sigma_zero_eq X Y hXY
  have h0a : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 :=
    congrArg Prod.fst h0
  have hgap1 := type15_pred_gap_negative X Y hXY (j := 1) (by decide) hsnd1
  have hg1s :
      (1 : ℚ) + (Sigma.sigma X.1.1 1).2 ≤
        (Sigma.sigma Y.1.1 1).2 := by
    simpa [Sigma.sigma, signature_ofRank_one_negative] using hgap1.2
  have hgapi1 := type10_mid_gap_even_of_Y_ne X Y h17_1 hi1_even
    (by omega) hYi1
  have hgi1f :
      (1 : ℚ) + (Sigma.sigma X.1.1 (i - 1)).1 ≤
        (Sigma.sigma Y.1.1 (i - 1)).1 := by
    simpa [Sigma.sigma] using hgapi1.1
  linarith

/-- The positive Case 2 odd window needs minimality only among negative genes. -/
lemma case2_positive_odd_gap_before_min_opposite
    {m i : ℕ} (X Y : nMixPi2Lambda (m + 2)) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g g₂ : Gene) (hg_pos : g.type = GeneType.Positive)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg₂min : ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h →
      g₂.rank ≤ h.rank)
    (hi_odd : ¬ Even i) (hi3 : 3 ≤ i) (hi₂ : i < g₂.rank)
    (hfst1 : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1) :
    (Sigma.sigma X.1.1 i).1 + 2 ≤ (Sigma.sigma Y.1.1 i).1 := by
  have hXpol := Variety.mem_Pi_iff.mp hXPi
  have hpos : ∀ h ∈ X.1.1.support, h.rank ≤ i - 1 →
      h.type = GeneType.Positive := by
    intro h hh hrank
    have hpol := Chromosome.IsPolarized_def'.mp hXpol h hh
    cases ht : h.type with
    | NonPolarized => exact False.elim (hpol ht)
    | Positive => rfl
    | Negative =>
        have hop : h.type = -g.type := by simp [ht, hg_pos]
        have := hg₂min h hop (Finsupp.mem_support_iff.mp hh).bot_lt
        omega
  exact case2_positive_odd_gap X Y hXY hXPi h17_1 hi_odd hi3 hpos
    hfst1 (no_pair_rank_two_single_Y_iterate_ne_before_second_rank
      X Y hXY g₂ hXg₂ (by omega))

/-- The negative Case 2 odd window needs minimality only among positive genes. -/
lemma case2_negative_odd_gap_before_min_opposite
    {m i : ℕ} (X Y : nMixPi2Lambda (m + 2)) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g g₂ : Gene) (hg_neg : g.type = GeneType.Negative)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg₂min : ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h →
      g₂.rank ≤ h.rank)
    (hi_odd : ¬ Even i) (hi3 : 3 ≤ i) (hi₂ : i < g₂.rank)
    (hsnd1 : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2) :
    (Sigma.sigma X.1.1 i).2 + 2 ≤ (Sigma.sigma Y.1.1 i).2 := by
  have hXpol := Variety.mem_Pi_iff.mp hXPi
  have hneg : ∀ h ∈ X.1.1.support, h.rank ≤ i - 1 →
      h.type = GeneType.Negative := by
    intro h hh hrank
    have hpol := Chromosome.IsPolarized_def'.mp hXpol h hh
    cases ht : h.type with
    | NonPolarized => exact False.elim (hpol ht)
    | Positive =>
        have hop : h.type = -g.type := by simp [ht, hg_neg]
        have := hg₂min h hop (Finsupp.mem_support_iff.mp hh).bot_lt
        omega
    | Negative => rfl
  exact case2_negative_odd_gap X Y hXY hXPi h17_1 hi_odd hi3 hneg
    hsnd1 (no_pair_rank_two_single_Y_iterate_ne_before_second_rank
      X Y hXY g₂ hXg₂ (by omega))

/-- §17 Case 2, multiplicity-two branch.  The later gene is required to be
minimal only among genes of the opposite sign. -/
lemma case2_odd_mid_gaps_before_min_opposite_of_seed
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized) (g g₂ : Gene)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4) (hXg₂ : 0 < X.1.1 g₂)
    (hg₂min : ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h →
      g₂.rank ≤ h.rank)
    (hseed :
      (g.type = GeneType.Positive ∧
        (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1) ∨
      (g.type = GeneType.Negative ∧
        (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2)) :
    (g.type = GeneType.Positive →
      ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 → ¬ Even j →
        ((2 : ℚ), (0 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) ∧
    (g.type = GeneType.Negative →
      ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 → ¬ Even j →
        ((0 : ℚ), (2 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) := by
  have hXPi : X.1.1 ∈ Variety.Pi := Variety.mem_Pi_iff.mpr hXpol
  constructor
  · intro hg_pos j hjlo hjhi hjodd
    rcases hseed with ⟨_, hfst1⟩ | ⟨hg_neg, _⟩
    · apply type15_odd_positive_gap_of_fst_add_two X Y hXY
      simpa [Sigma.sigma] using case2_positive_odd_gap_before_min_opposite
          X Y hXY hXPi h17_1 g g₂ hg_pos hXg₂ hg₂min hjodd
            (by
              obtain ⟨u, hu⟩ := Nat.not_even_iff_odd.mp hjodd
              omega) (by
              obtain ⟨u, hu⟩ := Nat.not_even_iff_odd.mp hjodd
              rw [hg₂_rank]
              omega) hfst1
    · simp [hg_pos] at hg_neg
  · intro hg_neg j hjlo hjhi hjodd
    rcases hseed with ⟨hg_pos, _⟩ | ⟨_, hsnd1⟩
    · simp [hg_neg] at hg_pos
    · apply type15_odd_negative_gap_of_snd_add_two X Y hXY
      simpa [Sigma.sigma] using case2_negative_odd_gap_before_min_opposite
          X Y hXY hXPi h17_1 g g₂ hg_neg hXg₂ hg₂min hjodd
            (by
              obtain ⟨u, hu⟩ := Nat.not_even_iff_odd.mp hjodd
              omega) (by
              obtain ⟨u, hu⟩ := Nat.not_even_iff_odd.mp hjodd
              rw [hg₂_rank]
              omega) hsnd1

/-- Exact-one specialization of the directed odd-window engine. -/
lemma case2_odd_mid_gaps_before_min_opposite
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized) (g g₂ : Gene)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4) (hXg₂ : 0 < X.1.1 g₂)
    (hg₂min : ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h →
      g₂.rank ≤ h.rank)
    (hone : RankTwoSingleExactOne X Y g) :
    (g.type = GeneType.Positive →
      ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 → ¬ Even j →
        ((2 : ℚ), (0 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) ∧
    (g.type = GeneType.Negative →
      ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 → ¬ Even j →
        ((0 : ℚ), (2 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) := by
  apply case2_odd_mid_gaps_before_min_opposite_of_seed X Y hXY h17_1
    hXpol g g₂ hg₂_rank hXg₂ hg₂min
  rcases hone with ⟨hg_pos, hone⟩ | ⟨hg_neg, hone⟩
  · exact Or.inl ⟨hg_pos, by simpa [Sigma.sigma] using (show
      (signature (Chromosome.prime^[1] X.1.1)).1 <
        (signature (Chromosome.prime^[1] Y.1.1)).1 by linarith)⟩
  · exact Or.inr ⟨hg_neg, by simpa [Sigma.sigma] using (show
      (signature (Chromosome.prime^[1] X.1.1)).2 <
        (signature (Chromosome.prime^[1] Y.1.1)).2 by linarith)⟩

/-- Two-cell level-one specialization of the directed odd-window engine. -/
lemma case2_odd_mid_gaps_before_min_opposite_of_two
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized) (g g₂ : Gene)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4) (hXg₂ : 0 < X.1.1 g₂)
    (hg₂min : ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h →
      g₂.rank ≤ h.rank)
    (htwo :
      (g.type = GeneType.Positive ∧
        (signature (Chromosome.prime^[1] X.1.1)).1 + 2 ≤
          (signature (Chromosome.prime^[1] Y.1.1)).1) ∨
      (g.type = GeneType.Negative ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 + 2 ≤
          (signature (Chromosome.prime^[1] Y.1.1)).2)) :
    (g.type = GeneType.Positive →
      ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 → ¬ Even j →
        ((2 : ℚ), (0 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) ∧
    (g.type = GeneType.Negative →
      ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 → ¬ Even j →
        ((0 : ℚ), (2 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) := by
  apply case2_odd_mid_gaps_before_min_opposite_of_seed X Y hXY h17_1
    hXpol g g₂ hg₂_rank hXg₂ hg₂min
  rcases htwo with ⟨hg_pos, htwo⟩ | ⟨hg_neg, htwo⟩
  · exact Or.inl ⟨hg_pos, by simpa [Sigma.sigma] using (show
      (signature (Chromosome.prime^[1] X.1.1)).1 <
        (signature (Chromosome.prime^[1] Y.1.1)).1 by linarith)⟩
  · exact Or.inr ⟨hg_neg, by simpa [Sigma.sigma] using (show
      (signature (Chromosome.prime^[1] X.1.1)).2 <
        (signature (Chromosome.prime^[1] Y.1.1)).2 by linarith)⟩

/-- §17 Case 2, multiplicity-two branch.  The later gene is required to be
minimal only among genes of the opposite sign. -/
lemma exists_mutation_le_no_pair_rank_two_single_type17_of_directed_odd_gaps
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g g₂ : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hg₂_two : 2 ≤ X.1.1 g₂)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hodd :
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
    (hYtop : Chromosome.prime^[2 * q₂ + 4] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_type17_rank_two_of_genes_of_gaps hg_pol
    X Y hXY g g₂ rfl hg₂_neg hg_rank
      (show g₂.rank = 2 * (q₂ + 1) + 2 by omega)
      (by omega) hg₂_two hne
  · simpa using no_pair_rank_two_single_low_fallback_type15_pred_gap
      X Y hXY g hlow
  · intro j hjlo hjhi heven
    by_cases hjtop : j = 2 * q₂ + 4
    · subst j
      exact type10_mid_gap_even_of_Y_ne X Y h17_1 heven (by omega) hYtop
    · exact no_pair_rank_two_single_even_mid_gap_before_second_rank
        X Y hXY h17_1 g₂ (by omega) heven (by omega) (by
          rw [hg₂_rank]
          omega)
  · exact hodd.1
  · exact hodd.2

/-- Exact-one wrapper for the directed Type17 constructor. -/
lemma exists_mutation_le_no_pair_rank_two_single_type17_min_opposite
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (g g₂ : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hg₂_two : 2 ≤ X.1.1 g₂)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (hg₂min : ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h →
      g₂.rank ≤ h.rank)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hone : RankTwoSingleExactOne X Y g)
    (hYtop : Chromosome.prime^[2 * q₂ + 4] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hodd := case2_odd_mid_gaps_before_min_opposite X Y hXY h17_1
    hXpol g g₂ hg₂_rank (by omega) hg₂min hone
  exact exists_mutation_le_no_pair_rank_two_single_type17_of_directed_odd_gaps
    X Y hXY h17_1 g g₂ hg_pol hg_rank hg₂_rank hg_one hg₂_two hne
      hg₂_neg hlow hodd hYtop

/-- §17 Case 2, multiplicity-one Type15 branch with an opposite-minimal later
gene. -/
lemma exists_mutation_le_no_pair_rank_two_single_type15_of_directed_odd_gaps
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g g₂ : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hg₂_one : X.1.1 g₂ = 1)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hodd :
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
    (hYtop : Chromosome.prime^[2 * q₂ + 4] Y.1.1 ≠ 0)
    (hsucc : RankTwoSingleType15Succ (q₂ := q₂) X Y g) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_type15_of_genes_of_gaps hg_pol
    (Nat.zero_le (q₂ + 1)) X Y hXY g g₂ rfl hg₂_neg
      (show g.rank = 2 * 0 + 2 by omega)
      (show g₂.rank = 2 * (q₂ + 1) + 2 by omega)
      (by omega) (by omega) hne
  · simpa using no_pair_rank_two_single_low_fallback_type15_pred_gap
      X Y hXY g hlow
  · intro j hjlo hjhi heven
    by_cases hjtop : j = 2 * q₂ + 4
    · subst j
      exact type10_mid_gap_even_of_Y_ne X Y h17_1 heven (by omega) hYtop
    · exact no_pair_rank_two_single_even_mid_gap_before_second_rank
        X Y hXY h17_1 g₂ (by omega) heven (by omega) (by
          rw [hg₂_rank]
          omega)
  · exact hodd.1
  · exact hodd.2
  · simpa [show 2 * (q₂ + 1) + 3 = 2 * q₂ + 5 by omega] using
      no_pair_rank_two_single_type15_succ_gap X Y hXY g hsucc

/-- Exact-one wrapper for the directed Type15 constructor. -/
lemma exists_mutation_le_no_pair_rank_two_single_type15_min_opposite
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (g g₂ : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hg₂_one : X.1.1 g₂ = 1)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (hg₂min : ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h →
      g₂.rank ≤ h.rank)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hone : RankTwoSingleExactOne X Y g)
    (hYtop : Chromosome.prime^[2 * q₂ + 4] Y.1.1 ≠ 0)
    (hsucc : RankTwoSingleType15Succ (q₂ := q₂) X Y g) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hodd := case2_odd_mid_gaps_before_min_opposite X Y hXY h17_1
    hXpol g g₂ hg₂_rank (by omega) hg₂min hone
  exact exists_mutation_le_no_pair_rank_two_single_type15_of_directed_odd_gaps
    X Y hXY h17_1 g g₂ hg_pol hg_rank hg₂_rank hg_one hg₂_one hne
      hg₂_neg hlow hodd hYtop hsucc

/-- Removing the unique negative exception below level `i` changes the
negative count by exactly one. -/
private lemma case2_neg_count_kill_one
    {W : Chromosome} {gneg : Gene} {i : ℕ}
    (hgneg_one : W gneg = 1) (hgneg_type : gneg.type = .Negative)
    (hgneg_rank : gneg.rank ≤ i)
    (hothers : ∀ h ∈ W.support, h.rank ≤ i → h ≠ gneg →
      h.type = .Positive) :
    (Chromosome.prime^[i] W).sum
        (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
      W.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) - 1 := by
  let W' : Chromosome := W - Finsupp.single gneg 1
  have hgpos : 0 < W gneg := by omega
  have hWsplit : W = W' + Finsupp.single gneg 1 :=
    (sub_single_add_single_eq hgpos).symm
  have hnegadd :
      W.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
        W'.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) + 1 := by
    conv_lhs => rw [hWsplit]
    rw [Finsupp.sum_add_index (by intro g _; simp)
      (by intro g _ mm nn; split_ifs <;> push_cast <;> ring)]
    rw [Finsupp.sum_single_index (by simp)]
    simp [hgneg_type]
  have hkill : Chromosome.prime^[i] (Finsupp.single gneg 1) = 0 := by
    rw [← Gene.ofRank_eq_gene, prime_iterate_ofRank,
      show gneg.rank - i = 0 by omega, Gene.ofRank_zero]
  have hprime_eq : Chromosome.prime^[i] W = Chromosome.prime^[i] W' := by
    conv_lhs => rw [hWsplit]
    rw [iterate_map_add, hkill, add_zero]
  have hW'pos : ∀ h ∈ W'.support, h.rank ≤ i →
      h.type = .Positive := by
    intro h hh hrank
    have hhne : h ≠ gneg := by
      intro he
      subst h
      rw [Finsupp.mem_support_iff, Finsupp.tsub_apply,
        Finsupp.single_eq_same, hgneg_one] at hh
      simp at hh
    have hhW : h ∈ W.support := by
      rw [Finsupp.mem_support_iff, Finsupp.tsub_apply,
        Finsupp.single_apply, if_neg (fun he => hhne he.symm)] at hh
      exact Finsupp.mem_support_iff.mpr (by omega)
    exact hothers h hhW hrank hhne
  have hnegeq := Sigma.neg_count_eq (X := W') i hW'pos
  rw [hprime_eq, hnegeq, hnegadd]
  ring

/-- Off-by-one telescoping with one negative exception. -/
private lemma case2_b0_bi_off_by_one
    {X : Chromosome} (hX : X ∈ Variety.Pi) {i : ℕ} {gneg : Gene}
    (hgneg_one : X gneg = 1) (hgneg_type : gneg.type = .Negative)
    (hgneg_rank : gneg.rank ≤ i)
    (hothers : ∀ h ∈ X.support, h.rank ≤ i → h ≠ gneg →
      h.type = .Positive) :
    (Sigma.sigma X 0).2 - (Sigma.sigma X i).2 =
      (Sigma.sigma X 1).1 - (Sigma.sigma X (i + 1)).1 + 1 := by
  have h0 := Sigma.bi_sum_ai1_eq_neg_count_1 X hX (i := 0)
  have hi := Sigma.bi_sum_ai1_eq_neg_count_1 X hX (i := i)
  have hkill := case2_neg_count_kill_one hgneg_one hgneg_type
    hgneg_rank hothers
  simp only [Sigma.sigma, Function.iterate_zero, id] at h0 hi ⊢
  rw [hkill] at hi
  linarith

/-- Positive-exception mirror of `case2_b0_bi_off_by_one`. -/
private lemma case2_a0_ai_off_by_one
    {X : Chromosome} (hX : X ∈ Variety.Pi) {i : ℕ} {gpos : Gene}
    (hgpos_one : X gpos = 1) (hgpos_type : gpos.type = .Positive)
    (hgpos_rank : gpos.rank ≤ i)
    (hothers : ∀ h ∈ X.support, h.rank ≤ i → h ≠ gpos →
      h.type = .Negative) :
    (Sigma.sigma X 0).1 - (Sigma.sigma X i).1 =
      (Sigma.sigma X 1).2 - (Sigma.sigma X (i + 1)).2 + 1 := by
  have hnegX : (-X) ∈ Variety.Pi := Variety.mem_Pi_iff.mpr
    (Chromosome.IsPolarized_iff_neg_polarized.mp
      (Variety.mem_Pi_iff.mp hX))
  have hkey := case2_b0_bi_off_by_one (X := -X) hnegX
    (gneg := -gpos) (i := i)
    (by rw [Chromosome.neg_apply, neg_neg]; exact hgpos_one)
    (by rw [Gene.neg_type, hgpos_type]; rfl)
    (by rwa [Gene.neg_rank])
    (by
      intro h hh hrank hne
      rw [Finsupp.mem_support_iff, Chromosome.neg_apply] at hh
      have hhX : -h ∈ X.support :=
        Finsupp.mem_support_iff.mpr (by simpa using hh)
      have hhne : -h ≠ gpos := fun he => hne (by rw [← he, neg_neg])
      have ht := hothers (-h) hhX (by rwa [Gene.neg_rank]) hhne
      rw [Gene.neg_type] at ht
      cases hgt : h.type <;> simp_all)
  simp only [Sigma.sigma, ← Chromosome.prime_iterate_neg, signature_neg,
    Prod.snd_swap, Prod.fst_swap] at hkey
  exact hkey

/-- A minimum opposite-sign gene of coefficient one forces the Type15
successor component to be strict. -/
lemma case2_type15_succ_of_min_opposite_one
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized) (g g₂ : Gene)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4) (hg₂_one : X.1.1 g₂ = 1)
    (hg₂_neg : g₂.type = -g.type)
    (hg₂min : ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h →
      g₂.rank ≤ h.rank)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hYtop : Chromosome.prime^[2 * q₂ + 4] Y.1.1 ≠ 0) :
    RankTwoSingleType15Succ (q₂ := q₂) X Y g := by
  have hXPi : X.1.1 ∈ Variety.Pi := Variety.mem_Pi_iff.mpr hXpol
  have htop := type10_mid_gap_even_of_Y_ne X Y h17_1
    (show Even (2 * q₂ + 4) by exact ⟨q₂ + 2, by omega⟩)
    (by omega) hYtop
  have h0 := sigma_zero_eq X Y hXY
  have hdom_succ := le_iff_dominates.mp hXY.le (2 * q₂ + 5)
  rcases hlow with ⟨hg_pos, _, hstrict1⟩ | ⟨hg_neg, _, hstrict1⟩
  · left
    refine ⟨hg_pos, ?_⟩
    have hg₂_type : g₂.type = GeneType.Negative := by
      rw [hg₂_neg, hg_pos, GeneType.neg_positive]
    have hothers : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * q₂ + 4 →
        h ≠ g₂ → h.type = GeneType.Positive := by
      intro h hh hrank hne
      have hpol := Chromosome.IsPolarized_def'.mp hXpol h hh
      cases ht : h.type with
      | NonPolarized => exact False.elim (hpol ht)
      | Positive => rfl
      | Negative =>
          have hop : h.type = -g.type := by simp [ht, hg_pos]
          have hge := hg₂min h hop
            (Finsupp.mem_support_iff.mp hh).bot_lt
          have hrank_eq : h.rank = g₂.rank := by rw [hg₂_rank]; omega
          have hgene : h = g₂ := by
            ext
            · exact hrank_eq
            · exact ht.trans hg₂_type.symm
          exact False.elim (hne hgene)
    have hXid := case2_b0_bi_off_by_one hXPi hg₂_one hg₂_type
      (by rw [hg₂_rank]) hothers
    have hYid := case2_a1_ai_le_b0_bi Y.1.2
      (i := 2 * q₂ + 5) (by omega)
    by_contra hnot
    have hsucc_eq : (Sigma.sigma X.1.1 (2 * q₂ + 5)).1 =
        (Sigma.sigma Y.1.1 (2 * q₂ + 5)).1 :=
      le_antisymm hdom_succ.1 (le_of_not_gt hnot)
    have h0b := congrArg Prod.snd h0
    have htopb :
        (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).2 + 1 ≤
          (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).2 := by
      simpa [Prod.snd_add, add_comm] using htop.2
    simp only [Sigma.sigma,
      show 2 * q₂ + 4 + 1 = 2 * q₂ + 5 by omega,
      show 2 * q₂ + 5 - 1 = 2 * q₂ + 4 by omega] at hXid hYid h0b
    simp only [Sigma.sigma] at hstrict1 hsucc_eq
    linarith
  · right
    refine ⟨hg_neg, ?_⟩
    have hg₂_type : g₂.type = GeneType.Positive := by
      rw [hg₂_neg, hg_neg, GeneType.neg_negative]
    have hothers : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * q₂ + 4 →
        h ≠ g₂ → h.type = GeneType.Negative := by
      intro h hh hrank hne
      have hpol := Chromosome.IsPolarized_def'.mp hXpol h hh
      cases ht : h.type with
      | NonPolarized => exact False.elim (hpol ht)
      | Positive =>
          have hop : h.type = -g.type := by simp [ht, hg_neg]
          have hge := hg₂min h hop
            (Finsupp.mem_support_iff.mp hh).bot_lt
          have hrank_eq : h.rank = g₂.rank := by rw [hg₂_rank]; omega
          have hgene : h = g₂ := by
            ext
            · exact hrank_eq
            · exact ht.trans hg₂_type.symm
          exact False.elim (hne hgene)
      | Negative => rfl
    have hXid := case2_a0_ai_off_by_one hXPi hg₂_one hg₂_type
      (by rw [hg₂_rank]) hothers
    have hYid := case2_b1_bi_le_a0_ai Y.1.2
      (i := 2 * q₂ + 5) (by omega)
    by_contra hnot
    have hsucc_eq : (Sigma.sigma X.1.1 (2 * q₂ + 5)).2 =
        (Sigma.sigma Y.1.1 (2 * q₂ + 5)).2 :=
      le_antisymm hdom_succ.2 (le_of_not_gt hnot)
    have h0a := congrArg Prod.fst h0
    have htopy :
        (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).1 + 1 ≤
          (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).1 := by
      simpa [Prod.fst_add, add_comm] using htop.1
    simp only [Sigma.sigma,
      show 2 * q₂ + 4 + 1 = 2 * q₂ + 5 by omega,
      show 2 * q₂ + 5 - 1 = 2 * q₂ + 4 by omega] at hXid hYid h0a
    simp only [Sigma.sigma] at hstrict1 hsucc_eq
    linarith

/-- Callback-free Case 2 solver once the top endpoint is nonzero. -/
lemma exists_mutation_le_no_pair_rank_two_single_exact_one_min_opposite
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (g g₂ : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hXg₂ : 0 < X.1.1 g₂)
    (hne : g ≠ g₂) (hg₂_neg : g₂.type = -g.type)
    (hg₂min : ∀ h : Gene, h.type = -g.type → 0 < X.1.1 h →
      g₂.rank ≤ h.rank)
    (hlow : RankTwoSingleLowFallback X Y g)
    (hone : RankTwoSingleExactOne X Y g)
    (hYtop : Chromosome.prime^[2 * q₂ + 4] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hg₂_two : 2 ≤ X.1.1 g₂
  · exact exists_mutation_le_no_pair_rank_two_single_type17_min_opposite
      X Y hXY h17_1 hXpol g g₂ hg_pol hg_rank hg₂_rank hg_one
        hg₂_two hne hg₂_neg hg₂min hlow hone hYtop
  · have hg₂_one : X.1.1 g₂ = 1 := by omega
    have hsucc := case2_type15_succ_of_min_opposite_one
      X Y hXY h17_1 hXpol g g₂ hg₂_rank hg₂_one hg₂_neg hg₂min
        hlow hYtop
    exact exists_mutation_le_no_pair_rank_two_single_type15_min_opposite
      X Y hXY h17_1 hXpol g g₂ hg_pol hg_rank hg₂_rank hg_one
        hg₂_one hne hg₂_neg hg₂min hlow hone hYtop hsucc

private lemma case2_signature_prime_iterate_snd_eq_zero_of_rank_le
    {W : Chromosome} {i : ℕ}
    (hpol : ∀ g : Gene, 0 < W g → g.rank = i + 1 →
      g.type ≠ GeneType.NonPolarized)
    (hrank : ∀ g : Gene, 0 < W g → g.rank ≤ i + 1)
    (hno : W ⟨i + 1, GeneType.Negative, by omega⟩ = 0) :
    (signature (Chromosome.prime^[i] W)).2 = 0 := by
  rw [signature_snd, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro g hg
  by_cases hcoeff : (Chromosome.prime^[i] W) g = 0
  · simp [hcoeff]
  · have hcoeff_pos : 0 < (Chromosome.prime^[i] W) g :=
      Nat.pos_of_ne_zero hcoeff
    let g0 : Gene :=
      ⟨g.rank + i, g.type, Nat.le_add_right_of_le g.rank_pos⟩
    have hg0_pos : 0 < W g0 := by
      simpa [g0, prime_iterate_coeff] using hcoeff_pos
    have hg_rank : g.rank = 1 := by
      have hle := hrank g0 hg0_pos
      dsimp [g0] at hle
      have hpos := g.rank_pos
      omega
    have hg0_rank : g0.rank = i + 1 := by
      dsimp [g0]
      omega
    have hg_pol : g.type ≠ GeneType.NonPolarized :=
      hpol g0 hg0_pos hg0_rank
    have hg_not_neg : g.type ≠ GeneType.Negative := by
      intro hneg
      have hg0_eq : g0 = ⟨i + 1, GeneType.Negative, by omega⟩ := by
        ext
        · dsimp [g0]
          omega
        · exact hneg
      have : 0 < W ⟨i + 1, GeneType.Negative, by omega⟩ := by
        simpa [hg0_eq] using hg0_pos
      rw [hno] at this
      omega
    have hg_pos : g.type = GeneType.Positive := by
      cases ht : g.type
      · exact False.elim (hg_pol ht)
      · rfl
      · exact False.elim (hg_not_neg ht)
    simp [Gene.signature, hg_rank, hg_pos]

private lemma case2_signature_prime_iterate_fst_eq_zero_of_rank_le
    {W : Chromosome} {i : ℕ}
    (hpol : ∀ g : Gene, 0 < W g → g.rank = i + 1 →
      g.type ≠ GeneType.NonPolarized)
    (hrank : ∀ g : Gene, 0 < W g → g.rank ≤ i + 1)
    (hno : W ⟨i + 1, GeneType.Positive, by omega⟩ = 0) :
    (signature (Chromosome.prime^[i] W)).1 = 0 := by
  rw [signature_fst, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro g hg
  by_cases hcoeff : (Chromosome.prime^[i] W) g = 0
  · simp [hcoeff]
  · have hcoeff_pos : 0 < (Chromosome.prime^[i] W) g :=
      Nat.pos_of_ne_zero hcoeff
    let g0 : Gene :=
      ⟨g.rank + i, g.type, Nat.le_add_right_of_le g.rank_pos⟩
    have hg0_pos : 0 < W g0 := by
      simpa [g0, prime_iterate_coeff] using hcoeff_pos
    have hg_rank : g.rank = 1 := by
      have hle := hrank g0 hg0_pos
      dsimp [g0] at hle
      have hpos := g.rank_pos
      omega
    have hg0_rank : g0.rank = i + 1 := by
      dsimp [g0]
      omega
    have hg_pol : g.type ≠ GeneType.NonPolarized :=
      hpol g0 hg0_pos hg0_rank
    have hg_not_pos : g.type ≠ GeneType.Positive := by
      intro hpos
      have hg0_eq : g0 = ⟨i + 1, GeneType.Positive, by omega⟩ := by
        ext
        · dsimp [g0]
          omega
        · exact hpos
      have : 0 < W ⟨i + 1, GeneType.Positive, by omega⟩ := by
        simpa [hg0_eq] using hg0_pos
      rw [hno] at this
      omega
    have hg_neg : g.type = GeneType.Negative := by
      cases ht : g.type
      · exact False.elim (hg_pol ht)
      · exact False.elim (hg_not_pos ht)
      · rfl
    simp [Gene.signature, hg_rank, hg_neg]

/-- The no-common-gene reduction prevents `Y` from vanishing at the even rank
of any polarized X-gene. -/
lemma no_pair_rank_two_single_Y_iterate_ne_at_common_free_gene_rank
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ h : Gene, 0 < X.1.1 h → Y.1.1 h ≤ 0)
    (g₂ : Gene) (hXg₂ : 0 < X.1.1 g₂)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized) :
    Chromosome.prime^[2 * q₂ + 4] Y.1.1 ≠ 0 := by
  intro hYzero
  have hYrank : ∀ h : Gene, 0 < Y.1.1 h → h.rank ≤ 2 * q₂ + 4 := by
    intro h hh
    exact (Chromosome.prime_iterate_eq_zero_rank_le
      (X := Y.1.1) (k := 2 * q₂ + 4)).2 hYzero h
        (Finsupp.mem_support_iff.mpr (ne_of_gt hh))
  have hYpol_top : ∀ h : Gene, 0 < Y.1.1 h →
      h.rank = (2 * q₂ + 3) + 1 →
      h.type ≠ GeneType.NonPolarized := by
    intro h hh hhrank
    have heven : Even h.rank := by rw [hhrank]; exact ⟨q₂ + 2, by omega⟩
    have heven_part : 0 < Y.1.1.evenPart h := by
      rw [evenPart_eq, Finsupp.filter_apply, if_pos heven]
      exact hh
    exact Chromosome.IsPolarized_def'.mp
      (Variety.mem_Pi_iff.mp Y.1.2.1) h
      (Finsupp.mem_support_iff.mpr heven_part.ne')
  cases hg₂_type : g₂.type with
  | NonPolarized => exact hg₂_pol hg₂_type
  | Positive =>
      have hno_pos :
          Y.1.1 ⟨2 * q₂ + 4, GeneType.Positive, by omega⟩ = 0 := by
        have hgene :
            (⟨2 * q₂ + 4, GeneType.Positive, by omega⟩ : Gene) = g₂ :=
          Gene.ext (by simp [hg₂_rank]) hg₂_type.symm
        have hle := hcommon g₂ hXg₂
        rw [hgene]
        omega
      have hYfst0 := case2_signature_prime_iterate_fst_eq_zero_of_rank_le
        (W := Y.1.1) (i := 2 * q₂ + 3) hYpol_top
        (by intro h hh; simpa using hYrank h hh) (by simpa using hno_pos)
      have hXfst1 := one_le_signature_prime_pred_fst_of_positive
        (X := X.1.1) (gpos := g₂) hg₂_type hXg₂
      have hXfst1' :
          1 ≤ (signature (Chromosome.prime^[2 * q₂ + 3] X.1.1)).1 := by
        simpa [hg₂_rank] using hXfst1
      have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 3)).1
      linarith
  | Negative =>
      have hno_neg :
          Y.1.1 ⟨2 * q₂ + 4, GeneType.Negative, by omega⟩ = 0 := by
        have hgene :
            (⟨2 * q₂ + 4, GeneType.Negative, by omega⟩ : Gene) = g₂ :=
          Gene.ext (by simp [hg₂_rank]) hg₂_type.symm
        have hle := hcommon g₂ hXg₂
        rw [hgene]
        omega
      have hYsnd0 := case2_signature_prime_iterate_snd_eq_zero_of_rank_le
        (W := Y.1.1) (i := 2 * q₂ + 3) hYpol_top
        (by intro h hh; simpa using hYrank h hh) (by simpa using hno_neg)
      have hXsnd1 := one_le_signature_prime_pred_snd_of_negative
        (X := X.1.1) (gneg := g₂) hg₂_type hXg₂
      have hXsnd1' :
          1 ≤ (signature (Chromosome.prime^[2 * q₂ + 3] X.1.1)).2 := by
        simpa [hg₂_rank] using hXsnd1
      have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 3)).2
      linarith

/-- Complete §17 Case 2 low-fallback solver.  It selects the minimum
opposite-sign gene internally and exposes no structural callbacks. -/
lemma exists_mutation_le_no_pair_rank_two_single_low_fallback
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ h : Gene, 0 < X.1.1 h → Y.1.1 h ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ h : Gene, 0 < X.1.1 h → g.rank ≤ h.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized) (hg_rank : g.rank = 2)
    (hg_one : X.1.1 g = 1)
    (hlow : RankTwoSingleLowFallback X Y g) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨g₂, q₂, hg₂_neg, hXg₂, hg₂min, _hg₂_pol, hg₂_rank⟩ :=
    no_pair_rank_two_single_min_opposite_gene_data X Y hXY hXpol
      hno_pair g hgX hgmin hg_pol hg_rank hlow
  have hne : g ≠ g₂ := by
    intro heq
    rw [← heq, hg_rank] at hg₂_rank
    omega
  have hYtop := no_pair_rank_two_single_Y_iterate_ne_at_common_free_gene_rank
    X Y hXY hcommon g₂ hXg₂ hg₂_rank _hg₂_pol
  rcases no_pair_rank_two_single_low_fallback_gap_split X Y g hlow with
    htwo | hone'
  · have hodd := case2_odd_mid_gaps_before_min_opposite_of_two
      X Y hXY h17_1 hXpol g g₂ hg₂_rank hXg₂ hg₂min htwo
    by_cases hg₂_two : 2 ≤ X.1.1 g₂
    · exact exists_mutation_le_no_pair_rank_two_single_type17_of_directed_odd_gaps
        X Y hXY h17_1 g g₂ hg_pol hg_rank hg₂_rank hg_one hg₂_two
          hne hg₂_neg hlow hodd hYtop
    · have hg₂_one : X.1.1 g₂ = 1 := by omega
      have hsucc := case2_type15_succ_of_min_opposite_one
        X Y hXY h17_1 hXpol g g₂ hg₂_rank hg₂_one hg₂_neg hg₂min
          hlow hYtop
      exact exists_mutation_le_no_pair_rank_two_single_type15_of_directed_odd_gaps
        X Y hXY h17_1 g g₂ hg_pol hg_rank hg₂_rank hg_one hg₂_one
          hne hg₂_neg hlow hodd hYtop hsucc
  · exact exists_mutation_le_no_pair_rank_two_single_exact_one_min_opposite
      X Y hXY h17_1 hXpol g g₂ hg_pol hg_rank hg₂_rank hg_one hXg₂
        hne hg₂_neg hg₂min hlow hone' hYtop

end MixPi2Lambda
