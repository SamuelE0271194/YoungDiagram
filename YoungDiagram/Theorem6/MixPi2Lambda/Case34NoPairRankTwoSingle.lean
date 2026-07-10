import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleRest

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

private lemma one_one_le_of_both_lt_current_L3
    {W Z : Chromosome}
    (hW : W ∈ Mix (2 • Lambda, Pi))
    (hZ : Z ∈ Mix (2 • Lambda, Pi))
    (hfst : W.signature.1 < Z.signature.1)
    (hsnd : W.signature.2 < Z.signature.2) :
    ((1 : ℚ), (1 : ℚ)) + W.signature ≤ Z.signature := by
  obtain ⟨nw, hnw⟩ := Mix2LambdaSection17.signature_Mix_2Lambda_Pi_isNat hW
  obtain ⟨nz, hnz⟩ := Mix2LambdaSection17.signature_Mix_2Lambda_Pi_isNat hZ
  rw [hnw, hnz] at hfst hsnd ⊢
  change (nw.1 : ℚ) < (nz.1 : ℚ) at hfst
  change (nw.2 : ℚ) < (nz.2 : ℚ) at hsnd
  constructor
  · change (1 : ℚ) + (nw.1 : ℚ) ≤ (nz.1 : ℚ)
    have hn : nw.1 + 1 ≤ nz.1 :=
      Nat.add_one_le_iff.mpr (by exact_mod_cast hfst)
    have hnQ : (nw.1 : ℚ) + 1 ≤ (nz.1 : ℚ) := by exact_mod_cast hn
    linarith
  · change (1 : ℚ) + (nw.2 : ℚ) ≤ (nz.2 : ℚ)
    have hn : nw.2 + 1 ≤ nz.2 :=
      Nat.add_one_le_iff.mpr (by exact_mod_cast hsnd)
    have hnQ : (nw.2 : ℚ) + 1 ≤ (nz.2 : ℚ) := by exact_mod_cast hn
    linarith

/-!
# Label 4 rank-two singleton level-one boundary

This module isolates the first split in §17 Case 2.  For a minimal polarized
rank-`2` gene of multiplicity one, the first iterate of `X` is nonzero.  Hence
(17.1) gives a strict level-`1` component gap.  The component preferred by the
boundary type10 predecessor profile is the component opposite to the sign of
the low gene.
-/

/-- A minimal rank-`2` gene makes the first iterate of `Y` nonzero under
dominance. -/
lemma no_pair_rank_two_single_Y_prime_one_ne {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (g : Gene)
    (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_rank : g.rank = 2) :
    Chromosome.prime^[1] Y.1.1 ≠ 0 := by
  have hXne : X.1.1 ≠ 0 := by
    intro hzero
    rw [hzero] at hgX
    exact (Nat.not_lt_zero _ hgX)
  have hX1ne : Chromosome.prime^[1] X.1.1 ≠ 0 := by
    change X.1.1.prime ≠ 0
    apply prime_ne_zero_of_rank_ge_two hXne
    intro h hh
    have hhpos : 0 < X.1.1 h :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have hle := hgmin h hhpos
    omega
  intro hYzero
  have hle := le_iff_dominates.mp hXY.le 1
  rw [hYzero, map_zero] at hle
  exact hX1ne (signature_eq_zero
    (le_antisymm hle (signature_nonneg _)))

/-- The level-`1` strict gap from (17.1), ordered so that the type10-preferred
component is listed first. -/
lemma no_pair_rank_two_single_level_one_split {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g : Gene)
    (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) :
    (g.type = GeneType.Positive ∧
        ((signature (Chromosome.prime^[1] X.1.1)).2 <
            (signature (Chromosome.prime^[1] Y.1.1)).2 ∨
          (¬ (signature (Chromosome.prime^[1] X.1.1)).2 <
              (signature (Chromosome.prime^[1] Y.1.1)).2 ∧
            (signature (Chromosome.prime^[1] X.1.1)).1 <
              (signature (Chromosome.prime^[1] Y.1.1)).1))) ∨
      (g.type = GeneType.Negative ∧
        ((signature (Chromosome.prime^[1] X.1.1)).1 <
            (signature (Chromosome.prime^[1] Y.1.1)).1 ∨
          (¬ (signature (Chromosome.prime^[1] X.1.1)).1 <
              (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
            (signature (Chromosome.prime^[1] X.1.1)).2 <
              (signature (Chromosome.prime^[1] Y.1.1)).2))) := by
  have hY1 := no_pair_rank_two_single_Y_prime_one_ne
    X Y hXY g hgX hgmin hg_rank
  cases htype : g.type with
  | NonPolarized => exact False.elim (hg_pol htype)
  | Positive =>
      exact Or.inl ⟨rfl,
        prime_iterate_snd_or_fst_lt X Y hXY h17_1
          (k := 1) (by omega) hY1⟩
  | Negative =>
      exact Or.inr ⟨rfl,
        prime_iterate_fst_or_snd_lt X Y hXY h17_1
          (k := 1) (by omega) hY1⟩

/-- The preferred half of the level-`1` split is exactly the predecessor gap
needed by the boundary type10 mutation with lower parameter `q = 0`. -/
lemma no_pair_rank_two_single_preferred_type10_pred_gap {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (g : Gene)
    (hpreferred :
      (g.type = GeneType.Positive ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) ∨
      (g.type = GeneType.Negative ∧
        (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1)) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[1] X.1.1) ≤
      signature (Gene.ofRank 1 g.type) +
        signature (Chromosome.prime^[1] Y.1.1) := by
  rcases hpreferred with ⟨htype, hsnd⟩ | ⟨htype, hfst⟩
  · simpa [htype] using type10_pred_gap_positive X Y hXY (p := 0) hsnd
  · simpa [htype] using type10_pred_gap_negative X Y hXY (p := 0) hfst

/-- A surviving second gene forces every iterate of `Y` strictly below its
rank to be nonzero. -/
lemma no_pair_rank_two_single_Y_iterate_ne_before_second_rank {m j : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (g₂ : Gene)
    (hXg₂ : 0 < X.1.1 g₂)
    (hj : j < g₂.rank) :
    Chromosome.prime^[j] Y.1.1 ≠ 0 := by
  have hXj : Chromosome.prime^[j] X.1.1 ≠ 0 := by
    intro hXzero
    have hall :=
      (Chromosome.prime_iterate_eq_zero_rank_le
        (X := X.1.1) (k := j)).2 hXzero
    have hg₂_support : g₂ ∈ X.1.1.support :=
      Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂)
    exact (not_le_of_gt hj) (hall g₂ hg₂_support)
  intro hYzero
  have hle := le_iff_dominates.mp hXY.le j
  rw [hYzero, map_zero] at hle
  exact hXj (signature_eq_zero
    (le_antisymm hle (signature_nonneg _)))

/-- Every positive even middle level strictly below the selected second gene
has the `(1,1)` type10 slack directly from (17.1). -/
lemma no_pair_rank_two_single_even_mid_gap_before_second_rank {m j : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g₂ : Gene)
    (hXg₂ : 0 < X.1.1 g₂)
    (heven : Even j)
    (hjpos : 0 < j)
    (hj : j < g₂.rank) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := by
  exact type10_mid_gap_even_of_Y_ne X Y h17_1 heven hjpos
    (no_pair_rank_two_single_Y_iterate_ne_before_second_rank
      X Y hXY g₂ hXg₂ hj)

/-- §17 Case 2 positive low-gene seed:
`a₁-a₃ = r₀-r₁ > s₀-s₁ ≥ s₁-s₂ ≥ c₁-c₃`. -/
lemma no_pair_rank_two_single_case2_seed_fst_positive {m k : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g : Gene)
    (hg_rank : g.rank = 2)
    (hg_pos : g.type = GeneType.Positive)
    (hg_one : X.1.1 g = 1)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, k ≤ h.rank)
    (hk : 3 ≤ k) :
    (signature (Chromosome.prime^[3] X.1.1)).1 <
      (signature (Chromosome.prime^[3] Y.1.1)).1 := by
  have hXdrop := KEY_X_edge_fst_positive X
    (m := 2) (k := k) (gm := g) hg_rank hg_pos hg_one h2nd hk
  have hcond6 :=
    Mix2LambdaSection17.cond_15_6_Mix_Pi_2Lambda Y.1.2 1
  rw [if_neg (by decide : ¬ Even 1)] at hcond6
  have hYdrop := rank_drop_le Y.1.2 1
  have hrX0 :
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
    simpa [Sigma.sigma, X.2] using
      (@signature_sum_eq_rank (Chromosome.prime^[0] X.1.1))
  have hrY0 :
      (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
    simpa [Sigma.sigma, Y.2] using
      (@signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1))
  have hrX1 :
      (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := by
    simpa [Sigma.sigma] using
      (@signature_sum_eq_rank (Chromosome.prime^[1] X.1.1))
  have hrY1 :
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    simpa [Sigma.sigma] using
      (@signature_sum_eq_rank (Chromosome.prime^[1] Y.1.1))
  have hgapQ :
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 1 ≤
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt hr1
  have hdom := (le_iff_dominates.mp hXY.le 1).1
  norm_num at hXdrop hcond6 hYdrop
  simp only [Sigma.sigma] at hXdrop hcond6 hYdrop hrX0 hrY0 hrX1 hrY1 hdom ⊢
  linarith

/-- Negative-sign mirror of `no_pair_rank_two_single_case2_seed_fst_positive`. -/
lemma no_pair_rank_two_single_case2_seed_snd_negative {m k : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g : Gene)
    (hg_rank : g.rank = 2)
    (hg_neg : g.type = GeneType.Negative)
    (hg_one : X.1.1 g = 1)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, k ≤ h.rank)
    (hk : 3 ≤ k) :
    (signature (Chromosome.prime^[3] X.1.1)).2 <
      (signature (Chromosome.prime^[3] Y.1.1)).2 := by
  have hXdrop := KEY_X_edge_snd_negative X
    (m := 2) (k := k) (gm := g) hg_rank hg_neg hg_one h2nd hk
  have hcond7 :=
    Mix2LambdaSection17.cond_15_7_Mix_Pi_2Lambda Y.1.2 1
  rw [if_neg (by decide : ¬ Even 1)] at hcond7
  have hYdrop := rank_drop_le Y.1.2 1
  have hrX0 :
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
    simpa [Sigma.sigma, X.2] using
      (@signature_sum_eq_rank (Chromosome.prime^[0] X.1.1))
  have hrY0 :
      (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
        ((m + 2 : ℕ) : ℚ) := by
    simpa [Sigma.sigma, Y.2] using
      (@signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1))
  have hrX1 :
      (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := by
    simpa [Sigma.sigma] using
      (@signature_sum_eq_rank (Chromosome.prime^[1] X.1.1))
  have hrY1 :
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    simpa [Sigma.sigma] using
      (@signature_sum_eq_rank (Chromosome.prime^[1] Y.1.1))
  have hgapQ :
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 1 ≤
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt hr1
  have hdom := (le_iff_dominates.mp hXY.le 1).2
  norm_num at hXdrop hcond7 hYdrop
  simp only [Sigma.sigma] at hXdrop hcond7 hYdrop hrX0 hrY0 hrX1 hrY1 hdom ⊢
  linarith

/-- Positive preferred branch, first component: propagate `a₃<c₃`. -/
lemma no_pair_rank_two_single_preferred_odd_fst_lt_positive {m k : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g : Gene)
    (hg_rank : g.rank = 2)
    (hg_pos : g.type = GeneType.Positive)
    (hg_one : X.1.1 g = 1)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, k ≤ h.rank)
    (hk : 3 ≤ k) :
    ∀ j, 2 ≤ j → j ≤ k → ¬ Even j →
      (signature (Chromosome.prime^[j] X.1.1)).1 <
        (signature (Chromosome.prime^[j] Y.1.1)).1 := by
  intro j hjlo hjhi hjodd
  obtain ⟨u, hu⟩ := Nat.not_even_iff_odd.mp hjodd
  have hu_pos : 1 ≤ u := by omega
  let t := u - 1
  have hj3 : j = 3 + 2 * t := by
    dsimp [t]
    omega
  have hseed_fst := no_pair_rank_two_single_case2_seed_fst_positive
    X Y hXY hr1 g hg_rank hg_pos hg_one h2nd hk
  have hfst_window := window_odd_fst_lt X Y hr1 hg_one h2nd
    3 t (by decide) (by omega) hseed_fst
  rw [hj3]
  simpa [Sigma.sigma] using hfst_window t (le_refl t)

/-- Positive preferred branch, second component: propagate `b₁<d₁`. -/
lemma no_pair_rank_two_single_preferred_odd_snd_lt_positive {m k : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g : Gene)
    (hg_one : X.1.1 g = 1)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, k ≤ h.rank)
    (hsnd1 : (signature (Chromosome.prime^[1] X.1.1)).2 <
      (signature (Chromosome.prime^[1] Y.1.1)).2) :
    ∀ j, 2 ≤ j → j ≤ k → ¬ Even j →
      (signature (Chromosome.prime^[j] X.1.1)).2 <
        (signature (Chromosome.prime^[j] Y.1.1)).2 := by
  intro j hjlo hjhi hjodd
  obtain ⟨u, hu⟩ := Nat.not_even_iff_odd.mp hjodd
  have hsnd_window := window_odd_snd_lt X Y hr1 hg_one h2nd
    1 u (by decide) (by omega) (by simpa [Sigma.sigma] using hsnd1)
  rw [hu]
  simpa [Sigma.sigma, add_comm] using hsnd_window u (le_refl u)

/-- Negative preferred branch, first component: propagate `a₁<c₁`. -/
lemma no_pair_rank_two_single_preferred_odd_fst_lt_negative {m k : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g : Gene)
    (hg_one : X.1.1 g = 1)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, k ≤ h.rank)
    (hfst1 : (signature (Chromosome.prime^[1] X.1.1)).1 <
      (signature (Chromosome.prime^[1] Y.1.1)).1) :
    ∀ j, 2 ≤ j → j ≤ k → ¬ Even j →
      (signature (Chromosome.prime^[j] X.1.1)).1 <
        (signature (Chromosome.prime^[j] Y.1.1)).1 := by
  intro j hjlo hjhi hjodd
  obtain ⟨u, hu⟩ := Nat.not_even_iff_odd.mp hjodd
  have hfst_window := window_odd_fst_lt X Y hr1 hg_one h2nd
    1 u (by decide) (by omega) (by simpa [Sigma.sigma] using hfst1)
  rw [hu]
  simpa [Sigma.sigma, add_comm] using hfst_window u (le_refl u)

/-- Negative preferred branch, second component: propagate `b₃<d₃`. -/
lemma no_pair_rank_two_single_preferred_odd_snd_lt_negative {m k : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g : Gene)
    (hg_rank : g.rank = 2)
    (hg_neg : g.type = GeneType.Negative)
    (hg_one : X.1.1 g = 1)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, k ≤ h.rank)
    (hk : 3 ≤ k) :
    ∀ j, 2 ≤ j → j ≤ k → ¬ Even j →
      (signature (Chromosome.prime^[j] X.1.1)).2 <
        (signature (Chromosome.prime^[j] Y.1.1)).2 := by
  intro j hjlo hjhi hjodd
  obtain ⟨u, hu⟩ := Nat.not_even_iff_odd.mp hjodd
  have hu_pos : 1 ≤ u := by omega
  let t := u - 1
  have hj3 : j = 3 + 2 * t := by
    dsimp [t]
    omega
  have hseed_snd := no_pair_rank_two_single_case2_seed_snd_negative
    X Y hXY hr1 g hg_rank hg_neg hg_one h2nd hk
  have hsnd_window := window_odd_snd_lt X Y hr1 hg_one h2nd
    3 t (by decide) (by omega) hseed_snd
  rw [hj3]
  simpa [Sigma.sigma] using hsnd_window t (le_refl t)

/-- Positive preferred branch: combine the two odd component windows. -/
lemma no_pair_rank_two_single_preferred_odd_mid_gap_positive {m k : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g : Gene) (hg_rank : g.rank = 2)
    (hg_pos : g.type = GeneType.Positive) (hg_one : X.1.1 g = 1)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, k ≤ h.rank)
    (hk : 3 ≤ k)
    (hsnd1 : (signature (Chromosome.prime^[1] X.1.1)).2 <
      (signature (Chromosome.prime^[1] Y.1.1)).2) :
    ∀ j, 2 ≤ j → j ≤ k → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
  intro j hjlo hjhi hjodd
  have hXj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 j
  have hYj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 j
  rw [if_neg hjodd] at hXj_mem hYj_mem
  exact one_one_le_of_both_lt_current_L3 hXj_mem hYj_mem
    (no_pair_rank_two_single_preferred_odd_fst_lt_positive
      X Y hXY hr1 g hg_rank hg_pos hg_one h2nd hk j hjlo hjhi hjodd)
    (no_pair_rank_two_single_preferred_odd_snd_lt_positive
      X Y hr1 g hg_one h2nd hsnd1 j hjlo hjhi hjodd)

/-- Negative preferred branch: combine the two odd component windows. -/
lemma no_pair_rank_two_single_preferred_odd_mid_gap_negative {m k : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g : Gene) (hg_rank : g.rank = 2)
    (hg_neg : g.type = GeneType.Negative) (hg_one : X.1.1 g = 1)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, k ≤ h.rank)
    (hk : 3 ≤ k)
    (hfst1 : (signature (Chromosome.prime^[1] X.1.1)).1 <
      (signature (Chromosome.prime^[1] Y.1.1)).1) :
    ∀ j, 2 ≤ j → j ≤ k → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
  intro j hjlo hjhi hjodd
  have hXj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 j
  have hYj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 j
  rw [if_neg hjodd] at hXj_mem hYj_mem
  exact one_one_le_of_both_lt_current_L3 hXj_mem hYj_mem
    (no_pair_rank_two_single_preferred_odd_fst_lt_negative
      X Y hr1 g hg_one h2nd hfst1 j hjlo hjhi hjodd)
    (no_pair_rank_two_single_preferred_odd_snd_lt_negative
      X Y hXY hr1 g hg_rank hg_neg hg_one h2nd hk j hjlo hjhi hjodd)

/-- Sign-dispatching wrapper for the preferred odd middle window. -/
lemma no_pair_rank_two_single_preferred_odd_mid_gap {m k : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g : Gene)
    (hg_rank : g.rank = 2)
    (hg_one : X.1.1 g = 1)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support, k ≤ h.rank)
    (hk : 3 ≤ k)
    (hpreferred :
      (g.type = GeneType.Positive ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) ∨
      (g.type = GeneType.Negative ∧
        (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1)) :
    ∀ j, 2 ≤ j → j ≤ k → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
  rcases hpreferred with ⟨hg_pos, hsnd1⟩ | ⟨hg_neg, hfst1⟩
  · exact no_pair_rank_two_single_preferred_odd_mid_gap_positive
      X Y hXY hr1 g hg_rank hg_pos hg_one h2nd hk hsnd1
  · exact no_pair_rank_two_single_preferred_odd_mid_gap_negative
      X Y hXY hr1 g hg_rank hg_neg hg_one h2nd hk hfst1

/-- Assemble the preferred §17 Case 2 type10 mutation once its middle and
successor windows have been established. -/
lemma exists_mutation_le_no_pair_rank_two_single_preferred_of_type10_gaps
    {m q₂ : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (g g₂ : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg : 1 ≤ X.1.1 g)
    (hg₂ : 1 ≤ X.1.1 g₂)
    (hne : g ≠ g₂)
    (hpreferred :
      (g.type = GeneType.Positive ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) ∨
      (g.type = GeneType.Negative ∧
        (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1))
    (hgap_mid : ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 →
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 g₂.type) +
          signature (Chromosome.prime^[2 * q₂ + 5] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 5] Y.1.1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have h_le : 0 ≤ q₂ + 1 := Nat.zero_le _
  have hg_rank' : g.rank = 2 * 0 + 2 := by omega
  have hg₂_rank' : g₂.rank = 2 * (q₂ + 1) + 2 := by omega
  have hgap_pred :=
    no_pair_rank_two_single_preferred_type10_pred_gap X Y hXY g hpreferred
  have hZle := type10_pair_target_add_rest_le_of_gaps
    hg_pol hg₂_pol h_le X Y hXY g g₂ rfl rfl hg_rank' hg₂_rank'
    hg hg₂ hne hgap_pred
    (by
      intro j hjlo hjhi
      exact hgap_mid j (by omega) (by omega))
    (by simpa [show 2 * (q₂ + 1) + 3 = 2 * q₂ + 5 by omega]
      using hgap_succ)
  exact exists_mutation_le_type10_of_genes hg_pol hg₂_pol h_le X Y
    g g₂ rfl rfl hg_rank' hg₂_rank' hg hg₂ hne hZle

/-- Preferred-branch reduction with all even middle levels below the top
discharged internally.  The exposed obligations are exactly the odd window,
the top even level, and the successor level. -/
lemma exists_mutation_le_no_pair_rank_two_single_preferred_of_odd_top_succ_gaps
    {m q₂ : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g g₂ : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg : 1 ≤ X.1.1 g)
    (hg₂ : 1 ≤ X.1.1 g₂)
    (hne : g ≠ g₂)
    (hpreferred :
      (g.type = GeneType.Positive ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) ∨
      (g.type = GeneType.Negative ∧
        (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1))
    (hgap_odd : ∀ j, 2 ≤ j → j ≤ 2 * q₂ + 4 → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_top :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q₂ + 4] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 g₂.type) +
          signature (Chromosome.prime^[2 * q₂ + 5] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 5] Y.1.1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_no_pair_rank_two_single_preferred_of_type10_gaps
    X Y hXY g g₂ hg_pol hg₂_pol hg_rank hg₂_rank hg hg₂ hne
      hpreferred
  · intro j hjlo hjhi
    by_cases hjtop : j = 2 * q₂ + 4
    · simpa [hjtop] using hgap_top
    · by_cases heven : Even j
      · exact no_pair_rank_two_single_even_mid_gap_before_second_rank
          X Y hXY h17_1 g₂ hg₂ heven (by omega) (by
            rw [hg₂_rank]
            omega)
      · exact hgap_odd j hjlo hjhi heven
  · exact hgap_succ

/-- Preferred Case 2 type10 branch with every interior window discharged.
Only the top even gap and the successor gap remain as endpoint obligations. -/
lemma exists_mutation_le_no_pair_rank_two_single_preferred_of_top_succ_gaps
    {m q₂ : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g g₂ : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1)
    (hg₂ : 1 ≤ X.1.1 g₂)
    (hne : g ≠ g₂)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
      2 * q₂ + 4 ≤ h.rank)
    (hpreferred :
      (g.type = GeneType.Positive ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) ∨
      (g.type = GeneType.Negative ∧
        (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1))
    (hgap_top :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q₂ + 4] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 g₂.type) +
          signature (Chromosome.prime^[2 * q₂ + 5] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 5] Y.1.1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply
    exists_mutation_le_no_pair_rank_two_single_preferred_of_odd_top_succ_gaps
      X Y hXY h17_1 g g₂ hg_pol hg₂_pol hg_rank hg₂_rank
      (by omega) hg₂ hne hpreferred
  · exact no_pair_rank_two_single_preferred_odd_mid_gap
      X Y hXY hr1 g hg_rank hg_one h2nd (by omega) hpreferred
  · exact hgap_top
  · exact hgap_succ

end MixPi2Lambda
