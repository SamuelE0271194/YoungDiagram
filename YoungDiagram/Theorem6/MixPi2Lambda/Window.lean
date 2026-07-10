import YoungDiagram.Theorem6.MixPi2Lambda.Type10
import YoungDiagram.Theorem6.Mix2LambdaPrelim
import YoungDiagram.Theorem6.MixLambdaPi.Propagation

/-!
# §17 window-propagation core for `Mix (Pi, 2 • Lambda)` no-equal-rank-pair Case 1.

This file develops the §17 drop machinery for the `m ≥ 3` case of the
no-equal-rank-pair block, mirroring the §16 `MixLambdaPi/Propagation.lean`
engine.  The reusable, label-agnostic 2-step component-drop bricks
`MixLambdaPi.twostep` / `twostep_snd` / `cells` are reused directly.

The polarized source `X` here lies in `Pi` (every gene polarized, even rank), so
the X-side drop is a clean gene count, while the Y-side drop is bounded by the
zeroth drop via the `Mix (Pi, 2 • Lambda)` conditions (15.6)/(15.7).
-/

open Variety hiding prime prime_def
open Chromosome Pointwise
open Mix2LambdaSection17

namespace MixPi2Lambda

/-- Single-step rank-drop antitonicity for `Mix (Pi, 2 • Lambda)`: summing
(15.6) and (15.7) shows the rank-drop `r_i - r_{i+1}` is non-increasing. -/
private lemma rank_drop_step {Z : Chromosome} (hZ : Z ∈ Mix (Pi, 2 • Lambda)) (i : ℕ) :
    (Sigma.sigma Z (i + 1)).1 + (Sigma.sigma Z (i + 1)).2 -
        ((Sigma.sigma Z (i + 2)).1 + (Sigma.sigma Z (i + 2)).2) ≤
      (Sigma.sigma Z i).1 + (Sigma.sigma Z i).2 -
        ((Sigma.sigma Z (i + 1)).1 + (Sigma.sigma Z (i + 1)).2) := by
  have h6 := cond_15_6_Mix_Pi_2Lambda hZ i
  have h7 := cond_15_7_Mix_Pi_2Lambda hZ i
  by_cases hi : Even i
  · rw [if_pos hi] at h6 h7; linarith
  · rw [if_neg hi] at h6 h7; linarith

/-- Telescoped: the rank-drop at level `i` is at most the rank-drop at level `0`. -/
lemma rank_drop_le {Z : Chromosome} (hZ : Z ∈ Mix (Pi, 2 • Lambda)) (i : ℕ) :
    (Sigma.sigma Z i).1 + (Sigma.sigma Z i).2 -
        ((Sigma.sigma Z (i + 1)).1 + (Sigma.sigma Z (i + 1)).2) ≤
      (Sigma.sigma Z 0).1 + (Sigma.sigma Z 0).2 -
        ((Sigma.sigma Z 1).1 + (Sigma.sigma Z 1).2) := by
  induction i with
  | zero => exact le_refl _
  | succ k ih => exact le_trans (rank_drop_step hZ k) ih

/-- KEY_Y for Label 4: the `Y`-side `a`-component 2-step drop at an even level is
bounded by `r_0 - r_1 - 1`.  Sign-agnostic: only rank sums are used.  The level-1
strict rank gap `hr1` is the §17 hypothesis (17.1) at level 1. -/
lemma KEY_Y_fst {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    {i : ℕ} (hi : Even i) :
    (Sigma.sigma Y.1.1 i).1 - (Sigma.sigma Y.1.1 (i + 2)).1 ≤
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
  -- step a: c_{i+1} − c_{i+2} ≤ d_i − d_{i+1} (Label-4 (15.7), even branch)
  have hcond7 := cond_15_7_Mix_Pi_2Lambda Y.1.2 i
  rw [if_pos hi] at hcond7
  -- antitone: s_i − s_{i+1} ≤ s_0 − s_1
  have hdrop := rank_drop_le Y.1.2 i
  -- rank facts
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, X.2] using @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
  have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, Y.2] using @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hgap : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 1 ≤
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt hr1
  linarith

/-- KEY_Y `b`-component analogue: the `Y`-side second-component 2-step drop at an
even level is bounded by `r_0 - r_1 - 1`.  Uses (15.6) instead of (15.7). -/
lemma KEY_Y_snd {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    {i : ℕ} (hi : Even i) :
    (Sigma.sigma Y.1.1 i).2 - (Sigma.sigma Y.1.1 (i + 2)).2 ≤
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
  -- step b: d_{i+1} − d_{i+2} ≤ c_i − c_{i+1} (Label-4 (15.6), even branch)
  have hcond6 := cond_15_6_Mix_Pi_2Lambda Y.1.2 i
  rw [if_pos hi] at hcond6
  have hdrop := rank_drop_le Y.1.2 i
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, X.2] using @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
  have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, Y.2] using @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hgap : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 1 ≤
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt hr1
  linarith

/-- Odd-level first-component counterpart of `KEY_Y_fst`.  At odd `i`,
(15.6) bounds the second half of `c_i-c_(i+2)` by the complementary component
of the one-step rank drop. -/
lemma KEY_Y_fst_odd {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    {i : ℕ} (hi : ¬ Even i) :
    (Sigma.sigma Y.1.1 i).1 - (Sigma.sigma Y.1.1 (i + 2)).1 ≤
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
  have hcond6 := cond_15_6_Mix_Pi_2Lambda Y.1.2 i
  rw [if_neg hi] at hcond6
  have hdrop := rank_drop_le Y.1.2 i
  have hrX0 :
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, X.2] using
      (@signature_sum_eq_rank (Chromosome.prime^[0] X.1.1))
  have hrY0 :
      (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
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
  have hgap :
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 1 ≤
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt hr1
  linarith

/-- Odd-level second-component counterpart of `KEY_Y_snd`, using (15.7). -/
lemma KEY_Y_snd_odd {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    {i : ℕ} (hi : ¬ Even i) :
    (Sigma.sigma Y.1.1 i).2 - (Sigma.sigma Y.1.1 (i + 2)).2 ≤
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
  have hcond7 := cond_15_7_Mix_Pi_2Lambda Y.1.2 i
  rw [if_neg hi] at hcond7
  have hdrop := rank_drop_le Y.1.2 i
  have hrX0 :
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, X.2] using
      (@signature_sum_eq_rank (Chromosome.prime^[0] X.1.1))
  have hrY0 :
      (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
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
  have hgap :
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 1 ≤
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt hr1
  linarith

/-- Removing one copy of the minimal gene `gm` does not change the sigma column
at levels `≥ gm.rank` (the removed gene is already annihilated). -/
private lemma shift_ge {N : ℕ} (X : nMixPi2Lambda N) (gm : Gene)
    (hgm1 : X.1.1 gm = 1) {i : ℕ} (hi : gm.rank ≤ i) :
    Sigma.sigma X.1.1 i = Sigma.sigma (X.1.1 - Finsupp.single gm 1) i := by
  have h3 : Chromosome.prime^[i] (Finsupp.single gm 1) = 0 := by
    rw [← prime_iterate_eq_zero_rank_le]
    intro g hg
    rw [Finsupp.support_single_ne_zero _ (by norm_num), Finset.mem_singleton] at hg
    subst hg; omega
  have hsub : X.1.1 = (X.1.1 - Finsupp.single gm 1) + Finsupp.single gm 1 := by
    ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : gm = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  conv_lhs => rw [hsub]
  rw [Sigma.sigma_linearity]
  simp only [Sigma.sigma, h3, map_zero, add_zero]

/-- Removing one copy of `gm` drops total multiplicity by exactly one. -/
private lemma cells_of_X {N : ℕ} (X : nMixPi2Lambda N) (gm : Gene)
    (hgm1 : X.1.1 gm = 1) :
    (X.1.1.sum fun _ m => (m : ℚ)) =
      (X.1.1 - Finsupp.single gm 1).sum (fun _ m => (m : ℚ)) + 1 := by
  have hsub : X.1.1 = (X.1.1 - Finsupp.single gm 1) + Finsupp.single gm 1 := by
    ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : gm = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  conv_lhs => rw [hsub]
  rw [Finsupp.sum_add_index (by simp) (by intros; simp),
    Finsupp.sum_single_index (by simp)]
  norm_num

/-- KEY_X (first component): under the no-pair Case 1 structure, `X`'s
`a`-component 2-step drop is the constant `r_0 - r_1 - 1` on the window above the
minimal gene `gm`.  Reuses the label-agnostic `MixLambdaPi.twostep`. -/
lemma KEY_X_fst {N : ℕ} (X : nMixPi2Lambda N) {m k : ℕ}
    {gm : Gene} (hgm_rank : gm.rank = m) (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    {i : ℕ} (hi1 : m ≤ i) (hi2 : i + 2 ≤ k) :
    (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
  have hW := shift_ge X gm hgm1 (i := i) (by rw [hgm_rank]; exact hi1)
  have hW' := shift_ge X gm hgm1 (i := i + 2) (by rw [hgm_rank]; omega)
  rw [hW, hW']
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, i + 2 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  rw [MixLambdaPi.twostep h2]
  have h4 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) :=
    @signature_sum_eq_rank _
  have h5 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      (X.1.1.prime.rank : ℚ) := by
    simpa [Sigma.sigma, Function.iterate_one] using
      @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
  rw [h4, h5, MixLambdaPi.cells, cells_of_X X gm hgm1]
  ring

/-- KEY_X (second component): the same constant `r_0 - r_1 - 1` 2-step drop for
the `b`-component, using `MixLambdaPi.twostep_snd`. -/
lemma KEY_X_snd {N : ℕ} (X : nMixPi2Lambda N) {m k : ℕ}
    {gm : Gene} (hgm_rank : gm.rank = m) (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    {i : ℕ} (hi1 : m ≤ i) (hi2 : i + 2 ≤ k) :
    (Sigma.sigma X.1.1 i).2 - (Sigma.sigma X.1.1 (i + 2)).2 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
  have hW := shift_ge X gm hgm1 (i := i) (by rw [hgm_rank]; exact hi1)
  have hW' := shift_ge X gm hgm1 (i := i + 2) (by rw [hgm_rank]; omega)
  rw [hW, hW']
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, i + 2 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  rw [MixLambdaPi.twostep_snd h2]
  have h4 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) :=
    @signature_sum_eq_rank _
  have h5 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      (X.1.1.prime.rank : ℚ) := by
    simpa [Sigma.sigma, Function.iterate_one] using
      @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
  rw [h4, h5, MixLambdaPi.cells, cells_of_X X gm hgm1]
  ring

/-- The minimal gene `gm = single gm 1` contributes a nonnegative amount to each
component drop (sigma is antitone). -/
private lemma single_drop_nonneg (gm : Gene) (i : ℕ) :
    0 ≤ (Sigma.sigma (Finsupp.single gm 1) i).1 -
        (Sigma.sigma (Finsupp.single gm 1) (i + 2)).1 ∧
      0 ≤ (Sigma.sigma (Finsupp.single gm 1) i).2 -
        (Sigma.sigma (Finsupp.single gm 1) (i + 2)).2 := by
  have hle := Sigma.antitone (Finsupp.single gm 1) (show i ≤ i + 2 by omega)
  exact ⟨by linarith [(Prod.le_def.mp hle).1], by linarith [(Prod.le_def.mp hle).2]⟩

/-- The `X = X' + gm` decomposition at the sigma level. -/
private lemma sigma_split {N : ℕ} (X : nMixPi2Lambda N) (gm : Gene)
    (hgm1 : X.1.1 gm = 1) (i : ℕ) :
    Sigma.sigma X.1.1 i =
      Sigma.sigma (X.1.1 - Finsupp.single gm 1) i +
        Sigma.sigma (Finsupp.single gm 1) i := by
  have hsub : X.1.1 = (X.1.1 - Finsupp.single gm 1) + Finsupp.single gm 1 := by
    ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : gm = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  conv_lhs => rw [hsub]
  rw [Sigma.sigma_linearity]

/-- KEY_X lower bound (first component): the `a`-drop is at least `D - 1`
everywhere the residue `X'` survives.  Valid at all even levels with `i + 2 ≤ k`,
including `i = m - 1` where `gm` is only partially alive. -/
lemma KEY_X_fst_ge {N : ℕ} (X : nMixPi2Lambda N) {k : ℕ}
    {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    {i : ℕ} (hi2 : i + 2 ≤ k) :
    (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 ≤
      (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 := by
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, i + 2 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  have hWdrop := MixLambdaPi.twostep h2
  have hsplit_i := sigma_split X gm hgm1 i
  have hsplit_i2 := sigma_split X gm hgm1 (i + 2)
  have hgm_nn := (single_drop_nonneg gm i).1
  have h4 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) :=
    @signature_sum_eq_rank _
  have h5 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      (X.1.1.prime.rank : ℚ) := by
    simpa [Sigma.sigma, Function.iterate_one] using
      @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
  rw [h4, h5, MixLambdaPi.cells, cells_of_X X gm hgm1]
  have hfst_i := congrArg Prod.fst hsplit_i
  have hfst_i2 := congrArg Prod.fst hsplit_i2
  simp only [Prod.fst_add] at hfst_i hfst_i2
  rw [hfst_i, hfst_i2]
  linarith [hWdrop, hgm_nn]

/-- KEY_X lower bound (second component). -/
lemma KEY_X_snd_ge {N : ℕ} (X : nMixPi2Lambda N) {k : ℕ}
    {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    {i : ℕ} (hi2 : i + 2 ≤ k) :
    (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 ≤
      (Sigma.sigma X.1.1 i).2 - (Sigma.sigma X.1.1 (i + 2)).2 := by
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, i + 2 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  have hWdrop := MixLambdaPi.twostep_snd h2
  have hsplit_i := sigma_split X gm hgm1 i
  have hsplit_i2 := sigma_split X gm hgm1 (i + 2)
  have hgm_nn := (single_drop_nonneg gm i).2
  have h4 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) :=
    @signature_sum_eq_rank _
  have h5 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      (X.1.1.prime.rank : ℚ) := by
    simpa [Sigma.sigma, Function.iterate_one] using
      @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
  rw [h4, h5, MixLambdaPi.cells, cells_of_X X gm hgm1]
  have hsnd_i := congrArg Prod.snd hsplit_i
  have hsnd_i2 := congrArg Prod.snd hsplit_i2
  simp only [Prod.snd_add] at hsnd_i hsnd_i2
  rw [hsnd_i, hsnd_i2]
  linarith [hWdrop, hgm_nn]

/-- Full `X`-drop at a level below the minimal rank (where every gene of `X`,
including `gm`, survives both steps): both component drops equal the count `D`. -/
lemma KEY_X_full_fst {N : ℕ} (X : nMixPi2Lambda N) {m : ℕ}
    (hmin : ∀ g ∈ X.1.1.support, m ≤ g.rank)
    {i : ℕ} (hi2 : i + 2 ≤ m) :
    (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
  have h2 : ∀ g ∈ X.1.1.support, i + 2 ≤ g.rank := by
    intro g hg; have := hmin g hg; omega
  rw [MixLambdaPi.twostep h2]
  have h4 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) :=
    @signature_sum_eq_rank _
  have h5 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      (X.1.1.prime.rank : ℚ) := by
    simpa [Sigma.sigma, Function.iterate_one] using
      @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
  rw [h4, h5, MixLambdaPi.cells]

/-- Full `X`-drop, second component. -/
lemma KEY_X_full_snd {N : ℕ} (X : nMixPi2Lambda N) {m : ℕ}
    (hmin : ∀ g ∈ X.1.1.support, m ≤ g.rank)
    {i : ℕ} (hi2 : i + 2 ≤ m) :
    (Sigma.sigma X.1.1 i).2 - (Sigma.sigma X.1.1 (i + 2)).2 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
  have h2 : ∀ g ∈ X.1.1.support, i + 2 ≤ g.rank := by
    intro g hg; have := hmin g hg; omega
  rw [MixLambdaPi.twostep_snd h2]
  have h4 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) :=
    @signature_sum_eq_rank _
  have h5 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      (X.1.1.prime.rank : ℚ) := by
    simpa [Sigma.sigma, Function.iterate_one] using
      @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
  rw [h4, h5, MixLambdaPi.cells]

private lemma single_edge_drop_fst_positive {gm : Gene} (hgm_pos : gm.type = GeneType.Positive) :
    (Sigma.sigma (Finsupp.single gm 1 : Chromosome) (gm.rank - 1)).1 -
        (Sigma.sigma (Finsupp.single gm 1 : Chromosome) (gm.rank + 1)).1 = 1 := by
  have hsingle : (Finsupp.single gm 1 : Chromosome) = Gene.ofRank gm.rank gm.type :=
    Gene.ofRank_eq_gene.symm
  rw [hsingle, Sigma.sigma, Sigma.sigma, prime_iterate_ofRank, prime_iterate_ofRank]
  have hpred : gm.rank - (gm.rank - 1) = 1 := by
    have := gm.rank_pos
    omega
  have hsucc : gm.rank - (gm.rank + 1) = 0 := by omega
  rw [hpred, hsucc, Gene.ofRank_zero, map_zero, hgm_pos, signature_ofRank_one_positive]
  norm_num

private lemma single_edge_drop_snd_negative {gm : Gene} (hgm_neg : gm.type = GeneType.Negative) :
    (Sigma.sigma (Finsupp.single gm 1 : Chromosome) (gm.rank - 1)).2 -
        (Sigma.sigma (Finsupp.single gm 1 : Chromosome) (gm.rank + 1)).2 = 1 := by
  have hsingle : (Finsupp.single gm 1 : Chromosome) = Gene.ofRank gm.rank gm.type :=
    Gene.ofRank_eq_gene.symm
  rw [hsingle, Sigma.sigma, Sigma.sigma, prime_iterate_ofRank, prime_iterate_ofRank]
  have hpred : gm.rank - (gm.rank - 1) = 1 := by
    have := gm.rank_pos
    omega
  have hsucc : gm.rank - (gm.rank + 1) = 0 := by omega
  rw [hpred, hsucc, Gene.ofRank_zero, map_zero, hgm_neg, signature_ofRank_one_negative]
  norm_num

/-- Lower-edge full drop for a positive minimal single gene.  At the boundary
`m-1 → m+1`, the positive copy contributes exactly one to the first component,
so the first-component drop is the full count `r_0-r_1`. -/
lemma KEY_X_edge_fst_positive {N : ℕ} (X : nMixPi2Lambda N) {m k : ℕ}
    {gm : Gene} (hgm_rank : gm.rank = m) (hgm_pos : gm.type = GeneType.Positive)
    (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (hwin : m + 1 ≤ k) :
    (Sigma.sigma X.1.1 (m - 1)).1 - (Sigma.sigma X.1.1 (m + 1)).1 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
  have hmpos : 1 ≤ m := by
    rw [← hgm_rank]
    exact gm.rank_pos
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, m + 1 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  have h2' : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, (m - 1) + 2 ≤ g.rank := by
    intro g hg; have := h2 g hg; omega
  have hWdrop := MixLambdaPi.twostep (W := X.1.1 - Finsupp.single gm 1)
    (i := m - 1) h2'
  have hidx : (m - 1) + 2 = m + 1 := by omega
  rw [hidx] at hWdrop
  have hsplit_i := sigma_split X gm hgm1 (m - 1)
  have hsplit_i2 := sigma_split X gm hgm1 (m + 1)
  have hgm_drop := single_edge_drop_fst_positive (gm := gm) hgm_pos
  have h4 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) :=
    @signature_sum_eq_rank _
  have h5 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      (X.1.1.prime.rank : ℚ) := by
    simpa [Sigma.sigma, Function.iterate_one] using
      @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
  rw [h4, h5, MixLambdaPi.cells, cells_of_X X gm hgm1]
  have hfst_i := congrArg Prod.fst hsplit_i
  have hfst_i2 := congrArg Prod.fst hsplit_i2
  simp only [Prod.fst_add] at hfst_i hfst_i2
  rw [hfst_i, hfst_i2]
  rw [hgm_rank] at hgm_drop
  linarith

/-- Lower-edge full drop for a negative minimal single gene, in the second
component. -/
lemma KEY_X_edge_snd_negative {N : ℕ} (X : nMixPi2Lambda N) {m k : ℕ}
    {gm : Gene} (hgm_rank : gm.rank = m) (hgm_neg : gm.type = GeneType.Negative)
    (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (hwin : m + 1 ≤ k) :
    (Sigma.sigma X.1.1 (m - 1)).2 - (Sigma.sigma X.1.1 (m + 1)).2 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
  have hmpos : 1 ≤ m := by
    rw [← hgm_rank]
    exact gm.rank_pos
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, m + 1 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  have h2' : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, (m - 1) + 2 ≤ g.rank := by
    intro g hg; have := h2 g hg; omega
  have hWdrop := MixLambdaPi.twostep_snd (W := X.1.1 - Finsupp.single gm 1)
    (i := m - 1) h2'
  have hidx : (m - 1) + 2 = m + 1 := by omega
  rw [hidx] at hWdrop
  have hsplit_i := sigma_split X gm hgm1 (m - 1)
  have hsplit_i2 := sigma_split X gm hgm1 (m + 1)
  have hgm_drop := single_edge_drop_snd_negative (gm := gm) hgm_neg
  have h4 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) :=
    @signature_sum_eq_rank _
  have h5 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      (X.1.1.prime.rank : ℚ) := by
    simpa [Sigma.sigma, Function.iterate_one] using
      @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
  rw [h4, h5, MixLambdaPi.cells, cells_of_X X gm hgm1]
  have hsnd_i := congrArg Prod.snd hsplit_i
  have hsnd_i2 := congrArg Prod.snd hsplit_i2
  simp only [Prod.snd_add] at hsnd_i hsnd_i2
  rw [hsnd_i, hsnd_i2]
  rw [hgm_rank] at hgm_drop
  linarith

/-- Even-level `a`-window propagation: from a strict seed `a_{j0} < c_{j0}` at an
even level `j0`, the strict first-component bound propagates across the even
sublevels of the window.  The `hstep` uses the `Y`-side bound `KEY_Y_fst` and the
`X`-side lower bound `KEY_X_fst_ge`, so no `m ≤ j0` hypothesis is needed. -/
lemma window_even_fst_lt {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    {k : ℕ} {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (j0 d : ℕ) (hj0_even : Even j0) (hwin : j0 + 2 * d ≤ k)
    (hseed : (Sigma.sigma X.1.1 j0).1 < (Sigma.sigma Y.1.1 j0).1) :
    ∀ t, t ≤ d →
      (Sigma.sigma X.1.1 (j0 + 2 * t)).1 < (Sigma.sigma Y.1.1 (j0 + 2 * t)).1 := by
  apply Mix2LambdaSection17.fst_propagate_window_lt (X := X.1.1) (Y := Y.1.1) j0 d hseed
  intro t ht
  have heven : Even (j0 + 2 * t) := hj0_even.add (⟨t, by ring⟩)
  have hY := KEY_Y_fst X Y hr1 heven
  have hX := KEY_X_fst_ge X (k := k) hgm1 h2nd (i := j0 + 2 * t) (by omega)
  simp only [Sigma.sigma] at hX hY ⊢
  linarith

/-- Even-level `b`-window propagation: mirror of `window_even_fst_lt`. -/
lemma window_even_snd_lt {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    {k : ℕ} {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (j0 d : ℕ) (hj0_even : Even j0) (hwin : j0 + 2 * d ≤ k)
    (hseed : (Sigma.sigma X.1.1 j0).2 < (Sigma.sigma Y.1.1 j0).2) :
    ∀ t, t ≤ d →
      (Sigma.sigma X.1.1 (j0 + 2 * t)).2 < (Sigma.sigma Y.1.1 (j0 + 2 * t)).2 := by
  apply Mix2LambdaSection17.snd_propagate_window_lt (X := X.1.1) (Y := Y.1.1) j0 d hseed
  intro t ht
  have heven : Even (j0 + 2 * t) := hj0_even.add (⟨t, by ring⟩)
  have hY := KEY_Y_snd X Y hr1 heven
  have hX := KEY_X_snd_ge X (k := k) hgm1 h2nd (i := j0 + 2 * t) (by omega)
  simp only [Sigma.sigma] at hX hY ⊢
  linarith

/-- Odd-level first-component strict propagation, using `KEY_Y_fst_odd` and
the residue lower bound `KEY_X_fst_ge`. -/
lemma window_odd_fst_lt {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    {k : ℕ} {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (j0 d : ℕ) (hj0_odd : ¬ Even j0) (hwin : j0 + 2 * d ≤ k)
    (hseed : (Sigma.sigma X.1.1 j0).1 < (Sigma.sigma Y.1.1 j0).1) :
    ∀ t, t ≤ d →
      (Sigma.sigma X.1.1 (j0 + 2 * t)).1 <
        (Sigma.sigma Y.1.1 (j0 + 2 * t)).1 := by
  apply Mix2LambdaSection17.fst_propagate_window_lt
    (X := X.1.1) (Y := Y.1.1) j0 d hseed
  intro t ht
  have hodd : ¬ Even (j0 + 2 * t) := by
    obtain ⟨q, hq⟩ := Nat.not_even_iff_odd.mp hj0_odd
    exact Nat.not_even_iff_odd.mpr ⟨q + t, by omega⟩
  have hY := KEY_Y_fst_odd X Y hr1 hodd
  have hX := KEY_X_fst_ge X (k := k) hgm1 h2nd
    (i := j0 + 2 * t) (by omega)
  simp only [Sigma.sigma] at hX hY ⊢
  linarith

/-- Odd-level second-component strict propagation. -/
lemma window_odd_snd_lt {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    {k : ℕ} {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (j0 d : ℕ) (hj0_odd : ¬ Even j0) (hwin : j0 + 2 * d ≤ k)
    (hseed : (Sigma.sigma X.1.1 j0).2 < (Sigma.sigma Y.1.1 j0).2) :
    ∀ t, t ≤ d →
      (Sigma.sigma X.1.1 (j0 + 2 * t)).2 <
        (Sigma.sigma Y.1.1 (j0 + 2 * t)).2 := by
  apply Mix2LambdaSection17.snd_propagate_window_lt
    (X := X.1.1) (Y := Y.1.1) j0 d hseed
  intro t ht
  have hodd : ¬ Even (j0 + 2 * t) := by
    obtain ⟨q, hq⟩ := Nat.not_even_iff_odd.mp hj0_odd
    exact Nat.not_even_iff_odd.mpr ⟨q + t, by omega⟩
  have hY := KEY_Y_snd_odd X Y hr1 hodd
  have hX := KEY_X_snd_ge X (k := k) hgm1 h2nd
    (i := j0 + 2 * t) (by omega)
  simp only [Sigma.sigma] at hX hY ⊢
  linarith

/-! ### Seeds for the even windows.

The even-window seeds are one-shot drop comparisons.  At an even level `i`, if
the `X`-side `a`-drop equals the full count `D = r_0 - r_1` while the `Y`-side
`a`-drop is bounded by `D - 1` (`KEY_Y_fst`), then dominance at level `i`
upgrades to a strict gap at level `i + 2`. -/

/-- Generic first-component seed: a full `X`-drop `= D` plus dominance at `i`
gives a strict gap at `i + 2`. -/
lemma seed_fst_lt {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    {i : ℕ} (hi : Even i)
    (hXdrop : (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2))
    (hdom : (Sigma.sigma X.1.1 i).1 ≤ (Sigma.sigma Y.1.1 i).1) :
    (Sigma.sigma X.1.1 (i + 2)).1 < (Sigma.sigma Y.1.1 (i + 2)).1 := by
  have hY := KEY_Y_fst X Y hr1 hi
  linarith

/-- Generic second-component seed. -/
lemma seed_snd_lt {N : ℕ} (X Y : nMixPi2Lambda N)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    {i : ℕ} (hi : Even i)
    (hXdrop : (Sigma.sigma X.1.1 i).2 - (Sigma.sigma X.1.1 (i + 2)).2 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2))
    (hdom : (Sigma.sigma X.1.1 i).2 ≤ (Sigma.sigma Y.1.1 i).2) :
    (Sigma.sigma X.1.1 (i + 2)).2 < (Sigma.sigma Y.1.1 (i + 2)).2 := by
  have hY := KEY_Y_snd X Y hr1 hi
  linarith

end MixPi2Lambda
