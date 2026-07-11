import YoungDiagram.Theorem6.MixPi2Lambda.Case34Helpers
import YoungDiagram.Theorem6.MixPi2Lambda.Type15
import YoungDiagram.Theorem6.MixPi2Lambda.Type17

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

lemma prime_iterate_rank_lt_of_sigma_ne
    {X Y : Chromosome} (hXY : X ≤ Y) {k : ℕ}
    (hne : Sigma.sigma X k ≠ Sigma.sigma Y k) :
    (Chromosome.prime^[k] X).rank < (Chromosome.prime^[k] Y).rank := by
  have hle := le_iff_dominates.mp hXY k
  change Sigma.sigma X k ≤ Sigma.sigma Y k at hle
  have hstrict :
      (Sigma.sigma X k).1 < (Sigma.sigma Y k).1 ∨
      (Sigma.sigma X k).2 < (Sigma.sigma Y k).2 := by
    by_cases hfst : (Sigma.sigma X k).1 = (Sigma.sigma Y k).1
    · right
      exact lt_of_le_of_ne hle.2 fun hsnd => hne (Prod.ext hfst hsnd)
    · left
      exact lt_of_le_of_ne hle.1 hfst
  have hsum :
      (Sigma.sigma X k).1 + (Sigma.sigma X k).2 <
      (Sigma.sigma Y k).1 + (Sigma.sigma Y k).2 := by
    rcases hstrict with h | h <;> linarith [hle.1, hle.2]
  simp only [Sigma.sigma, signature_sum_eq_rank] at hsum
  exact_mod_cast hsum

lemma signature_prime_iterate_eq_zero_of_le_zero
    {X Y : Chromosome} (hXY : X ≤ Y) {k : ℕ}
    (hYzero : Chromosome.prime^[k] Y = 0) :
    signature (Chromosome.prime^[k] X) = 0 := by
  have hle := le_iff_dominates.mp hXY k
  rw [hYzero, map_zero] at hle
  exact Prod.ext (le_antisymm hle.1
      (signature_nonneg (Chromosome.prime^[k] X)).1)
    (le_antisymm hle.2
      (signature_nonneg (Chromosome.prime^[k] X)).2)

lemma snd_pred_strict_of_succ_fst_eq
    {b₀ a₁ b₁ a₂ d₀ c₁ d₁ c₂ : ℚ}
    (hfst_succ_eq : a₂ = c₂)
    (hgap_rank_fst : a₁ + 1 ≤ c₁)
    (hgap_rank_snd : b₁ + 1 ≤ d₁)
    (hYdrop : c₁ - c₂ ≤ d₀ - d₁)
    (hXdrop : b₀ - b₁ ≤ a₁ - a₂ + 1) :
    b₀ < d₀ := by
  linarith

lemma fst_pred_strict_of_succ_snd_eq
    {a₀ b₁ a₁ b₂ c₀ d₁ c₁ d₂ : ℚ}
    (hsnd_succ_eq : b₂ = d₂)
    (hgap_rank_fst : a₁ + 1 ≤ c₁)
    (hgap_rank_snd : b₁ + 1 ≤ d₁)
    (hYdrop : d₁ - d₂ ≤ c₀ - c₁)
    (hXdrop : a₀ - a₁ ≤ b₁ - b₂ + 1) :
    a₀ < c₀ := by
  linarith

/-- Under the reduced §17 hypothesis, a nonzero positive iterate of `Y` has a
strict sigma gap in at least one component. -/
lemma prime_iterate_some_component_lt
    {N k : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hkpos : 0 < k) (hYk : Chromosome.prime^[k] Y.1.1 ≠ 0) :
    (signature (Chromosome.prime^[k] X.1.1)).1 <
        (signature (Chromosome.prime^[k] Y.1.1)).1 ∨
      (signature (Chromosome.prime^[k] X.1.1)).2 <
        (signature (Chromosome.prime^[k] Y.1.1)).2 := by
  have hle := le_iff_dominates.mp hXY.le k
  have hrank_lt := h17_1 k hkpos hYk
  have hsum :
      (signature (Chromosome.prime^[k] X.1.1)).1 +
          (signature (Chromosome.prime^[k] X.1.1)).2 <
        (signature (Chromosome.prime^[k] Y.1.1)).1 +
          (signature (Chromosome.prime^[k] Y.1.1)).2 := by
    simp only [signature_sum_eq_rank]
    exact_mod_cast hrank_lt
  by_cases hfst :
      (signature (Chromosome.prime^[k] X.1.1)).1 <
        (signature (Chromosome.prime^[k] Y.1.1)).1
  · exact Or.inl hfst
  · right
    exact lt_of_le_of_ne hle.2 fun hsnd => by
      have hfst_eq :
          (signature (Chromosome.prime^[k] X.1.1)).1 =
            (signature (Chromosome.prime^[k] Y.1.1)).1 :=
        le_antisymm hle.1 (le_of_not_gt hfst)
      linarith

/-- A directed version of `prime_iterate_some_component_lt`: either the first
component is strict, or it is not strict and the second component is strict. -/
lemma prime_iterate_fst_or_snd_lt
    {N k : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hkpos : 0 < k) (hYk : Chromosome.prime^[k] Y.1.1 ≠ 0) :
    (signature (Chromosome.prime^[k] X.1.1)).1 <
        (signature (Chromosome.prime^[k] Y.1.1)).1 ∨
      (¬ (signature (Chromosome.prime^[k] X.1.1)).1 <
          (signature (Chromosome.prime^[k] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[k] X.1.1)).2 <
          (signature (Chromosome.prime^[k] Y.1.1)).2) := by
  have hle := le_iff_dominates.mp hXY.le k
  have hrank_lt := h17_1 k hkpos hYk
  have hsum :
      (signature (Chromosome.prime^[k] X.1.1)).1 +
          (signature (Chromosome.prime^[k] X.1.1)).2 <
        (signature (Chromosome.prime^[k] Y.1.1)).1 +
          (signature (Chromosome.prime^[k] Y.1.1)).2 := by
    simp only [signature_sum_eq_rank]
    exact_mod_cast hrank_lt
  by_cases hfst :
      (signature (Chromosome.prime^[k] X.1.1)).1 <
        (signature (Chromosome.prime^[k] Y.1.1)).1
  · exact Or.inl hfst
  · refine Or.inr ⟨hfst, ?_⟩
    exact lt_of_le_of_ne hle.2 fun hsnd => by
      have hfst_eq :
          (signature (Chromosome.prime^[k] X.1.1)).1 =
            (signature (Chromosome.prime^[k] Y.1.1)).1 :=
        le_antisymm hle.1 (le_of_not_gt hfst)
      linarith

/-- The same directed split with the second component as the preferred one. -/
lemma prime_iterate_snd_or_fst_lt
    {N k : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hkpos : 0 < k) (hYk : Chromosome.prime^[k] Y.1.1 ≠ 0) :
    (signature (Chromosome.prime^[k] X.1.1)).2 <
        (signature (Chromosome.prime^[k] Y.1.1)).2 ∨
      (¬ (signature (Chromosome.prime^[k] X.1.1)).2 <
          (signature (Chromosome.prime^[k] Y.1.1)).2 ∧
        (signature (Chromosome.prime^[k] X.1.1)).1 <
          (signature (Chromosome.prime^[k] Y.1.1)).1) := by
  have hle := le_iff_dominates.mp hXY.le k
  have hrank_lt := h17_1 k hkpos hYk
  have hsum :
      (signature (Chromosome.prime^[k] X.1.1)).1 +
          (signature (Chromosome.prime^[k] X.1.1)).2 <
        (signature (Chromosome.prime^[k] Y.1.1)).1 +
          (signature (Chromosome.prime^[k] Y.1.1)).2 := by
    simp only [signature_sum_eq_rank]
    exact_mod_cast hrank_lt
  by_cases hsnd :
      (signature (Chromosome.prime^[k] X.1.1)).2 <
        (signature (Chromosome.prime^[k] Y.1.1)).2
  · exact Or.inl hsnd
  · refine Or.inr ⟨hsnd, ?_⟩
    exact lt_of_le_of_ne hle.1 fun hfst => by
      have hsnd_eq :
          (signature (Chromosome.prime^[k] X.1.1)).2 =
            (signature (Chromosome.prime^[k] Y.1.1)).2 :=
        le_antisymm hle.2 (le_of_not_gt hsnd)
      linarith

private lemma one_one_le_of_both_lt
    {X Y : Chromosome} (hX : X ∈ Mix (Pi, 2 • Lambda))
    (hY : Y ∈ Mix (Pi, 2 • Lambda)) {i : ℕ}
    (hfst : (signature (Chromosome.prime^[i] X)).1 <
        (signature (Chromosome.prime^[i] Y)).1)
    (hsnd : (signature (Chromosome.prime^[i] X)).2 <
        (signature (Chromosome.prime^[i] Y)).2) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[i] X) ≤
      signature (Chromosome.prime^[i] Y) := by
  have hXmem := Variety.prime_mem_Mix_Pi_2Lambda_iterate hX i
  have hYmem := Variety.prime_mem_Mix_Pi_2Lambda_iterate hY i
  have key : ∀ (a b : ℚ × ℚ),
      (∃ n : ℕ × ℕ, a = ((n.1 : ℚ), (n.2 : ℚ))) →
      (∃ n : ℕ × ℕ, b = ((n.1 : ℚ), (n.2 : ℚ))) →
      a.1 < b.1 → a.2 < b.2 → ((1 : ℚ), (1 : ℚ)) + a ≤ b := by
    rintro a b ⟨na, hna⟩ ⟨nb, hnb⟩ h1 h2
    subst hna hnb
    simp only at h1 h2
    rw [Prod.le_def]
    refine ⟨?_, ?_⟩
    · change (1 : ℚ) + (na.1 : ℚ) ≤ (nb.1 : ℚ)
      have hn : na.1 + 1 ≤ nb.1 := Nat.add_one_le_iff.mpr (by exact_mod_cast h1)
      have : ((na.1 : ℚ)) + 1 ≤ (nb.1 : ℚ) := by exact_mod_cast hn
      linarith
    · change (1 : ℚ) + (na.2 : ℚ) ≤ (nb.2 : ℚ)
      have hn : na.2 + 1 ≤ nb.2 := Nat.add_one_le_iff.mpr (by exact_mod_cast h2)
      have : ((na.2 : ℚ)) + 1 ≤ (nb.2 : ℚ) := by exact_mod_cast hn
      linarith
  by_cases hev : Even i
  · rw [if_pos hev] at hXmem hYmem
    exact key _ _ (Mix2LambdaSection17.signature_Mix_Pi_2Lambda_isNat hXmem)
      (Mix2LambdaSection17.signature_Mix_Pi_2Lambda_isNat hYmem) hfst hsnd
  · rw [if_neg hev] at hXmem hYmem
    exact key _ _ (Mix2LambdaSection17.signature_Mix_2Lambda_Pi_isNat hXmem)
      (Mix2LambdaSection17.signature_Mix_2Lambda_Pi_isNat hYmem) hfst hsnd

private lemma seed_strict_lt_at_even
    {X Y : Chromosome} (hX : X ∈ Mix (Pi, 2 • Lambda))
    (hY : Y ∈ Mix (Pi, 2 • Lambda)) {i : ℕ} (heven : Even i)
    (hrank : (Chromosome.prime^[i] X).rank < (Chromosome.prime^[i] Y).rank) :
    (signature (Chromosome.prime^[i] X)).1 <
        (signature (Chromosome.prime^[i] Y)).1 ∧
      (signature (Chromosome.prime^[i] X)).2 <
        (signature (Chromosome.prime^[i] Y)).2 := by
  have hXeq := Mix2LambdaSection17.signature_prime_iterate_even_eq_components_L4 hX heven
  have hYeq := Mix2LambdaSection17.signature_prime_iterate_even_eq_components_L4 hY heven
  have hXsum : (signature (Chromosome.prime^[i] X)).1 +
      (signature (Chromosome.prime^[i] X)).2 =
      ((Chromosome.prime^[i] X).rank : ℚ) := signature_sum_eq_rank
  have hYsum : (signature (Chromosome.prime^[i] Y)).1 +
      (signature (Chromosome.prime^[i] Y)).2 =
      ((Chromosome.prime^[i] Y).rank : ℚ) := signature_sum_eq_rank
  have hcast : ((Chromosome.prime^[i] X).rank : ℚ) <
      ((Chromosome.prime^[i] Y).rank : ℚ) := by exact_mod_cast hrank
  constructor <;> linarith

/-- The type10 middle-window gap `hgap_mid` from per-component strict bounds.
At every level `j` in the window the type10 slack is `(1,1)`, so dominance there
needs both signature components strictly below `Y`; integrality
(`one_one_le_of_both_lt`) then yields the `(1,1)` gap. -/
lemma type10_hgap_mid_of_components
    {N : ℕ} (X Y : nMixPi2Lambda N) (lo hi : ℕ)
    (hfst : ∀ j, lo ≤ j → j ≤ hi →
      (signature (Chromosome.prime^[j] X.1.1)).1 <
        (signature (Chromosome.prime^[j] Y.1.1)).1)
    (hsnd : ∀ j, lo ≤ j → j ≤ hi →
      (signature (Chromosome.prime^[j] X.1.1)).2 <
        (signature (Chromosome.prime^[j] Y.1.1)).2) :
    ∀ j, lo ≤ j → j ≤ hi →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
  intro j hjlo hjhi
  exact one_one_le_of_both_lt X.1.2 Y.1.2 (hfst j hjlo hjhi) (hsnd j hjlo hjhi)

/-- Type15 odd-middle positive gap from a two-cell first-component gap.  The
second component is supplied by ordinary dominance. -/
lemma type15_odd_positive_gap_of_fst_add_two
    {N j : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hfst :
      (signature (Chromosome.prime^[j] X.1.1)).1 + 2 ≤
        (signature (Chromosome.prime^[j] Y.1.1)).1) :
    ((2 : ℚ), (0 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := by
  have hle := le_iff_dominates.mp hXY.le j
  exact ⟨by simpa [Prod.fst_add, add_comm] using hfst,
    by simpa [Prod.snd_add] using hle.2⟩

/-- Type15 odd-middle negative gap from a two-cell second-component gap.  The
first component is supplied by ordinary dominance. -/
lemma type15_odd_negative_gap_of_snd_add_two
    {N j : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hsnd :
      (signature (Chromosome.prime^[j] X.1.1)).2 + 2 ≤
        (signature (Chromosome.prime^[j] Y.1.1)).2) :
    ((0 : ℚ), (2 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := by
  have hle := le_iff_dominates.mp hXY.le j
  exact ⟨by simpa [Prod.fst_add] using hle.1,
    by simpa [Prod.snd_add, add_comm] using hsnd⟩

/-- Type15 predecessor gap for a positive lower gene.  At the odd predecessor
level, strictness of the first component upgrades to one integral cell; the
second component is ordinary dominance. -/
lemma type15_pred_gap_positive
    {N j : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hodd : ¬ Even j)
    (hfst :
      (signature (Chromosome.prime^[j] X.1.1)).1 <
        (signature (Chromosome.prime^[j] Y.1.1)).1) :
    signature (Gene.ofRank 1 GeneType.Positive) +
        signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := by
  have hXj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 j
  have hYj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 j
  rw [if_neg hodd] at hXj_mem hYj_mem
  have hfst_gap :=
    Mix2LambdaSection17.add_one_le_fst_of_lt_Mix_2Lambda_Pi
      hXj_mem hYj_mem hfst
  have hle := le_iff_dominates.mp hXY.le j
  rw [signature_ofRank_one_positive]
  exact ⟨by simpa [Prod.fst_add, add_comm] using hfst_gap,
    by simpa [Prod.snd_add] using hle.2⟩

/-- Negative-sign mirror of `type15_pred_gap_positive`. -/
lemma type15_pred_gap_negative
    {N j : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hodd : ¬ Even j)
    (hsnd :
      (signature (Chromosome.prime^[j] X.1.1)).2 <
        (signature (Chromosome.prime^[j] Y.1.1)).2) :
    signature (Gene.ofRank 1 GeneType.Negative) +
        signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := by
  have hXj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 j
  have hYj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 j
  rw [if_neg hodd] at hXj_mem hYj_mem
  have hsnd_gap :=
    Mix2LambdaSection17.add_one_le_snd_of_lt_Mix_2Lambda_Pi
      hXj_mem hYj_mem hsnd
  have hle := le_iff_dominates.mp hXY.le j
  rw [signature_ofRank_one_negative]
  exact ⟨by simpa [Prod.fst_add] using hle.1,
    by simpa [Prod.snd_add, add_comm] using hsnd_gap⟩

/-- At an odd Label 4 level, an integral strict first-component gap is either
at least two cells or exactly one cell. -/
lemma odd_fst_gap_two_or_one
    {N j : ℕ} (X Y : nMixPi2Lambda N) (hodd : ¬ Even j)
    (hfst :
      (signature (Chromosome.prime^[j] X.1.1)).1 <
        (signature (Chromosome.prime^[j] Y.1.1)).1) :
    (signature (Chromosome.prime^[j] X.1.1)).1 + 2 ≤
        (signature (Chromosome.prime^[j] Y.1.1)).1 ∨
      (signature (Chromosome.prime^[j] X.1.1)).1 + 1 =
        (signature (Chromosome.prime^[j] Y.1.1)).1 := by
  have hXj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 j
  have hYj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 j
  rw [if_neg hodd] at hXj_mem hYj_mem
  obtain ⟨nx, hnx⟩ :=
    Mix2LambdaSection17.signature_Mix_2Lambda_Pi_isNat hXj_mem
  obtain ⟨ny, hny⟩ :=
    Mix2LambdaSection17.signature_Mix_2Lambda_Pi_isNat hYj_mem
  rw [hnx, hny] at hfst ⊢
  change (nx.1 : ℚ) < (ny.1 : ℚ) at hfst
  change (nx.1 : ℚ) + 2 ≤ (ny.1 : ℚ) ∨
    (nx.1 : ℚ) + 1 = (ny.1 : ℚ)
  have hnat : nx.1 < ny.1 := by exact_mod_cast hfst
  by_cases htwo : nx.1 + 2 ≤ ny.1
  · left
    exact_mod_cast htwo
  · right
    have hone : nx.1 + 1 = ny.1 := by omega
    exact_mod_cast hone

/-- Second-component mirror of `odd_fst_gap_two_or_one`. -/
lemma odd_snd_gap_two_or_one
    {N j : ℕ} (X Y : nMixPi2Lambda N) (hodd : ¬ Even j)
    (hsnd :
      (signature (Chromosome.prime^[j] X.1.1)).2 <
        (signature (Chromosome.prime^[j] Y.1.1)).2) :
    (signature (Chromosome.prime^[j] X.1.1)).2 + 2 ≤
        (signature (Chromosome.prime^[j] Y.1.1)).2 ∨
      (signature (Chromosome.prime^[j] X.1.1)).2 + 1 =
        (signature (Chromosome.prime^[j] Y.1.1)).2 := by
  have hXj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 j
  have hYj_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 j
  rw [if_neg hodd] at hXj_mem hYj_mem
  obtain ⟨nx, hnx⟩ :=
    Mix2LambdaSection17.signature_Mix_2Lambda_Pi_isNat hXj_mem
  obtain ⟨ny, hny⟩ :=
    Mix2LambdaSection17.signature_Mix_2Lambda_Pi_isNat hYj_mem
  rw [hnx, hny] at hsnd ⊢
  change (nx.2 : ℚ) < (ny.2 : ℚ) at hsnd
  change (nx.2 : ℚ) + 2 ≤ (ny.2 : ℚ) ∨
    (nx.2 : ℚ) + 1 = (ny.2 : ℚ)
  have hnat : nx.2 < ny.2 := by exact_mod_cast hsnd
  by_cases htwo : nx.2 + 2 ≤ ny.2
  · left
    exact_mod_cast htwo
  · right
    have hone : nx.2 + 1 = ny.2 := by omega
    exact_mod_cast hone

/-- Even-level middle gap from the reduced §17 rank-strict hypothesis.  At even
levels Label 4 lies in the `Pi` side, so a strict rank gap splits into strict
gaps in both signature components, then integrality gives `(1,1)` slack. -/
lemma one_one_gap_of_even_rank_lt
    {N j : ℕ} (X Y : nMixPi2Lambda N) (heven : Even j)
    (hrank :
      (Chromosome.prime^[j] X.1.1).rank <
        (Chromosome.prime^[j] Y.1.1).rank) :
    ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := by
  have hcomp := seed_strict_lt_at_even X.1.2 Y.1.2 heven hrank
  exact one_one_le_of_both_lt X.1.2 Y.1.2 hcomp.1 hcomp.2

/-- Even-level middle gap directly from the reduced §17 hypothesis once the
corresponding iterate of `Y` is known to be nonzero. -/
lemma type10_mid_gap_even_of_Y_ne
    {N j : ℕ} (X Y : nMixPi2Lambda N)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (heven : Even j) (hjpos : 0 < j)
    (hYj : Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) :=
  one_one_gap_of_even_rank_lt X Y heven (h17_1 j hjpos hYj)

/-- Type10 predecessor gap for a positive lower-moving gene.  At the predecessor
level the target contributes `signature (g⁺(1))` on the right, so only the
second component needs a strict integral gap; the first follows from dominance. -/
lemma type10_pred_gap_positive
    {N p : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hsnd :
      (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * p + 1] X.1.1) ≤
      signature (Gene.ofRank 1 .Positive) +
        signature (Chromosome.prime^[2 * p + 1] Y.1.1) := by
  have hXk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 (2 * p + 1)
  have hYk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 (2 * p + 1)
  have hodd : ¬ Even (2 * p + 1) := Nat.not_even_iff_odd.mpr ⟨p, by ring⟩
  rw [if_neg hodd] at hXk_mem hYk_mem
  have hsnd_gap :=
    Mix2LambdaSection17.add_one_le_snd_of_lt_Mix_2Lambda_Pi hXk_mem hYk_mem hsnd
  have hle := le_iff_dominates.mp hXY.le (2 * p + 1)
  rw [signature_ofRank_one_positive]
  exact ⟨by simpa [Prod.fst_add] using hle.1,
    by simpa [Prod.snd_add, add_comm] using hsnd_gap⟩

/-- Type10 predecessor gap for a negative lower-moving gene; the first component
is the strict one. -/
lemma type10_pred_gap_negative
    {N p : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hfst :
      (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * p + 1] X.1.1) ≤
      signature (Gene.ofRank 1 .Negative) +
        signature (Chromosome.prime^[2 * p + 1] Y.1.1) := by
  have hXk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 (2 * p + 1)
  have hYk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 (2 * p + 1)
  have hodd : ¬ Even (2 * p + 1) := Nat.not_even_iff_odd.mpr ⟨p, by ring⟩
  rw [if_neg hodd] at hXk_mem hYk_mem
  have hfst_gap :=
    Mix2LambdaSection17.add_one_le_fst_of_lt_Mix_2Lambda_Pi
      hXk_mem hYk_mem hfst
  have hle := le_iff_dominates.mp hXY.le (2 * p + 1)
  rw [signature_ofRank_one_negative]
  exact ⟨by simpa [Prod.fst_add, add_comm] using hfst_gap,
    by simpa [Prod.snd_add] using hle.2⟩

/-- Type10 successor gap for a positive lower-moving gene.  This is the same
odd-level integral gap used by type16, exposed under the type10 name expected
by the Case34 dispatchers. -/
lemma type10_succ_gap_positive
    {N q : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hfst :
      (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1) :
    signature (Gene.ofRank 1 .Positive) +
        signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
      signature (Chromosome.prime^[2 * q + 3] Y.1.1) :=
  type16_succ_gap_positive X Y hXY hfst

/-- Type10 successor gap for a negative lower-moving gene. -/
lemma type10_succ_gap_negative
    {N q : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hsnd :
      (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2) :
    signature (Gene.ofRank 1 .Negative) +
        signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
      signature (Chromosome.prime^[2 * q + 3] Y.1.1) :=
  type16_succ_gap_negative X Y hXY hsnd

/-- Pack the doubled-gene type10 dominance check into the standard
pred/mid/succ gap interface.  This keeps the no-pair dispatcher focused on
proving the three window gaps rather than rebuilding the source decomposition. -/
lemma type10_double_target_add_rest_le_of_gaps
    {N q : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1) (g : Gene)
    (hg : g.type = ε) (hg_rank : g.rank = 2 * q + 2)
    (hg2 : 2 ≤ X.1.1 g)
    (hgap_pred :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q + 1] X.1.1) ≤
        signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * q + 1] Y.1.1))
    (hgap_mid : ∀ j, 2 * q + 2 ≤ j → j ≤ 2 * q + 2 →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 3] Y.1.1)) :
    (Y10 (le_refl q) hε hε).1 +
        (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) ≤ Y.1.1 := by
  let restval : Chromosome := X.1.1 - Finsupp.single g 1 - Finsupp.single g 1
  have hg_eq :
      Gene.ofRank (2 * q + 2) ε = (Finsupp.single g 1 : Chromosome) := by
    rw [← hg_rank, ← hg]; exact Gene.ofRank_eq_gene (g := g)
  have hX10val :
      (X10 (le_refl q) hε hε).1 =
        Finsupp.single g 1 + Finsupp.single g 1 := by
    rw [X10_eq, hg_eq]
  have hXeq : (X10 (le_refl q) hε hε).1 + restval = X.1.1 := by
    rw [hX10val]
    exact Mix2LambdaSection17.double_single_add_rest hg2
  simpa [restval] using
    type10_target_add_rest_le_of_diagonal_gap hε hε (le_refl q) X Y hXY
      restval hXeq hgap_pred hgap_mid hgap_succ

/-- Pack the two-gene type10 dominance check into the standard pred/mid/succ
gap interface. -/
lemma type10_pair_target_add_rest_le_of_gaps
    {N q n : ℕ} {ε ε' : GeneType}
    (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized) (h_le : q ≤ n)
    (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (g₁ g₂ : Gene)
    (hg₁ : g₁.type = ε) (hg₂ : g₂.type = ε')
    (hg₁_rank : g₁.rank = 2 * q + 2) (hg₂_rank : g₂.rank = 2 * n + 2)
    (hcopy₁ : 1 ≤ X.1.1 g₁) (hcopy₂ : 1 ≤ X.1.1 g₂) (hne : g₁ ≠ g₂)
    (hgap_pred :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q + 1] X.1.1) ≤
        signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * q + 1] Y.1.1))
    (hgap_mid : ∀ j, 2 * q + 2 ≤ j → j ≤ 2 * n + 2 →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 ε') +
          signature (Chromosome.prime^[2 * n + 3] X.1.1) ≤
        signature (Chromosome.prime^[2 * n + 3] Y.1.1)) :
    (Y10 h_le hε hε').1 +
        (X.1.1 - Finsupp.single g₁ 1 - Finsupp.single g₂ 1) ≤ Y.1.1 := by
  let restval : Chromosome := X.1.1 - Finsupp.single g₁ 1 - Finsupp.single g₂ 1
  have hg₁_eq :
      Gene.ofRank (2 * q + 2) ε = (Finsupp.single g₁ 1 : Chromosome) := by
    rw [← hg₁_rank, ← hg₁]; exact Gene.ofRank_eq_gene (g := g₁)
  have hg₂_eq :
      Gene.ofRank (2 * n + 2) ε' = (Finsupp.single g₂ 1 : Chromosome) := by
    rw [← hg₂_rank, ← hg₂]; exact Gene.ofRank_eq_gene (g := g₂)
  have hX10val :
      (X10 h_le hε hε').1 = Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
    rw [X10_eq, hg₁_eq, hg₂_eq]
  have hXeq : (X10 h_le hε hε').1 + restval = X.1.1 := by
    rw [hX10val]
    exact Mix2LambdaSection17.single_pair_add_rest hcopy₁ hcopy₂ hne
  simpa [restval] using
    type10_target_add_rest_le_of_diagonal_gap hε hε' h_le X Y hXY
      restval hXeq hgap_pred hgap_mid hgap_succ

lemma signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative
    {W : Chromosome} {p : ℕ}
    (hpol : ∀ g : Gene, 0 < W g → g.type ≠ GeneType.NonPolarized)
    (hrank : ∀ g : Gene, 0 < W g → g.rank ≤ 2 * p + 1)
    (hno : W ⟨2 * p + 1, GeneType.Negative, by omega⟩ = 0) :
    (signature (Chromosome.prime^[2 * p] W)).2 = 0 := by
  rw [signature_snd, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro g hg
  by_cases hcoeff : (Chromosome.prime^[2 * p] W) g = 0
  · simp [hcoeff]
  · have hcoeff_pos : 0 < (Chromosome.prime^[2 * p] W) g :=
      Nat.pos_of_ne_zero hcoeff
    let g0 : Gene :=
      ⟨g.rank + 2 * p, g.type, Nat.le_add_right_of_le g.rank_pos⟩
    have hg0_pos : 0 < W g0 := by
      simpa [g0, prime_iterate_coeff] using hcoeff_pos
    have hg_rank : g.rank = 1 := by
      have hle := hrank g0 hg0_pos
      dsimp [g0] at hle
      change g.rank + 2 * p ≤ 2 * p + 1 at hle
      have hpos := g.rank_pos
      omega
    have hg_pol : g.type ≠ GeneType.NonPolarized := hpol g0 hg0_pos
    have hg_not_neg : g.type ≠ GeneType.Negative := by
      intro hneg
      have hg0_eq :
          g0 = ⟨2 * p + 1, GeneType.Negative, by omega⟩ := by
        ext
        · dsimp [g0]
          rw [hg_rank]
          omega
        · dsimp [g0]
          exact hneg
      have : 0 < W ⟨2 * p + 1, GeneType.Negative, by omega⟩ := by
        simpa [hg0_eq] using hg0_pos
      rw [hno] at this
      omega
    have hg_pos : g.type = GeneType.Positive := by
      cases htype : g.type
      · exact False.elim (hg_pol htype)
      · rfl
      · exact False.elim (hg_not_neg htype)
    simp [Gene.signature, hg_rank, hg_pos]

lemma signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive
    {W : Chromosome} {p : ℕ}
    (hpol : ∀ g : Gene, 0 < W g → g.type ≠ GeneType.NonPolarized)
    (hrank : ∀ g : Gene, 0 < W g → g.rank ≤ 2 * p + 1)
    (hno : W ⟨2 * p + 1, GeneType.Positive, by omega⟩ = 0) :
    (signature (Chromosome.prime^[2 * p] W)).1 = 0 := by
  rw [signature_fst, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro g hg
  by_cases hcoeff : (Chromosome.prime^[2 * p] W) g = 0
  · simp [hcoeff]
  · have hcoeff_pos : 0 < (Chromosome.prime^[2 * p] W) g :=
      Nat.pos_of_ne_zero hcoeff
    let g0 : Gene :=
      ⟨g.rank + 2 * p, g.type, Nat.le_add_right_of_le g.rank_pos⟩
    have hg0_pos : 0 < W g0 := by
      simpa [g0, prime_iterate_coeff] using hcoeff_pos
    have hg_rank : g.rank = 1 := by
      have hle := hrank g0 hg0_pos
      dsimp [g0] at hle
      change g.rank + 2 * p ≤ 2 * p + 1 at hle
      have hpos := g.rank_pos
      omega
    have hg_pol : g.type ≠ GeneType.NonPolarized := hpol g0 hg0_pos
    have hg_not_pos : g.type ≠ GeneType.Positive := by
      intro hpos
      have hg0_eq :
          g0 = ⟨2 * p + 1, GeneType.Positive, by omega⟩ := by
        ext
        · dsimp [g0]
          rw [hg_rank]
          omega
        · dsimp [g0]
          exact hpos
      have : 0 < W ⟨2 * p + 1, GeneType.Positive, by omega⟩ := by
        simpa [hg0_eq] using hg0_pos
      rw [hno] at this
      omega
    have hg_neg : g.type = GeneType.Negative := by
      cases htype : g.type
      · exact False.elim (hg_pol htype)
      · exact False.elim (hg_not_pos htype)
      · rfl
    simp [Gene.signature, hg_rank, hg_neg]

/-- Wrapper for the `2g⁺+g⁻` type16 branch using the actual equal-rank pair
rather than a pre-chosen `p` with rank `2*p+2`. -/
lemma exists_mutation_le_type16_positive_of_pair_fst_lt
    {N : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hpos : 2 ≤ X.1.1 gpos) (hneg : X.1.1 gneg = 1)
    (hfst :
      ∀ p, gpos.rank = 2 * p + 2 →
        (signature (Chromosome.prime^[2 * p + 3] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hpos_pos : 0 < X.1.1 gpos := by omega
  have heven := Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
    X.1.2 (g := gpos) hpos_pos (by rw [hgpos]; decide)
  obtain ⟨r, hr⟩ := heven
  cases r with
  | zero =>
      have hpos_rank := gpos.rank_pos
      omega
  | succ p =>
      have hp : gpos.rank = 2 * p + 2 := by
        rw [hr]
        ring
      have hgap_rank :=
        type16_diagonal_gap_rank (ε := GeneType.Positive) (by decide)
          X Y hXY hcommon h17_1 gpos gneg hgpos (by simpa using hgneg)
          hp hrank hpos (by omega)
      have hgap_succ := type16_succ_gap_positive X Y hXY (hfst p hp)
      exact exists_mutation_le_type16_diagonal (ε := GeneType.Positive) (by decide)
        X Y hXY gpos gneg hgpos (by simpa using hgneg) hp hrank hpos
        (by omega) hgap_rank hgap_succ

/-- Wrapper for the `g⁺+2g⁻` type16 branch using the actual equal-rank pair
rather than a pre-chosen `p` with rank `2*p+2`. -/
lemma exists_mutation_le_type16_negative_of_pair_snd_lt
    {N : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hpos : X.1.1 gpos = 1) (hneg : 2 ≤ X.1.1 gneg)
    (hsnd :
      ∀ p, gneg.rank = 2 * p + 2 →
        (signature (Chromosome.prime^[2 * p + 3] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).2) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hneg_pos : 0 < X.1.1 gneg := by omega
  have heven := Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
    X.1.2 (g := gneg) hneg_pos (by rw [hgneg]; decide)
  obtain ⟨r, hr⟩ := heven
  cases r with
  | zero =>
      have hneg_rank := gneg.rank_pos
      omega
  | succ p =>
      have hp : gneg.rank = 2 * p + 2 := by
        rw [hr]
        ring
      have hgap_rank :=
        type16_diagonal_gap_rank (ε := GeneType.Negative) (by decide)
          X Y hXY hcommon h17_1 gneg gpos hgneg (by simpa using hgpos)
          hp hrank.symm hneg (by omega)
      have hgap_succ := type16_succ_gap_negative X Y hXY (hsnd p hp)
      exact exists_mutation_le_type16_diagonal (ε := GeneType.Negative) (by decide)
        X Y hXY gneg gpos hgneg (by simpa using hgpos) hp hrank.symm hneg
        (by omega) hgap_rank hgap_succ

end MixPi2Lambda
