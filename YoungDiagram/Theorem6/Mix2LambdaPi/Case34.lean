import YoungDiagram.Theorem6.Mix2LambdaPi.Window
import YoungDiagram.Theorem6.Mix2LambdaPi.Type15
import YoungDiagram.Theorem6.Mix2LambdaPi.Type17

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

private lemma prime_iterate_rank_lt_of_sigma_ne
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

private lemma signature_prime_iterate_eq_zero_of_le_zero
    {X Y : Chromosome} (hXY : X ≤ Y) {k : ℕ}
    (hYzero : Chromosome.prime^[k] Y = 0) :
    signature (Chromosome.prime^[k] X) = 0 := by
  have hle := le_iff_dominates.mp hXY k
  rw [hYzero, map_zero] at hle
  exact Prod.ext (le_antisymm hle.1
      (signature_nonneg (Chromosome.prime^[k] X)).1)
    (le_antisymm hle.2
      (signature_nonneg (Chromosome.prime^[k] X)).2)

private lemma snd_pred_strict_of_succ_fst_eq
    {b₀ a₁ b₁ a₂ d₀ c₁ d₁ c₂ : ℚ}
    (hfst_succ_eq : a₂ = c₂)
    (hgap_rank_fst : a₁ + 1 ≤ c₁)
    (hgap_rank_snd : b₁ + 1 ≤ d₁)
    (hYdrop : c₁ - c₂ ≤ d₀ - d₁)
    (hXdrop : b₀ - b₁ ≤ a₁ - a₂ + 1) :
    b₀ < d₀ := by
  linarith

private lemma fst_pred_strict_of_succ_snd_eq
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
private lemma prime_iterate_some_component_lt
    {N k : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
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
private lemma prime_iterate_fst_or_snd_lt
    {N k : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
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
private lemma prime_iterate_snd_or_fst_lt
    {N k : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
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

/-- The type10 middle-window gap `hgap_mid` from per-component strict bounds.
At every level `j` in the window the type10 slack is `(1,1)`, so dominance there
needs both signature components strictly below `Y`; integrality
(`one_one_le_of_both_lt`) then yields the `(1,1)` gap. -/
private lemma type10_hgap_mid_of_components
    {N : ℕ} (X Y : nMix2LambdaPi N) (lo hi : ℕ)
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
  exact Mix2LambdaSection17.one_one_le_of_both_lt X.1.2 Y.1.2
    (hfst j hjlo hjhi) (hsnd j hjlo hjhi)

set_option maxHeartbeats 800000 in
/-- No-equal-rank-pair dispatcher (§17 final block).  Let `m` be the minimum
rank of a gene of the polarized `X`; in Label 3 every polarized gene is
odd-rank, so `m` is odd and the paper's Case 2 (`m = 2`) does not occur.  We
split on `m ≥ 3` (Case 1) versus `m = 1` (Cases 3/4). -/
private lemma exists_mutation_le_no_pair (m : ℕ)
    (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  -- `X ≠ 0`, so it has a gene of minimal rank.
  have hXne : X.1.1 ≠ 0 := by
    intro hzero
    have hrank0 : X.1.1.rank = 0 := by rw [hzero, map_zero]
    rw [X.2] at hrank0
    omega
  obtain ⟨g, hgX, hgmin⟩ :=
    Mix2LambdaSection17.exists_min_rank_gene hXne
  -- The minimal gene is polarized (so odd rank in Label 3).
  have hg_pol : g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp hXpol g (Finsupp.mem_support_iff.mpr (ne_of_gt hgX))
  have hg_odd : Odd g.rank :=
    Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
      X.1.2 hgX hg_pol
  -- `m ≥ 3` (Case 1) or `m = 1` (Cases 3/4); `m = 2` cannot occur (m is odd).
  obtain ⟨p, hp⟩ := hg_odd
  by_cases hp0 : p = 0
  · -- `g.rank = 1`: Cases 3/4 of §17 (the `m = 1` minimum-rank analysis).
    exact sorry
  · -- `g.rank = 2p+1 ≥ 3`: Case 1 of §17.
    let q := p - 1
    have hpq : p = q + 1 := by omega
    have hg_rank_q : g.rank = 2 * q + 3 := by omega
    have hg_ne_np : g.type ≠ GeneType.NonPolarized := hg_pol
    by_cases hg_two : 2 ≤ X.1.1 g
    · -- The diagonal subcase `2g^ε(2q+3) → g^ε(2q+1)+g^ε(2q+5)`.
      have hZle :
          (Y10 (le_refl q) hg_ne_np hg_ne_np).1 +
              (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) ≤ Y.1.1 := by
        -- This is the type10 dominance assembly for the doubled minimal gene.
        -- It will be discharged from the Case 1 pred/mid/succ window gaps.
        sorry
      exact exists_mutation_le_type10_of_double hg_ne_np X Y g rfl hg_rank_q hg_two hZle
    · -- Multiplicity-one subcase: choose the next gene of minimal rank in
      -- `X - g`, and use the two-gene type10 move.
      have hg_one : X.1.1 g = 1 := by omega
      let restAfterG : Chromosome := X.1.1 - Finsupp.single g 1
      have hrest_ne : restAfterG ≠ 0 := by
        -- If no second gene remains, the level-1 strict rank gap from (17.1)
        -- contradicts the fact that priming a single rank-`2q+3` gene drops
        -- rank by exactly one.
        sorry
      obtain ⟨g₂, hg₂_rest, hg₂min⟩ :=
        Mix2LambdaSection17.exists_min_rank_gene hrest_ne
      have hXg₂ : 0 < X.1.1 g₂ := by
        dsimp [restAfterG] at hg₂_rest
        exact lt_of_lt_of_le hg₂_rest (by
          exact Nat.sub_le _ _)
      have hg₂_pol : g₂.type ≠ GeneType.NonPolarized :=
        IsPolarized_def'.mp hXpol g₂ (Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂))
      have hg₂_odd : Odd g₂.rank :=
        Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
          X.1.2 hXg₂ hg₂_pol
      obtain ⟨n, hg₂_rank_raw⟩ := hg₂_odd
      have hq_succ_le_n : q + 1 ≤ n := by
        have hg_le_g₂ := hgmin g₂ hXg₂
        rw [hg_rank_q, hg₂_rank_raw] at hg_le_g₂
        omega
      have hg₂_rank_q : g₂.rank = 2 * n + 1 := hg₂_rank_raw
      -- The previous witness is off by one for type10, so choose the actual
      -- type10 parameter explicitly.
      let n10 := n - 1
      have hn10 : n = n10 + 1 := by omega
      have hq_le_n10 : q ≤ n10 := by omega
      have hg₂_rank_n10 : g₂.rank = 2 * n10 + 3 := by omega
      have hne_g_g₂ : g ≠ g₂ := by
        intro h
        subst h
        dsimp [restAfterG] at hg₂_rest
        simp [hg_one] at hg₂_rest
      have hZle :
          (Y10 hq_le_n10 hg_ne_np hg₂_pol).1 +
              (X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1) ≤ Y.1.1 := by
        -- This is the type10 dominance assembly for the minimal gene and the
        -- next gene in `X - g`; it is the main Case 1 window-propagation goal.
        sorry
      exact exists_mutation_le_type10_of_genes hg_ne_np hg₂_pol hq_le_n10
        X Y g g₂ rfl rfl hg_rank_q hg₂_rank_n10 (by omega) (by omega) hne_g_g₂ hZle

private lemma signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative
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

private lemma signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive
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
rather than a pre-chosen `p` with rank `2*p+1`. -/
private lemma exists_mutation_le_type16_positive_of_pair_fst_lt
    {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hpos : 2 ≤ X.1.1 gpos) (hneg : X.1.1 gneg = 1)
    (hfst :
      ∀ p, gpos.rank = 2 * p + 1 →
        (signature (Chromosome.prime^[2 * p + 2] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hodd := Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
    X.1.2 (g := gpos) (by omega) (by rw [hgpos]; decide)
  obtain ⟨p, hp⟩ := Nat.not_even_iff_odd.mp
    (Nat.not_even_iff_odd.mpr hodd)
  exact exists_mutation_le_type16_diagonal_positive_of_fst_lt
    X Y hXY hcommon h17_1 gpos gneg hgpos hgneg hp hrank hpos
    (by omega) (hfst p hp)

/-- Wrapper for the `g⁺+2g⁻` type16 branch using the actual equal-rank pair
rather than a pre-chosen `p` with rank `2*p+1`. -/
private lemma exists_mutation_le_type16_negative_of_pair_snd_lt
    {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hpos : X.1.1 gpos = 1) (hneg : 2 ≤ X.1.1 gneg)
    (hsnd :
      ∀ p, gneg.rank = 2 * p + 1 →
        (signature (Chromosome.prime^[2 * p + 2] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).2) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hodd := Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
    X.1.2 (g := gneg) (by omega) (by rw [hgneg]; decide)
  obtain ⟨p, hp⟩ := Nat.not_even_iff_odd.mp
    (Nat.not_even_iff_odd.mpr hodd)
  exact exists_mutation_le_type16_diagonal_negative_of_snd_lt
    X Y hXY hcommon h17_1 gpos gneg hgpos hgneg hp hrank
    (by omega) hneg (hsnd p hp)

set_option maxHeartbeats 800000 in
-- The §17 polarized remainder now carries the type11 active-window proof inline;
-- elaborating its nested sigma decompositions needs a larger local budget.
/-- The remaining polarized part of §17 after the diagonal type13 branch.
This consists of the `2+1`, `1+1`, and no-equal-rank-pair cases, using
type10--type12 and type14--type17. -/
private lemma exists_mutation_le_polarized_remaining (m : ℕ)
    (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hnodouble : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      2 ≤ X.1.1 gpos ∧ 2 ≤ X.1.1 gneg) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hpairs : ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg
  · obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXpos, hXneg,
      hmin, hmult⟩ :=
      Mix2LambdaSection17.exists_min_equal_rank_pair_multiplicity_cases
        hnodouble hpairs
    rcases hmult with htwo_one | hone_two | hone_one
    · -- Paper: `X ⊃ 2g⁺(m)+g⁻(m)`, with `m` minimal.
      -- If the successor level has the positive strict gap, this is exactly
      -- the diagonal type16 branch.  The remaining work is to derive that
      -- strict gap from (15.6)/(15.7) and the minimality hypothesis, or else
      -- to switch to the type17 subcase when the successor iterate vanishes.
      have hodd := Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
        X.1.2 (g := gpos) (by omega) (by rw [hgpos]; decide)
      obtain ⟨p, hp⟩ := Nat.not_even_iff_odd.mp
        (Nat.not_even_iff_odd.mpr hodd)
      have hbranch :
          (∀ p, gpos.rank = 2 * p + 1 →
              (signature (Chromosome.prime^[2 * p + 2] X.1.1)).1 <
                (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).1) →
            ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
        intro hfst
        exact exists_mutation_le_type16_positive_of_pair_fst_lt
          X Y hXY hcommon h17_1 gpos gneg hrank hgpos hgneg
          htwo_one.1 htwo_one.2 hfst
      by_cases hYsucc : Chromosome.prime^[2 * p + 2] Y.1.1 ≠ 0
      · -- Paper's `Y^(m+1) ≠ 0` subcase.  It remains to show that the
        -- strict component at this level is the positive one.
        have hstrict := prime_iterate_fst_or_snd_lt X Y hXY h17_1
          (k := 2 * p + 2) (by omega) hYsucc
        rcases hstrict with hfst | ⟨hnfst, hsnd⟩
        · exact exists_mutation_le_type16_diagonal_positive_of_fst_lt
            X Y hXY hcommon h17_1 gpos gneg hgpos hgneg hp hrank
            htwo_one.1 (by omega) hfst
        · -- This is the precise remaining "wrong successor component" fork.
          by_cases hp0 : p = 0
          · have hp_zero : p = 0 := hp0
            have hgneg_rank_p : gneg.rank = 2 * p + 1 := by
              rw [← hrank, hp]
            have hgap_rank_p :
                ((1 : ℚ), (1 : ℚ)) +
                    signature (Chromosome.prime^[2 * p + 1] X.1.1) ≤
                  signature (Chromosome.prime^[2 * p + 1] Y.1.1) :=
              type16_diagonal_gap_rank
                (ε := GeneType.Positive) (by decide) X Y hXY hcommon h17_1
                gpos gneg hgpos (by simpa using hgneg) hp hrank
                htwo_one.1 (by omega)
            have hle_succ := le_iff_dominates.mp hXY.le (2 * p + 2)
            have hfst_succ_eq :
                (signature (Chromosome.prime^[2 * p + 2] X.1.1)).1 =
                  (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).1 :=
              le_antisymm hle_succ.1 (le_of_not_gt hnfst)
            have hYdrop :
                (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 -
                    (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * p] Y.1.1)).2 -
                    (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 := by
              have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi
                Y.1.2 (2 * p)
              have heven : Even (2 * p) := by exact ⟨p, by ring⟩
              simpa [Sigma.sigma, heven] using h
            have hXPi : X.1.1 ∈ Pi := Variety.mem_Pi_iff.mpr hXpol
            have hXdrop :
                (signature (Chromosome.prime^[2 * p] X.1.1)).2 -
                    (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 -
                    (signature (Chromosome.prime^[2 * p + 2] X.1.1)).1 + 1 :=
              snd_drop_le_fst_drop_succ_add_one X.1.1 hXPi
                gneg hgneg_rank_p hgneg htwo_one.2
            have hgap_rank_fst_p :
                (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 + 1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 := by
              have h := hgap_rank_p.1
              change
                1 + (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 at h
              linarith
            have hgap_rank_snd_p :
                (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 + 1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 := by
              have h := hgap_rank_p.2
              change
                1 + (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 at h
              linarith
            have hsnd_pred_p :
                (signature (Chromosome.prime^[2 * p] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * p] Y.1.1)).2 := by
              exact snd_pred_strict_of_snd_succ_strict
                (hfst_succ_eq := hfst_succ_eq)
                (hgap_rank_fst := hgap_rank_fst_p)
                (hgap_rank_snd := hgap_rank_snd_p)
                (hYdrop := hYdrop)
                (hXdrop := hXdrop)
                (hsnd)
            have hsnd_zero :
                (signature X.1.1).2 < (signature Y.1.1).2 := by
              simpa [hp_zero] using hsnd_pred_p
            have hle_zero := le_iff_dominates.mp hXY.le 0
            have hfst_zero_le :
                (signature X.1.1).1 ≤ (signature Y.1.1).1 := by
              simpa using hle_zero.1
            have hsum_eq :
                (signature X.1.1).1 + (signature X.1.1).2 =
                  (signature Y.1.1).1 + (signature Y.1.1).2 := by
              rw [signature_sum_eq_rank, signature_sum_eq_rank, X.2, Y.2]
            exact False.elim (by linarith)
          · let q := p - 1
            have hpq : p = q + 1 := by omega
            have hgpos_rank_q : gpos.rank = 2 * q + 3 := by omega
            have hgneg_rank_p : gneg.rank = 2 * p + 1 := by omega
            have hgap_rank_p :
                ((1 : ℚ), (1 : ℚ)) +
                    signature (Chromosome.prime^[2 * p + 1] X.1.1) ≤
                  signature (Chromosome.prime^[2 * p + 1] Y.1.1) :=
              type16_diagonal_gap_rank
                (ε := GeneType.Positive) (by decide) X Y hXY hcommon h17_1
                gpos gneg hgpos (by simpa using hgneg) hp hrank
                htwo_one.1 (by omega)
            have hgap_rank_q :
                ((1 : ℚ), (1 : ℚ)) +
                    signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
                  signature (Chromosome.prime^[2 * q + 3] Y.1.1) := by
              have hexp : 2 * p + 1 = 2 * q + 3 := by omega
              simpa [hexp] using hgap_rank_p
            have hle_succ := le_iff_dominates.mp hXY.le (2 * p + 2)
            have hfst_succ_eq :
                (signature (Chromosome.prime^[2 * p + 2] X.1.1)).1 =
                  (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).1 :=
              le_antisymm hle_succ.1 (le_of_not_gt hnfst)
            have hYdrop :
                (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 -
                    (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * p] Y.1.1)).2 -
                    (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 := by
              have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi
                Y.1.2 (2 * p)
              have heven : Even (2 * p) := by exact ⟨p, by ring⟩
              simpa [Sigma.sigma, heven] using h
            have hXPi : X.1.1 ∈ Pi := Variety.mem_Pi_iff.mpr hXpol
            have hXdrop :
                (signature (Chromosome.prime^[2 * p] X.1.1)).2 -
                    (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 -
                    (signature (Chromosome.prime^[2 * p + 2] X.1.1)).1 + 1 :=
              snd_drop_le_fst_drop_succ_add_one X.1.1 hXPi
                gneg hgneg_rank_p hgneg htwo_one.2
            have hgap_rank_fst_p :
                (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 + 1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 := by
              have h := hgap_rank_p.1
              change
                1 + (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 at h
              linarith
            have hgap_rank_snd_p :
                (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 + 1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 := by
              have h := hgap_rank_p.2
              change
                1 + (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 at h
              linarith
            have hsnd_pred_p :
                (signature (Chromosome.prime^[2 * p] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * p] Y.1.1)).2 := by
              exact snd_pred_strict_of_snd_succ_strict
                (hfst_succ_eq := hfst_succ_eq)
                (hgap_rank_fst := hgap_rank_fst_p)
                (hgap_rank_snd := hgap_rank_snd_p)
                (hYdrop := hYdrop)
                (hXdrop := hXdrop)
                (hsnd)
            have hsnd_pred_q :
                (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 := by
              have hexp : 2 * q + 2 = 2 * p := by omega
              simpa [hexp] using hsnd_pred_p
            have hsnd_succ_q :
                (signature (Chromosome.prime^[2 * q + 4] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2 := by
              have hexp : 2 * q + 4 = 2 * p + 2 := by omega
              simpa [hexp] using hsnd
            exact exists_mutation_le_type15_positive_of_snd_lt
              X Y hXY gpos gneg hgpos hgneg hgpos_rank_q hrank
              (by omega) (by omega) hgap_rank_q hsnd_pred_q hsnd_succ_q
      · -- Paper's `Y^(m+1)=0` subcase, handled by type17.
        by_cases hp0 : p = 0
        · -- Boundary rank `m=1`; type17 would require `g⁺(m-2)`.
          exact sorry
        · let q := p - 1
          have hpq : p = q + 1 := by omega
          have hgpos_rank_q : gpos.rank = 2 * q + 3 := by omega
          have hgap_rank :
              ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
                signature (Chromosome.prime^[2 * q + 3] Y.1.1) := by
            have hgap := type16_diagonal_gap_rank
              (ε := GeneType.Positive) (by decide) X Y hXY hcommon h17_1
              gpos gneg hgpos (by simpa using hgneg) hp hrank
              htwo_one.1 (by omega)
            have hexp : 2 * p + 1 = 2 * q + 3 := by omega
            simpa [hexp] using hgap
          have hbranch17 :
              (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
                (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 →
              ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
            intro hsnd_pred
            have hgap_pred := type17_pred_gap_positive X Y hXY hsnd_pred
            exact exists_mutation_le_type17_diagonal_positive
              X Y hXY gpos gneg hgpos hgneg hgpos_rank_q hrank
              htwo_one.1 (by omega) hgap_pred hgap_rank
          have hYpred : Chromosome.prime^[2 * q + 2] Y.1.1 ≠ 0 := by
            intro hYpred_zero
            have hYrank_zero : Chromosome.prime^[2 * q + 3] Y.1.1 = 0 := by
              have hprime_zero :
                  Chromosome.prime (Chromosome.prime^[2 * q + 2] Y.1.1) = 0 := by
                rw [hYpred_zero, map_zero]
              simpa [show 2 * q + 3 = (2 * q + 2) + 1 by omega,
                Function.iterate_succ_apply'] using hprime_zero
            rw [hYrank_zero, map_zero] at hgap_rank
            have hxnonneg :
                (0 : ℚ) ≤
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 :=
              (signature_nonneg (Chromosome.prime^[2 * q + 3] X.1.1)).1
            have hle0 :
                (1 : ℚ) +
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 ≤ 0 :=
              hgap_rank.1
            linarith
          have hpred_strict := prime_iterate_snd_or_fst_lt X Y hXY h17_1
            (k := 2 * q + 2) (by omega) hYpred
          rcases hpred_strict with hsnd_pred | ⟨hnsnd_pred, hfst_pred⟩
          · exact hbranch17 hsnd_pred
          · -- Remaining type17 predecessor-level wrong-component fork.
            have hYsucc_zero_p :
                Chromosome.prime^[2 * p + 2] Y.1.1 = 0 :=
              not_not.mp hYsucc
            have hYsucc_zero_q :
                Chromosome.prime^[2 * q + 4] Y.1.1 = 0 := by
              have hexp : 2 * q + 4 = 2 * p + 2 := by omega
              simpa [hexp] using hYsucc_zero_p
            have hXsucc_sig_zero :
                signature (Chromosome.prime^[2 * q + 4] X.1.1) = 0 :=
              signature_prime_iterate_eq_zero_of_le_zero hXY.le hYsucc_zero_q
            have hYsucc_sig_zero :
                signature (Chromosome.prime^[2 * q + 4] Y.1.1) = 0 := by
              rw [hYsucc_zero_q, map_zero]
            have hfst_succ_eq :
                (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 =
                  (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1 := by
              rw [hXsucc_sig_zero, hYsucc_sig_zero]
            have hYdrop :
                (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 -
                    (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 -
                    (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 := by
              have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi
                Y.1.2 (2 * q + 2)
              have heven : Even (2 * q + 2) := by
                exact ⟨q + 1, by ring⟩
              simpa [Sigma.sigma, heven] using h
            have hXPi : X.1.1 ∈ Pi := Variety.mem_Pi_iff.mpr hXpol
            have hgneg_rank_q1 : gneg.rank = 2 * (q + 1) + 1 := by
              omega
            have hXdrop :
                (signature (Chromosome.prime^[2 * (q + 1)] X.1.1)).2 -
                    (signature (Chromosome.prime^[2 * (q + 1) + 1] X.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * (q + 1) + 1] X.1.1)).1 -
                    (signature (Chromosome.prime^[2 * (q + 1) + 2] X.1.1)).1 + 1 :=
              snd_drop_le_fst_drop_succ_add_one X.1.1 hXPi
                gneg hgneg_rank_q1 hgneg htwo_one.2
            have hgap_rank_fst :
                (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 + 1 ≤
                  (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 := by
              have h := hgap_rank.1
              change
                1 + (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 at h
              linarith
            have hgap_rank_snd :
                (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 + 1 ≤
                  (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 := by
              have h := hgap_rank.2
              change
                1 + (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 at h
              linarith
            have hsnd_pred_raw :
                (signature (Chromosome.prime^[2 * (q + 1)] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * (q + 1)] Y.1.1)).2 := by
              exact snd_pred_strict_of_succ_fst_eq
                (hfst_succ_eq := by
                  simpa [show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
                    using hfst_succ_eq)
                (hgap_rank_fst := by
                  simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega]
                    using hgap_rank_fst)
                (hgap_rank_snd := by
                  simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega]
                    using hgap_rank_snd)
                (hYdrop := by
                  simpa [show 2 * (q + 1) = 2 * q + 2 by omega,
                    show 2 * (q + 1) + 1 = 2 * q + 3 by omega,
                    show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
                    using hYdrop)
                (hXdrop := hXdrop)
            have hsnd_pred :
                (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 := by
              simpa [show 2 * (q + 1) = 2 * q + 2 by omega] using hsnd_pred_raw
            exact hbranch17 hsnd_pred
    · -- Negated version of the preceding `2+1` branch.
      have hodd := Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
        X.1.2 (g := gneg) (by omega) (by rw [hgneg]; decide)
      obtain ⟨p, hp⟩ := Nat.not_even_iff_odd.mp
        (Nat.not_even_iff_odd.mpr hodd)
      have hbranch :
          (∀ p, gneg.rank = 2 * p + 1 →
              (signature (Chromosome.prime^[2 * p + 2] X.1.1)).2 <
                (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).2) →
            ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
        intro hsnd
        exact exists_mutation_le_type16_negative_of_pair_snd_lt
          X Y hXY hcommon h17_1 gpos gneg hrank hgpos hgneg
          hone_two.1 hone_two.2 hsnd
      by_cases hYsucc : Chromosome.prime^[2 * p + 2] Y.1.1 ≠ 0
      · -- Type16 subcase for `g⁺+2g⁻`.
        have hstrict := prime_iterate_snd_or_fst_lt X Y hXY h17_1
          (k := 2 * p + 2) (by omega) hYsucc
        rcases hstrict with hsnd | ⟨hnsnd, hfst⟩
        · exact exists_mutation_le_type16_diagonal_negative_of_snd_lt
            X Y hXY hcommon h17_1 gpos gneg hgpos hgneg hp hrank
            (by omega) hone_two.2 hsnd
        · -- Negated version of the same "wrong successor component" fork.
          by_cases hp0 : p = 0
          · have hp_zero : p = 0 := hp0
            have hgpos_rank_p : gpos.rank = 2 * p + 1 := by
              rw [hrank, hp]
            have hgap_rank_p :
                ((1 : ℚ), (1 : ℚ)) +
                    signature (Chromosome.prime^[2 * p + 1] X.1.1) ≤
                  signature (Chromosome.prime^[2 * p + 1] Y.1.1) :=
              type16_diagonal_gap_rank
                (ε := GeneType.Negative) (by decide) X Y hXY hcommon h17_1
                gneg gpos hgneg (by simpa using hgpos) hp hrank.symm
                hone_two.2 (by omega)
            have hle_succ := le_iff_dominates.mp hXY.le (2 * p + 2)
            have hsnd_succ_eq :
                (signature (Chromosome.prime^[2 * p + 2] X.1.1)).2 =
                  (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).2 :=
              le_antisymm hle_succ.2 (le_of_not_gt hnsnd)
            have hYdrop :
                (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 -
                    (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * p] Y.1.1)).1 -
                    (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 := by
              have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi
                Y.1.2 (2 * p)
              have heven : Even (2 * p) := by exact ⟨p, by ring⟩
              simpa [Sigma.sigma, heven] using h
            have hXPi : X.1.1 ∈ Pi := Variety.mem_Pi_iff.mpr hXpol
            have hXdrop :
                (signature (Chromosome.prime^[2 * p] X.1.1)).1 -
                    (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 -
                    (signature (Chromosome.prime^[2 * p + 2] X.1.1)).2 + 1 :=
              fst_drop_le_snd_drop_succ_add_one X.1.1 hXPi
                gpos hgpos_rank_p hgpos hone_two.1
            have hgap_rank_fst_p :
                (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 + 1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 := by
              have h := hgap_rank_p.1
              change
                1 + (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 at h
              linarith
            have hgap_rank_snd_p :
                (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 + 1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 := by
              have h := hgap_rank_p.2
              change
                1 + (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 at h
              linarith
            have hfst_pred_p :
                (signature (Chromosome.prime^[2 * p] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * p] Y.1.1)).1 := by
              exact fst_pred_strict_of_fst_succ_strict
                (hsnd_succ_eq := hsnd_succ_eq)
                (hgap_rank_fst := hgap_rank_fst_p)
                (hgap_rank_snd := hgap_rank_snd_p)
                (hYdrop := hYdrop)
                (hXdrop := hXdrop)
                (hfst)
            have hfst_zero :
                (signature X.1.1).1 < (signature Y.1.1).1 := by
              simpa [hp_zero] using hfst_pred_p
            have hle_zero := le_iff_dominates.mp hXY.le 0
            have hsnd_zero_le :
                (signature X.1.1).2 ≤ (signature Y.1.1).2 := by
              simpa using hle_zero.2
            have hsum_eq :
                (signature X.1.1).1 + (signature X.1.1).2 =
                  (signature Y.1.1).1 + (signature Y.1.1).2 := by
              rw [signature_sum_eq_rank, signature_sum_eq_rank, X.2, Y.2]
            exact False.elim (by linarith)
          · let q := p - 1
            have hpq : p = q + 1 := by omega
            have hgneg_rank_q : gneg.rank = 2 * q + 3 := by omega
            have hgpos_rank_p : gpos.rank = 2 * p + 1 := by omega
            have hgap_rank_p :
                ((1 : ℚ), (1 : ℚ)) +
                    signature (Chromosome.prime^[2 * p + 1] X.1.1) ≤
                  signature (Chromosome.prime^[2 * p + 1] Y.1.1) :=
              type16_diagonal_gap_rank
                (ε := GeneType.Negative) (by decide) X Y hXY hcommon h17_1
                gneg gpos hgneg (by simpa using hgpos) hp hrank.symm
                hone_two.2 (by omega)
            have hgap_rank_q :
                ((1 : ℚ), (1 : ℚ)) +
                    signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
                  signature (Chromosome.prime^[2 * q + 3] Y.1.1) := by
              have hexp : 2 * p + 1 = 2 * q + 3 := by omega
              simpa [hexp] using hgap_rank_p
            have hle_succ := le_iff_dominates.mp hXY.le (2 * p + 2)
            have hsnd_succ_eq :
                (signature (Chromosome.prime^[2 * p + 2] X.1.1)).2 =
                  (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).2 :=
              le_antisymm hle_succ.2 (le_of_not_gt hnsnd)
            have hYdrop :
                (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 -
                    (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * p] Y.1.1)).1 -
                    (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 := by
              have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi
                Y.1.2 (2 * p)
              have heven : Even (2 * p) := by exact ⟨p, by ring⟩
              simpa [Sigma.sigma, heven] using h
            have hXPi : X.1.1 ∈ Pi := Variety.mem_Pi_iff.mpr hXpol
            have hXdrop :
                (signature (Chromosome.prime^[2 * p] X.1.1)).1 -
                    (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 -
                    (signature (Chromosome.prime^[2 * p + 2] X.1.1)).2 + 1 :=
              fst_drop_le_snd_drop_succ_add_one X.1.1 hXPi
                gpos hgpos_rank_p hgpos hone_two.1
            have hgap_rank_fst_p :
                (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 + 1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 := by
              have h := hgap_rank_p.1
              change
                1 + (signature (Chromosome.prime^[2 * p + 1] X.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 at h
              linarith
            have hgap_rank_snd_p :
                (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 + 1 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 := by
              have h := hgap_rank_p.2
              change
                1 + (signature (Chromosome.prime^[2 * p + 1] X.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 at h
              linarith
            have hfst_pred_p :
                (signature (Chromosome.prime^[2 * p] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * p] Y.1.1)).1 := by
              exact fst_pred_strict_of_fst_succ_strict
                (hsnd_succ_eq := hsnd_succ_eq)
                (hgap_rank_fst := hgap_rank_fst_p)
                (hgap_rank_snd := hgap_rank_snd_p)
                (hYdrop := hYdrop)
                (hXdrop := hXdrop)
                (hfst)
            have hfst_pred_q :
                (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 := by
              have hexp : 2 * q + 2 = 2 * p := by omega
              simpa [hexp] using hfst_pred_p
            have hfst_succ_q :
                (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1 := by
              have hexp : 2 * q + 4 = 2 * p + 2 := by omega
              simpa [hexp] using hfst
            exact exists_mutation_le_type15_negative_of_fst_lt
              X Y hXY gpos gneg hgpos hgneg hgneg_rank_q hrank
              (by omega) (by omega) hgap_rank_q hfst_pred_q hfst_succ_q
      · -- Type17 subcase for `g⁺+2g⁻`.
        by_cases hp0 : p = 0
        · -- Boundary rank `m=1`; type17 would require `g⁻(m-2)`.
          exact sorry
        · let q := p - 1
          have hpq : p = q + 1 := by omega
          have hgneg_rank_q : gneg.rank = 2 * q + 3 := by omega
          have hgap_rank :
              ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
                signature (Chromosome.prime^[2 * q + 3] Y.1.1) := by
            have hgap := type16_diagonal_gap_rank
              (ε := GeneType.Negative) (by decide) X Y hXY hcommon h17_1
              gneg gpos hgneg (by simpa using hgpos) hp hrank.symm
              hone_two.2 (by omega)
            have hexp : 2 * p + 1 = 2 * q + 3 := by omega
            simpa [hexp] using hgap
          have hbranch17 :
              (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
                (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 →
              ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
            intro hfst_pred
            have hgap_pred := type17_pred_gap_negative X Y hXY hfst_pred
            exact exists_mutation_le_type17_diagonal_negative
              X Y hXY gpos gneg hgpos hgneg hgneg_rank_q hrank
              (by omega) hone_two.2 hgap_pred hgap_rank
          have hYpred : Chromosome.prime^[2 * q + 2] Y.1.1 ≠ 0 := by
            intro hYpred_zero
            have hYrank_zero : Chromosome.prime^[2 * q + 3] Y.1.1 = 0 := by
              have hprime_zero :
                  Chromosome.prime (Chromosome.prime^[2 * q + 2] Y.1.1) = 0 := by
                rw [hYpred_zero, map_zero]
              simpa [show 2 * q + 3 = (2 * q + 2) + 1 by omega,
                Function.iterate_succ_apply'] using hprime_zero
            rw [hYrank_zero, map_zero] at hgap_rank
            have hxnonneg :
                (0 : ℚ) ≤
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 :=
              (signature_nonneg (Chromosome.prime^[2 * q + 3] X.1.1)).1
            have hle0 :
                (1 : ℚ) +
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 ≤ 0 :=
              hgap_rank.1
            linarith
          have hpred_strict := prime_iterate_fst_or_snd_lt X Y hXY h17_1
            (k := 2 * q + 2) (by omega) hYpred
          rcases hpred_strict with hfst_pred | ⟨hnfst_pred, hsnd_pred⟩
          · exact hbranch17 hfst_pred
          · -- Remaining type17 predecessor-level wrong-component fork.
            have hYsucc_zero_p :
                Chromosome.prime^[2 * p + 2] Y.1.1 = 0 :=
              not_not.mp hYsucc
            have hYsucc_zero_q :
                Chromosome.prime^[2 * q + 4] Y.1.1 = 0 := by
              have hexp : 2 * q + 4 = 2 * p + 2 := by omega
              simpa [hexp] using hYsucc_zero_p
            have hXsucc_sig_zero :
                signature (Chromosome.prime^[2 * q + 4] X.1.1) = 0 :=
              signature_prime_iterate_eq_zero_of_le_zero hXY.le hYsucc_zero_q
            have hYsucc_sig_zero :
                signature (Chromosome.prime^[2 * q + 4] Y.1.1) = 0 := by
              rw [hYsucc_zero_q, map_zero]
            have hsnd_succ_eq :
                (signature (Chromosome.prime^[2 * q + 4] X.1.1)).2 =
                  (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2 := by
              rw [hXsucc_sig_zero, hYsucc_sig_zero]
            have hYdrop :
                (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 -
                    (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 -
                    (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 := by
              have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi
                Y.1.2 (2 * q + 2)
              have heven : Even (2 * q + 2) := by
                exact ⟨q + 1, by ring⟩
              simpa [Sigma.sigma, heven] using h
            have hXPi : X.1.1 ∈ Pi := Variety.mem_Pi_iff.mpr hXpol
            have hgpos_rank_q1 : gpos.rank = 2 * (q + 1) + 1 := by
              omega
            have hXdrop :
                (signature (Chromosome.prime^[2 * (q + 1)] X.1.1)).1 -
                    (signature (Chromosome.prime^[2 * (q + 1) + 1] X.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * (q + 1) + 1] X.1.1)).2 -
                    (signature (Chromosome.prime^[2 * (q + 1) + 2] X.1.1)).2 + 1 :=
              fst_drop_le_snd_drop_succ_add_one X.1.1 hXPi
                gpos hgpos_rank_q1 hgpos hone_two.1
            have hgap_rank_fst :
                (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 + 1 ≤
                  (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 := by
              have h := hgap_rank.1
              change
                1 + (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 ≤
                  (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 at h
              linarith
            have hgap_rank_snd :
                (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 + 1 ≤
                  (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 := by
              have h := hgap_rank.2
              change
                1 + (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 ≤
                  (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 at h
              linarith
            have hfst_pred_raw :
                (signature (Chromosome.prime^[2 * (q + 1)] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * (q + 1)] Y.1.1)).1 := by
              exact fst_pred_strict_of_succ_snd_eq
                (hsnd_succ_eq := by
                  simpa [show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
                    using hsnd_succ_eq)
                (hgap_rank_fst := by
                  simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega]
                    using hgap_rank_fst)
                (hgap_rank_snd := by
                  simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega]
                    using hgap_rank_snd)
                (hYdrop := by
                  simpa [show 2 * (q + 1) = 2 * q + 2 by omega,
                    show 2 * (q + 1) + 1 = 2 * q + 3 by omega,
                    show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
                    using hYdrop)
                (hXdrop := hXdrop)
            have hfst_pred :
                (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 := by
              simpa [show 2 * (q + 1) = 2 * q + 2 by omega] using hfst_pred_raw
            exact hbranch17 hfst_pred
    · -- Paper: `X ⊃ g⁺(m)+g⁻(m)` but neither side has multiplicity two;
      -- this is the type10--type12 part.
      by_cases htype15 : ∃ q : ℕ, gpos.rank = 2 * q + 3 ∧
          (((signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 ∧
            (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1) ∨
          ((signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 ∧
            (signature (Chromosome.prime^[2 * q + 4] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2))
      · obtain ⟨q, hgpos_rank_q, hsame⟩ := htype15
        rcases hsame with ⟨hfst_pred, hfst_succ⟩ | ⟨hsnd_pred, hsnd_succ⟩
        · have hgneg_rank_q : gneg.rank = 2 * q + 3 := by
            rw [← hrank]
            exact hgpos_rank_q
          exact Mix2LambdaPi.exists_mutation_le_type15_negative_of_fst_lt_of_pair
            X Y hXY hcommon h17_1 gpos gneg hgpos hgneg
            hgneg_rank_q hrank (by omega) (by omega) hfst_pred hfst_succ
        · exact Mix2LambdaPi.exists_mutation_le_type15_positive_of_snd_lt_of_pair
            X Y hXY hcommon h17_1 gpos gneg hgpos hgneg
            hgpos_rank_q hrank (by omega) (by omega) hsnd_pred hsnd_succ
      · have hodd := Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
          X.1.2 (g := gpos) (by omega) (by rw [hgpos]; decide)
        obtain ⟨p, hp⟩ := Nat.not_even_iff_odd.mp
          (Nat.not_even_iff_odd.mpr hodd)
        by_cases hp0 : p = 0
        · -- Boundary rank `m=1`; handled by the separate rank-one analysis.
          exact sorry
        · let q := p - 1
          have hpq : p = q + 1 := by omega
          have hgpos_rank_q : gpos.rank = 2 * q + 3 := by omega
          have hgneg_rank_q : gneg.rank = 2 * q + 3 := by
            rw [← hrank]
            exact hgpos_rank_q
          have hgap_rank :
              ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
                signature (Chromosome.prime^[2 * q + 3] Y.1.1) :=
            type15_diagonal_gap_rank (ε := GeneType.Positive) (by decide)
              X Y hXY hcommon h17_1 gpos gneg hgpos
              (by simpa using hgneg) hgpos_rank_q hrank (by omega) (by omega)
          have hYpred : Chromosome.prime^[2 * q + 2] Y.1.1 ≠ 0 := by
            intro hYpred_zero
            have hYrank_zero : Chromosome.prime^[2 * q + 3] Y.1.1 = 0 := by
              have hprime_zero :
                  Chromosome.prime (Chromosome.prime^[2 * q + 2] Y.1.1) = 0 := by
                rw [hYpred_zero, map_zero]
              simpa [show 2 * q + 3 = (2 * q + 2) + 1 by omega,
                Function.iterate_succ_apply'] using hprime_zero
            rw [hYrank_zero, map_zero] at hgap_rank
            have hxnonneg :
                (0 : ℚ) ≤
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 :=
              (signature_nonneg (Chromosome.prime^[2 * q + 3] X.1.1)).1
            have hle0 :
                (1 : ℚ) +
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 ≤ 0 :=
              hgap_rank.1
            linarith
          by_cases hYsucc : Chromosome.prime^[2 * q + 4] Y.1.1 ≠ 0
          · have hpred_strict := prime_iterate_fst_or_snd_lt X Y hXY h17_1
              (k := 2 * q + 2) (by omega) hYpred
            have hsucc_strict := prime_iterate_fst_or_snd_lt X Y hXY h17_1
              (k := 2 * q + 4) (by omega) hYsucc
            rcases hpred_strict with hfst_pred | ⟨hnfst_pred, hsnd_pred⟩
            · rcases hsucc_strict with hfst_succ | ⟨hnfst_succ, hsnd_succ⟩
              · exact False.elim <| htype15 ⟨q, hgpos_rank_q,
                  Or.inl ⟨hfst_pred, hfst_succ⟩⟩
              · have hle_succ := le_iff_dominates.mp hXY.le (2 * q + 4)
                have hfst_succ_eq :
                    (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 =
                      (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1 :=
                  le_antisymm hle_succ.1 (le_of_not_gt hnfst_succ)
                have hYdrop :
                    (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 -
                        (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1 ≤
                      (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 -
                        (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 := by
                  have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi
                    Y.1.2 (2 * q + 2)
                  have heven : Even (2 * q + 2) := by
                    exact ⟨q + 1, by ring⟩
                  simpa [Sigma.sigma, heven] using h
                have hXPi : X.1.1 ∈ Pi := Variety.mem_Pi_iff.mpr hXpol
                have hXdrop :
                    (signature (Chromosome.prime^[2 * (q + 1)] X.1.1)).2 -
                        (signature (Chromosome.prime^[2 * (q + 1) + 1] X.1.1)).2 ≤
                      (signature (Chromosome.prime^[2 * (q + 1) + 1] X.1.1)).1 -
                        (signature (Chromosome.prime^[2 * (q + 1) + 2] X.1.1)).1 + 1 :=
                  snd_drop_le_fst_drop_succ_add_one X.1.1 hXPi
                    gneg (by omega) hgneg hone_one.2
                have hgap_rank_fst :
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 + 1 ≤
                      (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 := by
                  have h := hgap_rank.1
                  change
                    1 + (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 ≤
                      (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 at h
                  linarith
                have hgap_rank_snd :
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 + 1 ≤
                      (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 := by
                  have h := hgap_rank.2
                  change
                    1 + (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 ≤
                      (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 at h
                  linarith
                have hsnd_pred_raw :
                    (signature (Chromosome.prime^[2 * (q + 1)] X.1.1)).2 <
                      (signature (Chromosome.prime^[2 * (q + 1)] Y.1.1)).2 := by
                  exact snd_pred_strict_of_snd_succ_strict
                    (hfst_succ_eq := by
                      simpa [show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
                        using hfst_succ_eq)
                    (hgap_rank_fst := by
                      simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega]
                        using hgap_rank_fst)
                    (hgap_rank_snd := by
                      simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega]
                        using hgap_rank_snd)
                    (hYdrop := by
                      simpa [show 2 * (q + 1) = 2 * q + 2 by omega,
                        show 2 * (q + 1) + 1 = 2 * q + 3 by omega,
                        show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
                        using hYdrop)
                    (hXdrop := hXdrop)
                    hsnd_succ
                have hsnd_pred' :
                    (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
                      (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 := by
                  simpa [show 2 * (q + 1) = 2 * q + 2 by omega] using hsnd_pred_raw
                exact Mix2LambdaPi.exists_mutation_le_type15_positive_of_snd_lt_of_pair
                  X Y hXY hcommon h17_1 gpos gneg hgpos hgneg
                  hgpos_rank_q hrank (by omega) (by omega) hsnd_pred' hsnd_succ
            · rcases hsucc_strict with hfst_succ | ⟨hnfst_succ, hsnd_succ⟩
              · have hle_succ := le_iff_dominates.mp hXY.le (2 * q + 4)
                have hsnd_succ_eq :
                    (signature (Chromosome.prime^[2 * q + 4] X.1.1)).2 =
                      (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2 :=
                  le_antisymm hle_succ.2 (le_of_not_gt (by
                    intro hsnd_succ'
                    exact htype15 ⟨q, hgpos_rank_q,
                      Or.inr ⟨hsnd_pred, hsnd_succ'⟩⟩))
                have hYdrop :
                    (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 -
                        (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2 ≤
                      (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 -
                        (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 := by
                  have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi
                    Y.1.2 (2 * q + 2)
                  have heven : Even (2 * q + 2) := by
                    exact ⟨q + 1, by ring⟩
                  simpa [Sigma.sigma, heven] using h
                have hXPi : X.1.1 ∈ Pi := Variety.mem_Pi_iff.mpr hXpol
                have hXdrop :
                    (signature (Chromosome.prime^[2 * (q + 1)] X.1.1)).1 -
                        (signature (Chromosome.prime^[2 * (q + 1) + 1] X.1.1)).1 ≤
                      (signature (Chromosome.prime^[2 * (q + 1) + 1] X.1.1)).2 -
                        (signature (Chromosome.prime^[2 * (q + 1) + 2] X.1.1)).2 + 1 :=
                  fst_drop_le_snd_drop_succ_add_one X.1.1 hXPi
                    gpos (by omega) hgpos hone_one.1
                have hgap_rank_fst :
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 + 1 ≤
                      (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 := by
                  have h := hgap_rank.1
                  change
                    1 + (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 ≤
                      (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 at h
                  linarith
                have hgap_rank_snd :
                    (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 + 1 ≤
                      (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 := by
                  have h := hgap_rank.2
                  change
                    1 + (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 ≤
                      (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 at h
                  linarith
                have hfst_pred_raw :
                    (signature (Chromosome.prime^[2 * (q + 1)] X.1.1)).1 <
                      (signature (Chromosome.prime^[2 * (q + 1)] Y.1.1)).1 := by
                  exact fst_pred_strict_of_fst_succ_strict
                    (hsnd_succ_eq := by
                      simpa [show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
                        using hsnd_succ_eq)
                    (hgap_rank_fst := by
                      simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega]
                        using hgap_rank_fst)
                    (hgap_rank_snd := by
                      simpa [show 2 * (q + 1) + 1 = 2 * q + 3 by omega]
                        using hgap_rank_snd)
                    (hYdrop := by
                      simpa [show 2 * (q + 1) = 2 * q + 2 by omega,
                        show 2 * (q + 1) + 1 = 2 * q + 3 by omega,
                        show 2 * (q + 1) + 2 = 2 * q + 4 by omega]
                        using hYdrop)
                    (hXdrop := hXdrop)
                    hfst_succ
                have hfst_pred' :
                    (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
                      (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 := by
                  simpa [show 2 * (q + 1) = 2 * q + 2 by omega] using hfst_pred_raw
                exact Mix2LambdaPi.exists_mutation_le_type15_negative_of_fst_lt_of_pair
                  X Y hXY hcommon h17_1 gpos gneg hgpos hgneg
                  hgneg_rank_q hrank (by omega) (by omega) hfst_pred' hfst_succ
              · exact False.elim <| htype15 ⟨q, hgpos_rank_q,
                  Or.inr ⟨hsnd_pred, hsnd_succ⟩⟩
          · -- If `Y^(m+1)=0`, the paper switches to the remaining-gene
            -- type11/type12 subcase.
            have hYsucc_zero :
                Chromosome.prime^[2 * q + 4] Y.1.1 = 0 :=
              not_not.mp hYsucc
            have hne_pos_neg : gpos ≠ gneg := by
              intro h
              have ht := congrArg Gene.type h
              rw [hgpos, hgneg] at ht
              contradiction
            have hY_double_np_succ :
                2 ≤ Y.1.1 ⟨2 * q + 4, GeneType.NonPolarized, by omega⟩ := by
              let Ytop : Chromosome := Chromosome.prime^[2 * q + 3] Y.1.1
              have hYtop_ne : Ytop ≠ 0 := by
                intro hzero
                have h := hgap_rank.1
                change Chromosome.prime^[2 * q + 3] Y.1.1 = 0 at hzero
                rw [hzero, map_zero] at h
                norm_num at h
                have hXnonneg' :
                    0 ≤
                      (signature
                        (Chromosome.prime^[2 * q]
                          (Chromosome.prime (Chromosome.prime
                            (Chromosome.prime X.1.1))))).1 :=
                  (signature_nonneg _).1
                linarith
              obtain ⟨gtop, hgtop_support⟩ :=
                Finsupp.support_nonempty_iff.mpr hYtop_ne
              have hgtop_pos : 0 < Ytop gtop :=
                Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hgtop_support)
              have hYtop_prime : Ytop.prime = 0 := by
                change Chromosome.prime (Chromosome.prime^[2 * q + 3] Y.1.1) = 0
                simpa [Function.iterate_succ_apply',
                  show 2 * q + 3 + 1 = 2 * q + 4 by omega]
                  using hYsucc_zero
              have hgtop_rank : gtop.rank = 1 :=
                rank_one_of_prime_eq_zero hYtop_prime hgtop_support
              have htop_odd : ¬ Even (2 * q + 3) :=
                Nat.not_even_iff_odd.mpr ⟨q + 1, by ring⟩
              have hYtop_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate
                Y.1.2 (2 * q + 3)
              rw [if_neg htop_odd] at hYtop_mem
              have hgtop_odd_rank : Odd gtop.rank := by
                rw [hgtop_rank]
                exact ⟨0, rfl⟩
              have hgtop_oddPart :
                  0 < (Chromosome.oddPart Ytop) gtop := by
                rw [oddPart_eq, Finsupp.filter_apply, if_pos hgtop_odd_rank]
                exact hgtop_pos
              have hgtop_type :
                  gtop.type = GeneType.NonPolarized :=
                Mix2LambdaSection17.type_eq_nonpolarized_of_mem_twoLambda
                  hYtop_mem.2 hgtop_oddPart
              have htwo_odd :
                  2 ≤ (Chromosome.oddPart Ytop) gtop :=
                Mix2LambdaSection17.two_le_coeff_of_mem_twoLambda
                  hYtop_mem.2 hgtop_oddPart
              have htwo_top : 2 ≤ Ytop gtop := by
                rw [oddPart_eq, Finsupp.filter_apply, if_pos hgtop_odd_rank] at htwo_odd
                exact htwo_odd
              let gone : Gene := ⟨1, GeneType.NonPolarized, le_rfl⟩
              have hgtop_eq : gtop = gone := by
                ext
                · exact hgtop_rank
                · exact hgtop_type
              have htwo_one : 2 ≤ Ytop gone := by
                simpa [hgtop_eq] using htwo_top
              have hcoeff := prime_iterate_coeff (2 * q + 3) Y.1.1 gone
              have hgene :
                  (⟨gone.rank + (2 * q + 3), gone.type,
                    Nat.le_add_right_of_le gone.rank_pos⟩ : Gene) =
                    ⟨2 * q + 4, GeneType.NonPolarized, by omega⟩ := by
                ext
                · simp [gone]
                  omega
                · simp [gone]
              change 2 ≤ (Chromosome.prime^[2 * q + 3] Y.1.1) gone at htwo_one
              rw [hcoeff, hgene] at htwo_one
              exact htwo_one
            by_cases hrest_zero :
                X.1.1 - Finsupp.single gpos 1 -
                    Finsupp.single gneg 1 = 0
            · -- Boundary subcase: after deleting the rank-`2q+3` pair,
              -- no polarized source remains for type11/type12.
              let restPair : Chromosome :=
                X.1.1 - Finsupp.single gpos 1 -
                  Finsupp.single gneg 1
              have hX_pair_decomp :
                  Finsupp.single gpos 1 + Finsupp.single gneg 1 +
                      restPair = X.1.1 :=
                Mix2LambdaSection17.single_pair_add_rest
                  (by omega) (by omega) hne_pos_neg
              have hrest_zero' : restPair = 0 := by
                dsimp [restPair]
                exact hrest_zero
              have hXeq_pair :
                  X.1.1 = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
                rw [← hX_pair_decomp, hrest_zero', add_zero]
              have hXrank_pair :
                  X.1.1.rank = 2 * q + 3 + (2 * q + 3) := by
                rw [hXeq_pair, map_add, rank_single, rank_single,
                  hgpos_rank_q, hgneg_rank_q]
                simp
              let gNPsucc : Gene :=
                ⟨2 * q + 4, GeneType.NonPolarized, by omega⟩
              have hYsucc_pos : 0 < Y.1.1 gNPsucc := by
                exact lt_of_lt_of_le (by omega) hY_double_np_succ
              let Yminus : Chromosome := Y.1.1 - Finsupp.single gNPsucc 1
              have hYsub_rank :
                  Yminus.rank =
                    Y.1.1.rank - gNPsucc.rank :=
                rank_sub_single hYsucc_pos
              have hYsub_g_pos :
                  0 < Yminus gNPsucc := by
                dsimp [Yminus, gNPsucc]
                simp
                omega
              have hg_le_Ysub_rank :
                  gNPsucc.rank ≤
                    Yminus.rank := by
                exact le_trans
                  (le_maxRank gNPsucc
                    (Finsupp.mem_support_iff.mpr (ne_of_gt hYsub_g_pos)))
                  (maxRank_le_rank _)
              have hYrank_lower : 2 * (2 * q + 4) ≤ Y.1.1.rank := by
                rw [hYsub_rank] at hg_le_Ysub_rank
                change 2 * q + 4 ≤ Y.1.1.rank - (2 * q + 4) at hg_le_Ysub_rank
                omega
              have hXYrank_eq : X.1.1.rank = Y.1.1.rank := by
                rw [X.2, Y.2]
              have hbad : 2 * (2 * q + 4) ≤ 2 * q + 3 + (2 * q + 3) := by
                rw [← hXrank_pair, hXYrank_eq]
                exact hYrank_lower
              omega
            · obtain ⟨gε, hgε_rest, hgεX, hne_ε_pos, hne_ε_neg, hgε_max⟩ :=
                Mix2LambdaSection17.exists_max_rank_gene_of_single_pair_rest_ne_zero
                  hone_one.1 hone_one.2 hne_pos_neg hrest_zero
              have hgε_pol : gε.type ≠ .NonPolarized :=
                IsPolarized_def'.mp hXpol gε
                  (Finsupp.mem_support_iff.mpr hgεX.ne')
              have hgε_odd :
                  Odd gε.rank :=
                Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
                  X.1.2 hgεX hgε_pol
              have hgε_rank_le : gε.rank ≤ 2 * q + 4 :=
                Mix2LambdaSection17.rank_le_of_le_prime_zero
                  hXY.le hYsucc_zero hgεX
              rcases Mix2LambdaSection17.odd_rank_le_even_succ_cases
                  hgε_odd hgε_rank_le with hgε_rank_one | ⟨t, ht_le, hgε_rank_t⟩
              · -- Rank-one remaining gene: this is the low-rank boundary of
                -- the type11/type12 fork.  The maximality of `gε` pins the
                -- whole remainder to rank one, while the diagonal pair
                -- minimality forbids both rank-one signs from appearing.
                let restPair : Chromosome :=
                  X.1.1 - Finsupp.single gpos 1 -
                    Finsupp.single gneg 1
                have hX_pair_decomp :
                    Finsupp.single gpos 1 + Finsupp.single gneg 1 +
                        restPair = X.1.1 :=
                  Mix2LambdaSection17.single_pair_add_rest
                    (by omega) (by omega) hne_pos_neg
                have hrest_all_rank_one :
                    ∀ l : Gene, 0 < restPair l → l.rank = 1 := by
                  intro l hl
                  have hle_l : l.rank ≤ gε.rank :=
                    hgε_max l (by simpa [restPair] using hl)
                  rw [hgε_rank_one] at hle_l
                  exact Nat.le_antisymm hle_l l.rank_pos
                have hrest_no_rank_one_pair :
                    ¬ (0 <
                          restPair ⟨1, GeneType.Positive, le_rfl⟩ ∧
                        0 <
                          restPair ⟨1, GeneType.Negative, le_rfl⟩) := by
                  rintro ⟨hpos1, hneg1⟩
                  have hposX :
                      0 < X.1.1 ⟨1, GeneType.Positive, le_rfl⟩ := by
                    rw [← hX_pair_decomp]
                    exact lt_of_lt_of_le hpos1 (Nat.le_add_left _ _)
                  have hnegX :
                      0 < X.1.1 ⟨1, GeneType.Negative, le_rfl⟩ := by
                    rw [← hX_pair_decomp]
                    exact lt_of_lt_of_le hneg1 (Nat.le_add_left _ _)
                  have hmin_le :=
                    hmin ⟨1, GeneType.Positive, le_rfl⟩
                      ⟨1, GeneType.Negative, le_rfl⟩ rfl rfl rfl
                      hposX hnegX
                  rw [hgpos_rank_q] at hmin_le
                  change 2 * q + 3 ≤ 1 at hmin_le
                  omega
                have hXrank_decomp :
                    X.1.1.rank =
                      2 * q + 3 + (2 * q + 3) + restPair.rank := by
                  rw [← hX_pair_decomp, map_add, map_add, rank_single,
                    rank_single, hgpos_rank_q, hgneg_rank_q]
                  simp
                let gNPsucc : Gene :=
                  ⟨2 * q + 4, GeneType.NonPolarized, by omega⟩
                have hYsucc_pos : 0 < Y.1.1 gNPsucc := by
                  exact lt_of_lt_of_le (by omega) hY_double_np_succ
                let Yminus : Chromosome := Y.1.1 - Finsupp.single gNPsucc 1
                have hYsub_rank :
                    Yminus.rank = Y.1.1.rank - gNPsucc.rank :=
                  rank_sub_single hYsucc_pos
                have hYsub_g_pos :
                    0 < Yminus gNPsucc := by
                  dsimp [Yminus, gNPsucc]
                  simp
                  omega
                have hg_le_Ysub_rank :
                    gNPsucc.rank ≤ Yminus.rank := by
                  exact le_trans
                    (le_maxRank gNPsucc
                      (Finsupp.mem_support_iff.mpr (ne_of_gt hYsub_g_pos)))
                    (maxRank_le_rank _)
                have hYrank_lower : 2 * (2 * q + 4) ≤ Y.1.1.rank := by
                  rw [hYsub_rank] at hg_le_Ysub_rank
                  change 2 * q + 4 ≤ Y.1.1.rank - (2 * q + 4) at hg_le_Ysub_rank
                  omega
                have hXYrank_eq : X.1.1.rank = Y.1.1.rank := by
                  rw [X.2, Y.2]
                have hrest_rank_ge_two : 2 ≤ restPair.rank := by
                  have hlower :
                      2 * (2 * q + 4) ≤
                        2 * q + 3 + (2 * q + 3) + restPair.rank := by
                    rw [← hXrank_decomp, hXYrank_eq]
                    exact hYrank_lower
                  omega
                have hrest_pol :
                    ∀ l : Gene, 0 < restPair l →
                      l.type ≠ GeneType.NonPolarized := by
                  intro l hl
                  have hXl : 0 < X.1.1 l := by
                    rw [← hX_pair_decomp]
                    exact lt_of_lt_of_le hl (Nat.le_add_left _ _)
                  exact IsPolarized_def'.mp hXpol l
                    (Finsupp.mem_support_iff.mpr (ne_of_gt hXl))
                let gOnePos : Gene := ⟨1, GeneType.Positive, le_rfl⟩
                let gOneNeg : Gene := ⟨1, GeneType.Negative, le_rfl⟩
                have hrest_support_rank_one :
                    restPair =
                      Finsupp.single gOnePos (restPair gOnePos) +
                        Finsupp.single gOneNeg (restPair gOneNeg) := by
                  ext l
                  by_cases hlpos : l = gOnePos
                  · subst hlpos
                    simp [gOnePos, gOneNeg]
                  · by_cases hlneg : l = gOneNeg
                    · subst hlneg
                      simp [gOnePos, gOneNeg]
                    · have hlzero : restPair l = 0 := by
                        by_contra hlne
                        have hl : 0 < restPair l := Nat.pos_of_ne_zero hlne
                        have hlrank : l.rank = 1 := hrest_all_rank_one l hl
                        have hlpol : l.type ≠ GeneType.NonPolarized :=
                          hrest_pol l hl
                        cases htype : l.type with
                        | NonPolarized => exact hlpol htype
                        | Positive =>
                            exact hlpos (Gene.ext hlrank htype)
                        | Negative =>
                            exact hlneg (Gene.ext hlrank htype)
                      simp [gOnePos, gOneNeg, hlpos, hlneg, hlzero]
                have hrest_rank_eq_coeffs :
                    restPair.rank =
                      restPair gOnePos + restPair gOneNeg := by
                  rw [hrest_support_rank_one, map_add, rank_single,
                    rank_single]
                  simp [gOnePos, gOneNeg]
                have hrest_double_rank_one :
                    2 ≤ restPair gOnePos ∨ 2 ≤ restPair gOneNeg := by
                  have hsum_ge :
                      2 ≤ restPair gOnePos + restPair gOneNeg := by
                    rw [← hrest_rank_eq_coeffs]
                    exact hrest_rank_ge_two
                  by_cases hpos2 : 2 ≤ restPair gOnePos
                  · exact Or.inl hpos2
                  · right
                    by_contra hneg2
                    have hpair :
                        0 < restPair gOnePos ∧ 0 < restPair gOneNeg := by
                      constructor <;> omega
                    exact hrest_no_rank_one_pair (by
                      simpa [gOnePos, gOneNeg] using hpair)
                exact sorry
              · have ht_lt : t < q := by
                  by_contra hnot
                  have htq : t = q := by omega
                  cases htype : gε.type with
                  | NonPolarized => exact hgε_pol htype
                  | Positive =>
                      have heq : gε = gpos := by
                        apply Gene.ext
                        · rw [hgε_rank_t, hgpos_rank_q, htq]
                        · rw [htype, hgpos]
                      exact hne_ε_pos heq
                  | Negative =>
                      have heq : gε = gneg := by
                        apply Gene.ext
                        · rw [hgε_rank_t, hgneg_rank_q, htq]
                        · rw [htype, hgneg]
                      exact hne_ε_neg heq
                have hno_opp_at_t :
                    X.1.1 ⟨2 * t + 3, -gε.type, by omega⟩ = 0 := by
                  by_contra hnonzero
                  have hopp_pos :
                      0 < X.1.1 ⟨2 * t + 3, -gε.type, by omega⟩ :=
                    Nat.pos_of_ne_zero hnonzero
                  cases htype : gε.type with
                  | NonPolarized => exact hgε_pol htype
                  | Positive =>
                      have hmin_le := hmin gε ⟨2 * t + 3, -gε.type, by omega⟩
                        (by rw [hgε_rank_t])
                        htype
                        (by simp [htype])
                        hgεX
                        hopp_pos
                      rw [hgpos_rank_q, hgε_rank_t] at hmin_le
                      omega
                  | Negative =>
                      have hmin_le := hmin ⟨2 * t + 3, -gε.type, by omega⟩ gε
                        (by rw [hgε_rank_t])
                        (by simp [htype])
                        htype
                        hopp_pos
                        hgεX
                      rw [hgpos_rank_q] at hmin_le
                      change 2 * q + 3 ≤ 2 * t + 3 at hmin_le
                      omega
                exact Mix2LambdaPi.exists_mutation_le_type11_of_genes_with_diagonal_gap
                  (ε := gε.type) hgε_pol ht_le X Y hXY
                  gε gpos gneg rfl hgpos hgneg hgε_rank_t hgpos_rank_q
                  hrank (by omega) (by omega) (by omega)
                  hne_ε_pos hne_ε_neg hne_pos_neg
                  (by
                    -- First active level of the type11 profile: only the
                    -- component opposite to `gε` is needed.
                    cases htype : gε.type with
                    | NonPolarized => exact False.elim (hgε_pol htype)
                    | Positive =>
                        exact type17_pred_gap_positive (q := t) X Y hXY (by
                          -- Paper: `X` has no `g⁻(k)` by minimality of `m`;
                          -- this is the remaining directed predecessor gap.
                          let restPair : Chromosome :=
                            X.1.1 - Finsupp.single gpos 1 -
                              Finsupp.single gneg 1
                          have hX_pair_decomp :
                              Finsupp.single gpos 1 + Finsupp.single gneg 1 +
                                  restPair = X.1.1 :=
                            Mix2LambdaSection17.single_pair_add_rest
                              (by omega) (by omega) hne_pos_neg
                          have hrest_pol :
                              ∀ l : Gene, 0 < restPair l →
                                l.type ≠ GeneType.NonPolarized := by
                            intro l hl
                            have hXl : 0 < X.1.1 l := by
                              rw [← hX_pair_decomp]
                              exact lt_of_lt_of_le hl
                                (Nat.le_add_left _ _)
                            exact IsPolarized_def'.mp hXpol l
                              (Finsupp.mem_support_iff.mpr (ne_of_gt hXl))
                          have hrest_rank :
                              ∀ l : Gene, 0 < restPair l → l.rank ≤ 2 * (t + 1) + 1 := by
                            intro l hl
                            have hle_l : l.rank ≤ gε.rank := hgε_max l hl
                            rw [hgε_rank_t] at hle_l
                            omega
                          have hrest_no_neg :
                              restPair ⟨2 * (t + 1) + 1, GeneType.Negative, by omega⟩ = 0 := by
                            have hgene :
                                (⟨2 * (t + 1) + 1, GeneType.Negative, by omega⟩ : Gene) =
                                  ⟨2 * t + 3, -gε.type, by omega⟩ := by
                              ext
                              · ring
                              · simp [htype]
                            have hnot_pos :
                                (⟨2 * (t + 1) + 1, GeneType.Negative, by omega⟩ : Gene) ≠
                                  gpos := by
                              intro h
                              have hr := congrArg Gene.rank h
                              rw [hgpos_rank_q] at hr
                              change 2 * (t + 1) + 1 = 2 * q + 3 at hr
                              omega
                            have hnot_neg :
                                (⟨2 * (t + 1) + 1, GeneType.Negative, by omega⟩ : Gene) ≠
                                  gneg := by
                              intro h
                              have hr := congrArg Gene.rank h
                              rw [hgneg_rank_q] at hr
                              change 2 * (t + 1) + 1 = 2 * q + 3 at hr
                              omega
                            dsimp [restPair]
                            simp [hgene, hno_opp_at_t]
                          have hrest_snd_zero :
                              (signature (Chromosome.prime^[2 * t + 2] restPair)).2 = 0 := by
                            simpa [show 2 * (t + 1) = 2 * t + 2 by omega] using
                              signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative
                                (W := restPair) (p := t + 1)
                                hrest_pol hrest_rank hrest_no_neg
                          have hX_snd_pair :
                              (signature (Chromosome.prime^[2 * t + 2] X.1.1)).2 =
                                (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome))).2 := by
                            conv_lhs => rw [← hX_pair_decomp]
                            rw [iterate_map_add, map_add]
                            change
                              (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome))).2 +
                                  (signature (Chromosome.prime^[2 * t + 2] restPair)).2 =
                                (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome))).2
                            rw [hrest_snd_zero]
                            ring
                          have hpos_single :
                              Gene.ofRank (2 * q + 3) GeneType.Positive =
                                (Finsupp.single gpos 1 : Chromosome) := by
                            have h := Gene.ofRank_eq_gene (g := gpos)
                            rwa [hgpos_rank_q, hgpos] at h
                          have hneg_single :
                              Gene.ofRank (2 * q + 3) GeneType.Negative =
                                (Finsupp.single gneg 1 : Chromosome) := by
                            have h := Gene.ofRank_eq_gene (g := gneg)
                            rw [hgneg, hgneg_rank_q] at h
                            exact h
                          let gNPsucc : Gene :=
                            ⟨2 * q + 4, GeneType.NonPolarized, by omega⟩
                          have hnp_single :
                              Gene.ofRank (2 * q + 4) GeneType.NonPolarized =
                                (Finsupp.single gNPsucc 1 : Chromosome) := by
                            have h := Gene.ofRank_eq_gene (g := gNPsucc)
                            rwa [show gNPsucc.rank = 2 * q + 4 by rfl,
                              show gNPsucc.type = GeneType.NonPolarized by rfl] at h
                          have hdouble_pair_sig :
                              signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 :
                                    Chromosome)) =
                                ((1 : ℚ), (1 : ℚ)) +
                                  signature (Chromosome.prime^[2 * t + 2]
                                    (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                      Chromosome)) := by
                            conv_lhs =>
                              rw [← hnp_single]
                            conv_rhs =>
                              rw [← hpos_single, ← hneg_single]
                            simp only [iterate_map_add, prime_iterate_ofRank, map_add]
                            have hsucc_rank :
                                2 * q + 4 - (2 * t + 2) =
                                  (2 * q + 3 - (2 * t + 2)) + 1 := by omega
                            rw [hsucc_rank, signature_ofRank_nonPolarized]
                            have hPN := signature_sum_ofRank_neg_eq_rank
                              (k := 2 * q + 3 - (2 * t + 2))
                              (ε := GeneType.Positive)
                            rw [GeneType.neg_positive] at hPN
                            rw [hPN]
                            ext <;> simp [add_halves] <;> ring
                          have hY_ge_double :
                              signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 :
                                    Chromosome)) ≤
                                signature (Chromosome.prime^[2 * t + 2] Y.1.1) := by
                            let yRest : Chromosome :=
                              Y.1.1 - Finsupp.single gNPsucc 1 -
                                Finsupp.single gNPsucc 1
                            have hY_decomp :
                                Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 +
                                    yRest = Y.1.1 :=
                              Mix2LambdaSection17.double_single_add_rest
                                hY_double_np_succ
                            have hY_decomp' :
                                (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1) +
                                    yRest = Y.1.1 := by
                              rw [← hY_decomp]
                            rw [← hY_decomp']
                            conv_rhs =>
                              rw [iterate_map_add, map_add]
                            exact le_add_of_nonneg_right (signature_nonneg _)
                          have hdouble_snd :
                              (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 :
                                    Chromosome))).2 =
                                1 + (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome))).2 := by
                            have := congrArg Prod.snd hdouble_pair_sig
                            simpa using this
                          have hY_snd_ge := hY_ge_double.2
                          rw [hdouble_snd] at hY_snd_ge
                          rw [hX_snd_pair]
                          linarith)
                    | Negative =>
                        exact type17_pred_gap_negative (q := t) X Y hXY (by
                          -- Symmetric directed predecessor gap.
                          let restPair : Chromosome :=
                            X.1.1 - Finsupp.single gpos 1 -
                              Finsupp.single gneg 1
                          have hX_pair_decomp :
                              Finsupp.single gpos 1 + Finsupp.single gneg 1 +
                                  restPair = X.1.1 :=
                            Mix2LambdaSection17.single_pair_add_rest
                              (by omega) (by omega) hne_pos_neg
                          have hrest_pol :
                              ∀ l : Gene, 0 < restPair l →
                                l.type ≠ GeneType.NonPolarized := by
                            intro l hl
                            have hXl : 0 < X.1.1 l := by
                              rw [← hX_pair_decomp]
                              exact lt_of_lt_of_le hl
                                (Nat.le_add_left _ _)
                            exact IsPolarized_def'.mp hXpol l
                              (Finsupp.mem_support_iff.mpr (ne_of_gt hXl))
                          have hrest_rank :
                              ∀ l : Gene, 0 < restPair l → l.rank ≤ 2 * (t + 1) + 1 := by
                            intro l hl
                            have hle_l : l.rank ≤ gε.rank := hgε_max l hl
                            rw [hgε_rank_t] at hle_l
                            omega
                          have hrest_no_pos :
                              restPair ⟨2 * (t + 1) + 1, GeneType.Positive, by omega⟩ = 0 := by
                            have hgene :
                                (⟨2 * (t + 1) + 1, GeneType.Positive, by omega⟩ : Gene) =
                                  ⟨2 * t + 3, -gε.type, by omega⟩ := by
                              ext
                              · ring
                              · simp [htype]
                            dsimp [restPair]
                            simp [hgene, hno_opp_at_t]
                          have hrest_fst_zero :
                              (signature (Chromosome.prime^[2 * t + 2] restPair)).1 = 0 := by
                            simpa [show 2 * (t + 1) = 2 * t + 2 by omega] using
                              signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive
                                (W := restPair) (p := t + 1)
                                hrest_pol hrest_rank hrest_no_pos
                          have hX_fst_pair :
                              (signature (Chromosome.prime^[2 * t + 2] X.1.1)).1 =
                                (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome))).1 := by
                            conv_lhs => rw [← hX_pair_decomp]
                            rw [iterate_map_add, map_add]
                            change
                              (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome))).1 +
                                  (signature (Chromosome.prime^[2 * t + 2] restPair)).1 =
                                (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome))).1
                            rw [hrest_fst_zero]
                            ring
                          have hpos_single :
                              Gene.ofRank (2 * q + 3) GeneType.Positive =
                                (Finsupp.single gpos 1 : Chromosome) := by
                            have h := Gene.ofRank_eq_gene (g := gpos)
                            rwa [hgpos_rank_q, hgpos] at h
                          have hneg_single :
                              Gene.ofRank (2 * q + 3) GeneType.Negative =
                                (Finsupp.single gneg 1 : Chromosome) := by
                            have h := Gene.ofRank_eq_gene (g := gneg)
                            rw [hgneg, hgneg_rank_q] at h
                            exact h
                          let gNPsucc : Gene :=
                            ⟨2 * q + 4, GeneType.NonPolarized, by omega⟩
                          have hnp_single :
                              Gene.ofRank (2 * q + 4) GeneType.NonPolarized =
                                (Finsupp.single gNPsucc 1 : Chromosome) := by
                            have h := Gene.ofRank_eq_gene (g := gNPsucc)
                            rwa [show gNPsucc.rank = 2 * q + 4 by rfl,
                              show gNPsucc.type = GeneType.NonPolarized by rfl] at h
                          have hdouble_pair_sig :
                              signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 :
                                    Chromosome)) =
                                ((1 : ℚ), (1 : ℚ)) +
                                  signature (Chromosome.prime^[2 * t + 2]
                                    (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                      Chromosome)) := by
                            conv_lhs =>
                              rw [← hnp_single]
                            conv_rhs =>
                              rw [← hpos_single, ← hneg_single]
                            simp only [iterate_map_add, prime_iterate_ofRank, map_add]
                            have hsucc_rank :
                                2 * q + 4 - (2 * t + 2) =
                                  (2 * q + 3 - (2 * t + 2)) + 1 := by omega
                            rw [hsucc_rank, signature_ofRank_nonPolarized]
                            have hPN := signature_sum_ofRank_neg_eq_rank
                              (k := 2 * q + 3 - (2 * t + 2))
                              (ε := GeneType.Positive)
                            rw [GeneType.neg_positive] at hPN
                            rw [hPN]
                            ext <;> simp [add_halves] <;> ring
                          have hY_ge_double :
                              signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 :
                                    Chromosome)) ≤
                                signature (Chromosome.prime^[2 * t + 2] Y.1.1) := by
                            let yRest : Chromosome :=
                              Y.1.1 - Finsupp.single gNPsucc 1 -
                                Finsupp.single gNPsucc 1
                            have hY_decomp :
                                Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 +
                                    yRest = Y.1.1 :=
                              Mix2LambdaSection17.double_single_add_rest
                                hY_double_np_succ
                            have hY_decomp' :
                                (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1) +
                                    yRest = Y.1.1 := by
                              rw [← hY_decomp]
                            rw [← hY_decomp']
                            conv_rhs =>
                              rw [iterate_map_add, map_add]
                            exact le_add_of_nonneg_right (signature_nonneg _)
                          have hdouble_fst :
                              (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 :
                                    Chromosome))).1 =
                                1 + (signature (Chromosome.prime^[2 * t + 2]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome))).1 := by
                            have := congrArg Prod.fst hdouble_pair_sig
                            simpa using this
                          have hY_fst_ge := hY_ge_double.1
                          rw [hdouble_fst] at hY_fst_ge
                          rw [hX_fst_pair]
                          linarith))
                  (by
                    -- This is the remaining active-window diagonal gap for
                    -- the middle part of the paper's type11 subcase.
                    intro j hjlo hj
                    by_cases hjtop : j = 2 * q + 3
                    · subst j
                      exact hgap_rank
                    · by_cases hjeven : Even j
                      · let restPair : Chromosome :=
                            X.1.1 - Finsupp.single gpos 1 -
                              Finsupp.single gneg 1
                        have hrestPair_zero :
                            Chromosome.prime^[j] restPair = 0 := by
                          apply prime_iterate_eq_zero_rank_le.mp
                          intro l hl
                          have hlpos : 0 < restPair l :=
                            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hl)
                          have hle_l : l.rank ≤ gε.rank :=
                            hgε_max l hlpos
                          rw [hgε_rank_t] at hle_l
                          omega
                        have hX_pair_decomp :
                            Finsupp.single gpos 1 + Finsupp.single gneg 1 +
                                restPair = X.1.1 :=
                          Mix2LambdaSection17.single_pair_add_rest
                            (by omega) (by omega) hne_pos_neg
                        have hXj_pair_sig :
                            signature (Chromosome.prime^[j] X.1.1) =
                              signature (Chromosome.prime^[j]
                                (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                  Chromosome)) := by
                          conv_lhs => rw [← hX_pair_decomp]
                          rw [iterate_map_add, map_add, hrestPair_zero, map_zero, add_zero]
                        have hpos_single :
                            Gene.ofRank (2 * q + 3) GeneType.Positive =
                              (Finsupp.single gpos 1 : Chromosome) := by
                          have h := Gene.ofRank_eq_gene (g := gpos)
                          rwa [hgpos_rank_q, hgpos] at h
                        have hneg_single :
                            Gene.ofRank (2 * q + 3) GeneType.Negative =
                              (Finsupp.single gneg 1 : Chromosome) := by
                          have h := Gene.ofRank_eq_gene (g := gneg)
                          rw [hgneg, hgneg_rank_q] at h
                          exact h
                        let gNPsucc : Gene :=
                          ⟨2 * q + 4, GeneType.NonPolarized, by omega⟩
                        have hnp_single :
                            Gene.ofRank (2 * q + 4) GeneType.NonPolarized =
                              (Finsupp.single gNPsucc 1 : Chromosome) := by
                          have h := Gene.ofRank_eq_gene (g := gNPsucc)
                          rwa [show gNPsucc.rank = 2 * q + 4 by rfl,
                            show gNPsucc.type = GeneType.NonPolarized by rfl] at h
                        have hXj_eq_components :
                            (signature (Chromosome.prime^[j] X.1.1)).1 =
                              (signature (Chromosome.prime^[j] X.1.1)).2 := by
                          rw [hXj_pair_sig]
                          conv_lhs =>
                            rw [← hpos_single, ← hneg_single]
                          conv_rhs =>
                            rw [← hpos_single, ← hneg_single]
                          simp only [iterate_map_add, prime_iterate_ofRank, map_add]
                          have hpair := signature_sum_ofRank_neg_eq_rank
                            (k := 2 * q + 3 - j) (ε := GeneType.Positive)
                          rw [GeneType.neg_positive] at hpair
                          rw [hpair]
                          rfl
                        have hdouble_pair_sig :
                            signature (Chromosome.prime^[j]
                                (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 :
                                  Chromosome)) =
                              ((1 : ℚ), (1 : ℚ)) +
                                signature (Chromosome.prime^[j]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome)) := by
                          conv_lhs =>
                            rw [← hnp_single]
                          conv_rhs =>
                            rw [← hpos_single, ← hneg_single]
                          simp only [iterate_map_add, prime_iterate_ofRank, map_add]
                          have hsucc_rank :
                              2 * q + 4 - j = (2 * q + 3 - j) + 1 := by omega
                          rw [hsucc_rank, signature_ofRank_nonPolarized]
                          have hPN := signature_sum_ofRank_neg_eq_rank
                            (k := 2 * q + 3 - j) (ε := GeneType.Positive)
                          rw [GeneType.neg_positive] at hPN
                          rw [hPN]
                          ext <;> simp [add_halves] <;> ring
                        have hY_ge_double :
                            signature (Chromosome.prime^[j]
                                (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 :
                                  Chromosome)) ≤
                              signature (Chromosome.prime^[j] Y.1.1) := by
                          let yRest : Chromosome :=
                            Y.1.1 - Finsupp.single gNPsucc 1 -
                              Finsupp.single gNPsucc 1
                          have hY_decomp :
                              Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 +
                                  yRest = Y.1.1 :=
                            Mix2LambdaSection17.double_single_add_rest
                              hY_double_np_succ
                          have hY_decomp' :
                              (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1) +
                                  yRest = Y.1.1 := by
                            rw [← hY_decomp]
                          rw [← hY_decomp']
                          conv_rhs =>
                            rw [iterate_map_add, map_add]
                          exact le_add_of_nonneg_right (signature_nonneg _)
                        calc
                          ((1 : ℚ), (1 : ℚ)) +
                              signature (Chromosome.prime^[j] X.1.1)
                              = ((1 : ℚ), (1 : ℚ)) +
                                signature (Chromosome.prime^[j]
                                  (Finsupp.single gpos 1 + Finsupp.single gneg 1 :
                                    Chromosome)) := by rw [hXj_pair_sig]
                          _ = signature (Chromosome.prime^[j]
                                (Finsupp.single gNPsucc 1 + Finsupp.single gNPsucc 1 :
                                  Chromosome)) := hdouble_pair_sig.symm
                          _ ≤ signature (Chromosome.prime^[j] Y.1.1) := hY_ge_double
                      · have hjlt : j < 2 * q + 3 := by omega
                        have hj_pred : j ≤ 2 * q + 2 := by omega
                        have hYj :
                            Chromosome.prime^[j] Y.1.1 ≠ 0 :=
                          Chromosome.prime_iterate_ne_zero_if_prime_ne
                            hj_pred hYpred
                        have hle_j := le_iff_dominates.mp hXY.le j
                        have hne_j :
                            signature (Chromosome.prime^[j] X.1.1) ≠
                              signature (Chromosome.prime^[j] Y.1.1) := by
                          intro heq
                          have hrank_lt := h17_1 j (by omega) hYj
                          have := congr_arg (fun q : ℚ × ℚ => q.1 + q.2) heq
                          simp only [signature_sum_eq_rank] at this
                          exact (ne_of_lt hrank_lt) (by exact_mod_cast this)
                        have hXj_mem :=
                          Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 j
                        have hYj_mem :=
                          Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 j
                        rw [if_neg hjeven] at hXj_mem hYj_mem
                        exact Mix2LambdaSection17.one_pair_add_le_of_lt_Mix_Pi_2Lambda
                          hXj_mem hYj_mem hle_j hne_j)
  · -- No equal-rank positive/negative pair remains; this is the final
    -- minimum-rank part of §17, using type14/type15 and the boundary cases.
    exact exists_mutation_le_no_pair m X Y hXY hcommon h17_1 hXpol hpairs

/-! ## Section 17 core after the induction and lifting reductions

The joint Label 3/4 induction first removes common genes and handles every
positive level at which the two sigma columns agree.  Consequently this file
starts precisely from condition (17.1) of Djoković: whenever `prime^[k] Y` is
nonzero at a positive level, the two sigma columns are unequal.  The remaining
proof is the type9--type17 classification from §17. -/

/-- The primitive-classification core of §17 for `Mix (2 • Lambda, Pi)`.

The hypotheses are disjointness and the negation of a positive sigma-agreement
level.  The latter is the Lean form of the reduction leading to (17.1). -/
lemma exists_mutation_le_reduced (m : ℕ)
    (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬ ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬ ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank := by
    intro k hkpos hYkne
    apply prime_iterate_rank_lt_of_sigma_ne hXY.le
    intro hsig
    exact hsigeq ⟨k, hkpos, hYkne, hsig⟩
  push Not at hcommon
  by_cases hNP : ∃ g : Gene, 0 < X.1.1 g ∧ g.type = .NonPolarized
  · obtain ⟨g, hXg, hgNP⟩ := hNP
    exact exists_mutation_le_of_nonpolarized X Y hXY hcommon h17_1 g hXg hgNP
  · push Not at hNP
    -- From here on `X` is polarized; this is the remaining type10--type17
    -- classification in §17.
    have hXpol : X.1.1.IsPolarized := by
      rw [IsPolarized_def']
      intro g hg
      exact hNP g (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg))
    by_cases hdouble : ∃ (gpos gneg : Gene),
        gpos.rank = gneg.rank ∧
        gpos.type = .Positive ∧ gneg.type = .Negative ∧
        2 ≤ X.1.1 gpos ∧ 2 ≤ X.1.1 gneg
    · obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXpos2, hXneg2⟩ := hdouble
      exact exists_mutation_le_of_double_pair X Y hXY hcommon h17_1
        gpos gneg hrank hgpos hgneg hXpos2 hXneg2
    · exact exists_mutation_le_polarized_remaining m X Y hXY hcommon h17_1
        hXpol hdouble

end Mix2LambdaPi
