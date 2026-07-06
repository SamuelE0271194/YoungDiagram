import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Seed
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps
import YoungDiagram.Theorem6.Mix2LambdaPi.Type14
import YoungDiagram.Theorem6.Mix2LambdaPi.Type16

/-!
# §17 Case 3 negative-partner gaps (Label 3)

This file builds the value-2 even-level gaps needed for the §17 Case 3 move
`2g⁺(1)+g⁻(k) → g⁺(k+2)` / `2g⁺(1)+2g⁻(k) → 2g(k+1)`, where `k` is the minimal
*negative* rank.  The same-sign genes between `g⁺(1)` and `g⁻(k)` sit in the
complementary alternating channel and do not affect the negative-count drop, so
the gaps telescope all the way to `k` (see Djoković §17).

Since `X` is polarized it lies in `Variety.Pi`, so the X-side identities
(`b0_bi_eq_a1_ai1`, `x_side_equalities`) apply directly; only the Y-side needs the
Mix telescoped bound `a1_ai_le_b0_bi_Mix` below.
-/

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-- Mix analog of `Sigma.a1_ai_le_b0_bi_1`: telescopes `cond_15_6/7_Mix_2Lambda_Pi`.
For `Y ∈ Mix (2•Λ, Π)`, the cumulative `a`-drop is bounded by the cumulative
`b`-drop shifted by one. -/
lemma a1_ai_le_b0_bi_Mix {Y : Chromosome} (hY : Y ∈ Mix (2 • Lambda, Pi))
    {i : ℕ} (h : i ≥ 1) :
    (Sigma.sigma Y 0).2 - (Sigma.sigma Y (i - 1)).2 ≥
      (Sigma.sigma Y 1).1 - (Sigma.sigma Y i).1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => simp
  | succ j ih =>
    induction j with
    | zero =>
      have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi hY 0
      rw [if_pos (by decide : Even 0)] at h
      simpa using h
    | succ j _ =>
      by_cases hei : Even (j + 2)
      · have hei1 : ¬ Even (j + 1) := Nat.even_add_one.mp hei
        have hstep :
            (Sigma.sigma Y (j + 1)).2 - (Sigma.sigma Y (j + 2)).2 ≥
              (Sigma.sigma Y (j + 2)).1 - (Sigma.sigma Y (j + 3)).1 := by
          have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi hY (j + 1)
          rw [if_neg hei1] at h
          simpa using h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
                   show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
                   show j + 3 - 1 = j + 2 from by omega]
        linarith
      · have hei1 : Even (j + 1) := by rwa [Nat.even_add_one, not_not] at hei
        have hstep :
            (Sigma.sigma Y (j + 1)).2 - (Sigma.sigma Y (j + 2)).2 ≥
              (Sigma.sigma Y (j + 2)).1 - (Sigma.sigma Y (j + 3)).1 := by
          have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi hY (j + 1)
          rw [if_pos hei1] at h
          simpa using h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
                   show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
                   show j + 3 - 1 = j + 2 from by omega]
        linarith

/-- §17 Case 3 value-2 even gap.  For `X ∈ Pi` (polarized) and `Y ∈ Mix (2•Λ,Π)` with
`X < Y`, if all genes of `X` of rank `≤ i-1` are Positive (i.e. the minimal negative
rank exceeds `i-1`) and `i` is even, then the first component has a gap of at least `2`.

Proof: `C_i - A_i ≥ (C_1-A_1) + (B_0-D_0) + (D_{i-1}-B_{i-1}) = 1 + 0 + 1`, using the
X-side identity `b0_bi_eq_a1_ai1`, the Y-side bound `a1_ai_le_b0_bi_Mix`, level-0 equality,
and the value-1 odd gaps at levels `1` and `i-1`. -/
lemma case3_value2_even_gap {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    {i : ℕ} (hi_even : Even i) (hi2 : 2 ≤ i)
    (hpos : ∀ g ∈ X.1.1.support, g.rank ≤ i - 1 → g.type = .Positive)
    (hY1 : Chromosome.prime^[1] Y.1.1 ≠ 0)
    (hYi1 : Chromosome.prime^[i - 1] Y.1.1 ≠ 0) :
    (Sigma.sigma X.1.1 i).1 + 2 ≤ (Sigma.sigma Y.1.1 i).1 := by
  have hi1_odd : ¬ Even (i - 1) :=
    Nat.not_even_iff_odd.mpr (Nat.Even.sub_odd (by omega) hi_even (by decide))
  have hYmem : Y.1.1 ∈ Mix (2 • Lambda, Pi) := Y.1.2
  -- X-side identity: `B_0 - B_{i-1} = A_1 - A_i`.
  have hXbob := Sigma.b0_bi_eq_a1_ai1 X.1.1 hXPi (i - 1) hpos
  rw [show i - 1 + 1 = i from by omega] at hXbob
  -- Y-side bound: `D_0 - D_{i-1} ≥ C_1 - C_i`.
  have hYbob := a1_ai_le_b0_bi_Mix hYmem (i := i) (by omega)
  -- level 0
  have h0 := sigma_zero_eq X Y hXY
  have h0b : (Sigma.sigma X.1.1 0).2 = (Sigma.sigma Y.1.1 0).2 := congrArg Prod.snd h0
  -- value-1 odd gap at level 1 (first component).
  have hgap1 := type10_mid_gap_odd_of_Y_ne X Y h17_1 (j := 1) (by decide) (by omega) hY1
  have hg1f : (1 : ℚ) + (Sigma.sigma X.1.1 1).1 ≤ (Sigma.sigma Y.1.1 1).1 :=
    (Prod.le_def.mp hgap1).1
  -- value-1 odd gap at level i-1 (second component).
  have hgapi1 := type10_mid_gap_odd_of_Y_ne X Y h17_1 (j := i - 1) hi1_odd (by omega) hYi1
  have hgi1s : (1 : ℚ) + (Sigma.sigma X.1.1 (i - 1)).2 ≤ (Sigma.sigma Y.1.1 (i - 1)).2 :=
    (Prod.le_def.mp hgapi1).2
  linarith

/-- Packaged even gap for the type16/type14 assembly (positive doubled gene):
`2·sig(g⁺(1)) + σX(i) ≤ σY(i)` at even `i`. -/
lemma case3_gap_even_positive {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    {i : ℕ} (hi_even : Even i) (hi2 : 2 ≤ i)
    (hpos : ∀ g ∈ X.1.1.support, g.rank ≤ i - 1 → g.type = .Positive)
    (hY1 : Chromosome.prime^[1] Y.1.1 ≠ 0)
    (hYi1 : Chromosome.prime^[i - 1] Y.1.1 ≠ 0) :
    signature (Gene.ofRank 1 GeneType.Positive) +
        signature (Gene.ofRank 1 GeneType.Positive) +
        signature (Chromosome.prime^[i] X.1.1) ≤
      signature (Chromosome.prime^[i] Y.1.1) := by
  have hfst : (signature (Chromosome.prime^[i] X.1.1)).1 + 2 ≤
      (signature (Chromosome.prime^[i] Y.1.1)).1 :=
    case3_value2_even_gap X Y hXY hXPi h17_1 hi_even hi2 hpos hY1 hYi1
  have hsnd : (signature (Chromosome.prime^[i] X.1.1)).2 ≤
      (signature (Chromosome.prime^[i] Y.1.1)).2 := (le_iff_dominates.mp hXY.le i).2
  rw [Prod.le_def]
  refine ⟨?_, ?_⟩ <;> simp only [signature_ofRank_one_positive, Prod.fst_add, Prod.snd_add]
  · linarith
  · linarith

/-- §17 Case 3 type14 branch: doubled positive rank-one gene `g` plus a doubled
minimal negative gene `gneg` at rank `2Q+3` give a reducing step (no succ gap needed). -/
lemma exists_step_type14_neg_partner {N Q : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    (g gneg : Gene)
    (hg_rank : g.rank = 1) (hg_pos : g.type = GeneType.Positive)
    (hgneg_rank : gneg.rank = 2 * Q + 3) (hgneg_neg : gneg.type = GeneType.Negative)
    (hg_two : 2 ≤ X.1.1 g) (hgneg_two : 2 ≤ X.1.1 gneg)
    (hpos_below : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * Q + 2 → h.type = .Positive)
    (hYne : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hε : (GeneType.Positive) ≠ .NonPolarized := by decide
  have hne : g ≠ gneg := by
    intro h; rw [h, hgneg_neg] at hg_pos; exact absurd hg_pos (by decide)
  have hgap_odd : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := fun j hjlo hjhi hjodd =>
    type10_mid_gap_odd_of_Y_ne X Y h17_1 hjodd (by omega) (hYne j hjlo hjhi)
  have hgap_even : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Even j →
      (signature (Gene.ofRank 1 GeneType.Positive) +
          signature (Gene.ofRank 1 GeneType.Positive)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hjeven
    have hjge2 : 2 ≤ j := by obtain ⟨t, ht⟩ := hjeven; omega
    exact case3_gap_even_positive X Y hXY hXPi h17_1 hjeven (by omega)
      (fun h hh hr => hpos_below h hh (by omega)) (hYne 1 (by omega) (by omega))
      (hYne (j - 1) (by omega) (by omega))
  have hg_rank' : g.rank = 2 * 0 + 1 := by omega
  have hgneg_rank' : gneg.rank = 2 * (Q + 1) + 1 := by omega
  have hg_eq : Gene.ofRank (2 * 0 + 1) GeneType.Positive = (Finsupp.single g 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g); rwa [hg_rank', hg_pos] at h
  have hgneg_eq : Gene.ofRank (2 * (Q + 1) + 1) (-GeneType.Positive) =
      (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg); rwa [hgneg_rank', hgneg_neg] at h
  have hX14val : (X14 (Nat.zero_le (Q + 1)) hε).1 =
      Finsupp.single g 1 + Finsupp.single g 1 +
        Finsupp.single gneg 1 + Finsupp.single gneg 1 := by
    rw [X14_eq, hg_eq, hgneg_eq]
  have hXeq : (X14 (Nat.zero_le (Q + 1)) hε).1 +
      (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
        Finsupp.single gneg 1 - Finsupp.single gneg 1) = X.1.1 := by
    rw [hX14val]; exact Mix2LambdaSection17.double_pair_add_rest hg_two hgneg_two hne
  have hZle := type14_rank_one_target_add_rest_le_of_gaps hε X Y hXY
    (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
      Finsupp.single gneg 1 - Finsupp.single gneg 1) hXeq hgap_odd hgap_even
  exact exists_mutation_le_type14_of_genes hε (Nat.zero_le (Q + 1)) X Y g gneg
    hg_pos hgneg_neg hg_rank' hgneg_rank' hg_two hgneg_two hne hZle

/-- §17 Case 3 type16 branch: doubled positive rank-one gene `g` plus a single
minimal negative gene `gneg` at rank `2Q+3`, given the successor gap. -/
lemma exists_step_type16_neg_partner {N Q : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    (g gneg : Gene)
    (hg_rank : g.rank = 1) (hg_pos : g.type = GeneType.Positive)
    (hgneg_rank : gneg.rank = 2 * Q + 3) (hgneg_neg : gneg.type = GeneType.Negative)
    (hg_two : 2 ≤ X.1.1 g) (hgneg_one : 1 ≤ X.1.1 gneg)
    (hpos_below : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * Q + 2 → h.type = .Positive)
    (hYne : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0)
    (hgap_succ : signature (Gene.ofRank 1 GeneType.Positive) +
        signature (Chromosome.prime^[2 * Q + 4] X.1.1) ≤
      signature (Chromosome.prime^[2 * Q + 4] Y.1.1)) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hε : (GeneType.Positive) ≠ .NonPolarized := by decide
  have hne : g ≠ gneg := by
    intro h; rw [h, hgneg_neg] at hg_pos; exact absurd hg_pos (by decide)
  have hgap_odd : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := fun j hjlo hjhi hjodd =>
    type10_mid_gap_odd_of_Y_ne X Y h17_1 hjodd (by omega) (hYne j hjlo hjhi)
  have hgap_even : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Even j →
      (signature (Gene.ofRank 1 GeneType.Positive) +
          signature (Gene.ofRank 1 GeneType.Positive)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hjeven
    have hjge2 : 2 ≤ j := by obtain ⟨t, ht⟩ := hjeven; omega
    exact case3_gap_even_positive X Y hXY hXPi h17_1 hjeven (by omega)
      (fun h hh hr => hpos_below h hh (by omega)) (hYne 1 (by omega) (by omega))
      (hYne (j - 1) (by omega) (by omega))
  have hg_rank' : g.rank = 2 * 0 + 1 := by omega
  have hgneg_rank' : gneg.rank = 2 * (Q + 1) + 1 := by omega
  have hg_eq : Gene.ofRank (2 * 0 + 1) GeneType.Positive = (Finsupp.single g 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g); rwa [hg_rank', hg_pos] at h
  have hgneg_eq : Gene.ofRank (2 * (Q + 1) + 1) (-GeneType.Positive) =
      (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg); rwa [hgneg_rank', hgneg_neg] at h
  have hX16val : (X16 (Nat.zero_le (Q + 1)) hε).1 =
      Finsupp.single g 1 + Finsupp.single g 1 + Finsupp.single gneg 1 := by
    rw [X16_eq, hg_eq, hgneg_eq]
  have hXeq : (X16 (Nat.zero_le (Q + 1)) hε).1 +
      (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 - Finsupp.single gneg 1) = X.1.1 := by
    rw [hX16val]; exact Mix2LambdaSection17.double_single_pair_add_rest hg_two hgneg_one hne
  have hZle := type16_rank_one_target_add_rest_le_of_gaps hε X Y hXY
    (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 - Finsupp.single gneg 1)
    hXeq hgap_odd hgap_even hgap_succ
  exact exists_mutation_le_type16_of_genes hε (Nat.zero_le (Q + 1)) X Y g gneg
    hg_pos hgneg_neg hg_rank' hgneg_rank' hg_two hgneg_one hne hZle

end Mix2LambdaPi
