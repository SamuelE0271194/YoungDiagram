import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Seed
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps

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

end Mix2LambdaPi
