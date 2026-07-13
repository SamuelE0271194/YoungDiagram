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

/-- Sigma columns of `-W` are the swapped columns of `W`. -/
private lemma np_sigma_neg_swap (W : Chromosome) (k : ℕ) :
    Sigma.sigma (-W) k = (Sigma.sigma W k).swap := by
  simp only [Sigma.sigma, ← Chromosome.prime_iterate_neg, signature_neg]

/-- The sign-dual chromosome of a rank-`N` element of `Mix (2•Λ, Π)`. -/
private noncomputable def npNeg {N : ℕ} (X : nMix2LambdaPi N) : nMix2LambdaPi N :=
  ⟨-X.1, by rw [Mix.tLambda_Pi_neg_val, Chromosome.rank_neg]; exact X.2⟩

private lemma npNeg_val {N : ℕ} (X : nMix2LambdaPi N) : (npNeg X).1.1 = -(X.1.1) := rfl

/-- Telescoped `a`-drop bound for `Y ∈ Mix (2•Λ,Π)` (first-component mirror). -/
private lemma np_mix_a1_ai_le_b0_bi_1 {Z : Chromosome} (hZ : Z ∈ Mix (2 • Lambda, Pi))
    {i : ℕ} (h : i ≥ 1) :
    (Sigma.sigma Z 0).2 - (Sigma.sigma Z (i - 1)).2 ≥
      (Sigma.sigma Z 1).1 - (Sigma.sigma Z i).1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => simp
  | succ j ih =>
    induction j with
    | zero =>
      have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi hZ 0
      rw [if_pos (by decide : Even 0)] at h
      simpa using h
    | succ j _ =>
      by_cases hei : Even (j + 2)
      · have hei1 : ¬ (Even (j + 1)) := Nat.even_add_one.mp hei
        have hstep : (Sigma.sigma Z (j + 1)).2 - (Sigma.sigma Z (j + 2)).2 ≥
            (Sigma.sigma Z (j + 2)).1 - (Sigma.sigma Z (j + 3)).1 := by
          have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi hZ (j + 1)
          rw [if_neg hei1] at h; exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
          show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
          show j + 3 - 1 = j + 2 from by omega]
        linarith
      · have hei1 : Even (j + 1) := by rwa [Nat.even_add_one, not_not] at hei
        have hstep : (Sigma.sigma Z (j + 1)).2 - (Sigma.sigma Z (j + 2)).2 ≥
            (Sigma.sigma Z (j + 2)).1 - (Sigma.sigma Z (j + 3)).1 := by
          have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi hZ (j + 1)
          rw [if_pos hei1] at h; exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
          show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
          show j + 3 - 1 = j + 2 from by omega]
        linarith

/-- Second-component mirror of `np_mix_a1_ai_le_b0_bi_1`. -/
private lemma np_mix_b1_bi_le_a0_ai_1 {Z : Chromosome} (hZ : Z ∈ Mix (2 • Lambda, Pi))
    {i : ℕ} (h : i ≥ 1) :
    (Sigma.sigma Z 0).1 - (Sigma.sigma Z (i - 1)).1 ≥
      (Sigma.sigma Z 1).2 - (Sigma.sigma Z i).2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => simp
  | succ j ih =>
    induction j with
    | zero =>
      have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi hZ 0
      rw [if_pos (by decide : Even 0)] at h
      simpa using h
    | succ j _ =>
      by_cases hei : Even (j + 2)
      · have hei1 : ¬ (Even (j + 1)) := Nat.even_add_one.mp hei
        have hstep : (Sigma.sigma Z (j + 1)).1 - (Sigma.sigma Z (j + 2)).1 ≥
            (Sigma.sigma Z (j + 2)).2 - (Sigma.sigma Z (j + 3)).2 := by
          have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi hZ (j + 1)
          rw [if_neg hei1] at h; exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
          show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
          show j + 3 - 1 = j + 2 from by omega]
        linarith
      · have hei1 : Even (j + 1) := by rwa [Nat.even_add_one, not_not] at hei
        have hstep : (Sigma.sigma Z (j + 1)).1 - (Sigma.sigma Z (j + 2)).1 ≥
            (Sigma.sigma Z (j + 2)).2 - (Sigma.sigma Z (j + 3)).2 := by
          have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi hZ (j + 1)
          rw [if_pos hei1] at h; exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
          show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
          show j + 3 - 1 = j + 2 from by omega]
        linarith

/-- Removing one negative gene of rank `≤ i` (others positive) drops the negative
count of `prime^[i]` by one. -/
private lemma np_sg_neg_count_kill_one {W : Chromosome} {gneg : Gene} {i : ℕ}
    (hgneg_one : W gneg = 1) (hgneg_type : gneg.type = .Negative)
    (hgneg_rank : gneg.rank ≤ i)
    (hothers : ∀ h ∈ W.support, h.rank ≤ i → h ≠ gneg → h.type = .Positive) :
    (Chromosome.prime^[i] W).sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
      W.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) - 1 := by
  set W' : Chromosome := W - Finsupp.single gneg 1 with hW'_def
  have hgpos : 0 < W gneg := by omega
  have hWsplit : W = W' + Finsupp.single gneg 1 := (sub_single_add_single_eq hgpos).symm
  have hnegadd : W.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
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
    conv_lhs => rw [hWsplit]; rw [iterate_map_add, hkill, add_zero]
  have hW'pos : ∀ h ∈ W'.support, h.rank ≤ i → h.type = .Positive := by
    intro h hh hrank
    have hhne : h ≠ gneg := by
      intro he; subst he
      rw [hW'_def, Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_eq_same,
        hgneg_one] at hh
      simp at hh
    have hhW : h ∈ W.support := by
      rw [hW'_def, Finsupp.mem_support_iff, Finsupp.tsub_apply,
        Finsupp.single_apply, if_neg (fun he => hhne he.symm)] at hh
      exact Finsupp.mem_support_iff.mpr (by omega)
    exact hothers h hhW hrank hhne
  have hnegeq := Sigma.neg_count_eq (X := W') i hW'pos
  rw [hprime_eq, hnegeq, hnegadd]; ring

/-- Off-by-one telescoping (negative killed at level `i`), second-component drop. -/
private lemma np_sg_b0_bi_off_by_one {X : Chromosome} (hX : X ∈ Variety.Pi) {i : ℕ}
    {gneg : Gene} (hgneg_one : X gneg = 1) (hgneg_type : gneg.type = .Negative)
    (hgneg_rank : gneg.rank ≤ i)
    (hothers : ∀ h ∈ X.support, h.rank ≤ i → h ≠ gneg → h.type = .Positive) :
    (Sigma.sigma X 0).2 - (Sigma.sigma X i).2 =
      (Sigma.sigma X 1).1 - (Sigma.sigma X (i + 1)).1 + 1 := by
  have h0 := Sigma.bi_sum_ai1_eq_neg_count_1 X hX (i := 0)
  have hi := Sigma.bi_sum_ai1_eq_neg_count_1 X hX (i := i)
  have hkill := np_sg_neg_count_kill_one hgneg_one hgneg_type hgneg_rank hothers
  simp only [Sigma.sigma, Function.iterate_zero, id] at h0 hi ⊢
  rw [hkill] at hi
  linarith

/-- Negative-family mirror of `np_sg_b0_bi_off_by_one`. -/
private lemma np_sg_a0_ai_off_by_one {X : Chromosome} (hX : X ∈ Variety.Pi) {i : ℕ}
    {gpos : Gene} (hgpos_one : X gpos = 1) (hgpos_type : gpos.type = .Positive)
    (hgpos_rank : gpos.rank ≤ i)
    (hothers : ∀ h ∈ X.support, h.rank ≤ i → h ≠ gpos → h.type = .Negative) :
    (Sigma.sigma X 0).1 - (Sigma.sigma X i).1 =
      (Sigma.sigma X 1).2 - (Sigma.sigma X (i + 1)).2 + 1 := by
  have hnegX : (-X) ∈ Variety.Pi :=
    Variety.mem_Pi_iff.mpr
      (Chromosome.IsPolarized_iff_neg_polarized.mp (Variety.mem_Pi_iff.mp hX))
  have hkey := np_sg_b0_bi_off_by_one (X := -X) hnegX (i := i) (gneg := -gpos)
    (by rw [Chromosome.neg_apply, neg_neg]; exact hgpos_one)
    (by rw [Gene.neg_type, hgpos_type]; rfl)
    (by rw [Gene.neg_rank]; exact hgpos_rank)
    (by
      intro h hh hrank hne
      rw [Finsupp.mem_support_iff, Chromosome.neg_apply] at hh
      have hhX : (-h) ∈ X.support := Finsupp.mem_support_iff.mpr (by simpa using hh)
      have hhne : (-h) ≠ gpos := fun he => hne (by rw [← he, neg_neg])
      have hval := hothers (-h) hhX (by rwa [Gene.neg_rank]) hhne
      rw [Gene.neg_type] at hval
      cases hgt : h.type with
      | NonPolarized => rw [hgt] at hval; simp at hval
      | Positive => rfl
      | Negative => rw [hgt] at hval; simp at hval)
  rw [np_sigma_neg_swap, np_sigma_neg_swap, np_sigma_neg_swap, np_sigma_neg_swap] at hkey
  simpa [Prod.fst_swap, Prod.snd_swap] using hkey

/-- Second-component (negative doubled gene) mirror of `case3_value2_even_gap`.
If all genes of `X` of rank `≤ i-1` are Negative and `i` is even, then the
second signature component has a gap of at least `2`.  Proved by negating and
invoking `case3_value2_even_gap` on `-X, -Y`. -/
lemma case3_value2_even_gap_snd {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    {i : ℕ} (hi_even : Even i) (hi2 : 2 ≤ i)
    (hneg : ∀ g ∈ X.1.1.support, g.rank ≤ i - 1 → g.type = .Negative)
    (hY1 : Chromosome.prime^[1] Y.1.1 ≠ 0)
    (hYi1 : Chromosome.prime^[i - 1] Y.1.1 ≠ 0) :
    (Sigma.sigma X.1.1 i).2 + 2 ≤ (Sigma.sigma Y.1.1 i).2 := by
  have hXYc : X.1.1 < Y.1.1 := hXY
  have hXYnn : (-(X.1.1)) < (-(Y.1.1)) := Chromosome.neg_lt_neg_iff.mpr hXYc
  have hXYneg : (npNeg X).1 < (npNeg Y).1 := hXYnn
  have hXnegPi : (npNeg X).1.1 ∈ Variety.Pi := by
    rw [npNeg_val]
    exact Variety.mem_Pi_iff.mpr
      (Chromosome.IsPolarized_iff_neg_polarized.mp (Variety.mem_Pi_iff.mp hXPi))
  have h17neg : ∀ k, 0 < k → Chromosome.prime^[k] (npNeg Y).1.1 ≠ 0 →
      (Chromosome.prime^[k] (npNeg X).1.1).rank <
        (Chromosome.prime^[k] (npNeg Y).1.1).rank := by
    intro k hk hne
    simp only [npNeg_val, ← Chromosome.prime_iterate_neg, Chromosome.rank_neg]
    apply h17_1 k hk
    simp only [npNeg_val, ← Chromosome.prime_iterate_neg] at hne
    intro hz; exact hne (by rw [hz, neg_zero])
  have hnegpos : ∀ g ∈ (npNeg X).1.1.support, g.rank ≤ i - 1 → g.type = .Positive := by
    intro g hg hrank
    rw [npNeg_val, Finsupp.mem_support_iff, Chromosome.neg_apply] at hg
    have hgX : (-g) ∈ X.1.1.support := Finsupp.mem_support_iff.mpr hg
    have hneg' := hneg (-g) hgX (by rwa [Gene.neg_rank])
    have : -(g.type) = GeneType.Negative := by rw [← Gene.neg_type]; exact hneg'
    cases hgt : g.type <;> simp_all
  have hY1neg : Chromosome.prime^[1] (npNeg Y).1.1 ≠ 0 := by
    rw [npNeg_val, ← Chromosome.prime_iterate_neg]
    intro hz; exact hY1 (by simpa using congrArg Neg.neg hz)
  have hYi1neg : Chromosome.prime^[i - 1] (npNeg Y).1.1 ≠ 0 := by
    rw [npNeg_val, ← Chromosome.prime_iterate_neg]
    intro hz; exact hYi1 (by simpa using congrArg Neg.neg hz)
  have h := case3_value2_even_gap (npNeg X) (npNeg Y) hXYneg hXnegPi h17neg
    hi_even hi2 hnegpos hY1neg hYi1neg
  rw [npNeg_val, npNeg_val, np_sigma_neg_swap, np_sigma_neg_swap,
    Prod.fst_swap, Prod.fst_swap] at h
  exact h

/-- Packaged even gap for the type16/type14 assembly (arbitrary polarized doubled
gene `gᵉ(1)`): `2·sig(gᵉ(1)) + σX(i) ≤ σY(i)` at even `i`, where all genes of `X`
of rank `≤ i-1` share the sign `ε`. -/
lemma case3_gap_even {N : ℕ} {ε : GeneType} (hε : ε ≠ GeneType.NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    {i : ℕ} (hi_even : Even i) (hi2 : 2 ≤ i)
    (hbelow : ∀ g ∈ X.1.1.support, g.rank ≤ i - 1 → g.type = ε)
    (hY1 : Chromosome.prime^[1] Y.1.1 ≠ 0)
    (hYi1 : Chromosome.prime^[i - 1] Y.1.1 ≠ 0) :
    signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε) +
        signature (Chromosome.prime^[i] X.1.1) ≤
      signature (Chromosome.prime^[i] Y.1.1) := by
  cases hεc : ε with
  | NonPolarized => exact absurd hεc hε
  | Positive =>
      subst hεc
      have hfst : (signature (Chromosome.prime^[i] X.1.1)).1 + 2 ≤
          (signature (Chromosome.prime^[i] Y.1.1)).1 :=
        case3_value2_even_gap X Y hXY hXPi h17_1 hi_even hi2 hbelow hY1 hYi1
      have hsnd : (signature (Chromosome.prime^[i] X.1.1)).2 ≤
          (signature (Chromosome.prime^[i] Y.1.1)).2 := (le_iff_dominates.mp hXY.le i).2
      rw [Prod.le_def]
      refine ⟨?_, ?_⟩ <;> simp only [signature_ofRank_one_positive, Prod.fst_add, Prod.snd_add]
      · linarith
      · linarith
  | Negative =>
      subst hεc
      have hsnd : (signature (Chromosome.prime^[i] X.1.1)).2 + 2 ≤
          (signature (Chromosome.prime^[i] Y.1.1)).2 :=
        case3_value2_even_gap_snd X Y hXY hXPi h17_1 hi_even hi2 hbelow hY1 hYi1
      have hfst : (signature (Chromosome.prime^[i] X.1.1)).1 ≤
          (signature (Chromosome.prime^[i] Y.1.1)).1 := (le_iff_dominates.mp hXY.le i).1
      rw [Prod.le_def]
      refine ⟨?_, ?_⟩ <;> simp only [signature_ofRank_one_negative, Prod.fst_add, Prod.snd_add]
      · linarith
      · linarith

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

/-- §17 Case 3 successor gap for a single opposite-sign gene of multiplicity one.
Given the doubled polarized `gᵉ(1)`, a single opposite-sign `g⁻ᵉ(2Q+3)`, and that
below rank `2Q+3` every gene other than `gopp` has sign `ε`, the off-by-one
telescoping produces the `type16` successor gap at level `2Q+4`. -/
lemma np_succ_gap_of_one {N Q : ℕ} {ε : GeneType} (hε : ε ≠ GeneType.NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    (gopp : Gene)
    (hgopp_rank : gopp.rank = 2 * Q + 3) (hgopp_type : gopp.type = -ε)
    (hone : X.1.1 gopp = 1)
    (hlow : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * Q + 3 → h ≠ gopp → h.type = ε)
    (hYne : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    signature (Gene.ofRank 1 ε) +
        signature (Chromosome.prime^[2 * Q + 4] X.1.1) ≤
      signature (Chromosome.prime^[2 * Q + 4] Y.1.1) := by
  have hsucc_rank : 2 * Q + 4 = (2 * Q + 3) + 1 := by omega
  -- level-0 agreement
  have h0 := sigma_zero_eq X Y hXY
  have hb0d0 : (Sigma.sigma X.1.1 0).2 = (Sigma.sigma Y.1.1 0).2 := congrArg Prod.snd h0
  have ha0c0 : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 := congrArg Prod.fst h0
  -- level-1 gap
  have hgap1 : ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[1] X.1.1) ≤
      signature (Chromosome.prime^[1] Y.1.1) :=
    type10_mid_gap_odd_of_Y_ne X Y h17_1 (by decide) (by omega) (hYne 1 (by omega) (by omega))
  -- level 2Q+3 gap
  have hodd_gap : ((1 : ℚ), (1 : ℚ)) +
      signature (Chromosome.prime^[2 * Q + 3] X.1.1) ≤
      signature (Chromosome.prime^[2 * Q + 3] Y.1.1) :=
    type10_mid_gap_odd_of_Y_ne X Y h17_1
      (Nat.not_even_iff_odd.mpr ⟨Q + 1, by ring⟩) (by omega) (hYne (2 * Q + 3) (by omega) le_rfl)
  cases hgt : ε with
  | NonPolarized => exact absurd hgt hε
  | Positive =>
      subst hgt
      have hgopp_neg : gopp.type = GeneType.Negative := by rw [hgopp_type]; rfl
      have hlow_pos : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * Q + 3 →
          h ≠ gopp → h.type = GeneType.Positive := hlow
      have hX1 := np_sg_b0_bi_off_by_one hXPi (i := 2 * Q + 3) hone hgopp_neg
        (by rw [hgopp_rank]) hlow_pos
      have hY1 := np_mix_a1_ai_le_b0_bi_1 Y.1.2 (i := 2 * Q + 4) (by omega)
      have hodd_snd := snd_add_one_le_of_one_one_add_le hodd_gap
      have hc1a1 := fst_add_one_le_of_one_one_add_le hgap1
      rw [← hsucc_rank] at hX1
      simp only [Sigma.sigma, show 2 * Q + 4 - 1 = 2 * Q + 3 by omega]
        at hX1 hY1 hodd_snd hc1a1
      have hstrict : (signature (Chromosome.prime^[2 * Q + 4] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * Q + 4] Y.1.1)).1 := by
        simp only [Sigma.sigma] at hb0d0 ha0c0 ⊢
        linarith
      simpa [show 2 * (Q + 1) + 2 = 2 * Q + 4 by omega] using
        type16_succ_gap_positive X Y hXY (p := Q + 1)
          (by simpa [show 2 * (Q + 1) + 2 = 2 * Q + 4 by omega] using hstrict)
  | Negative =>
      subst hgt
      have hgopp_pos : gopp.type = GeneType.Positive := by rw [hgopp_type]; rfl
      have hlow_neg : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * Q + 3 →
          h ≠ gopp → h.type = GeneType.Negative := hlow
      have hX1 := np_sg_a0_ai_off_by_one hXPi (i := 2 * Q + 3) hone hgopp_pos
        (by rw [hgopp_rank]) hlow_neg
      have hY1 := np_mix_b1_bi_le_a0_ai_1 Y.1.2 (i := 2 * Q + 4) (by omega)
      have hodd_fst := fst_add_one_le_of_one_one_add_le hodd_gap
      have hc1a1 := snd_add_one_le_of_one_one_add_le hgap1
      rw [← hsucc_rank] at hX1
      simp only [Sigma.sigma, show 2 * Q + 4 - 1 = 2 * Q + 3 by omega]
        at hX1 hY1 hodd_fst hc1a1
      have hstrict : (signature (Chromosome.prime^[2 * Q + 4] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * Q + 4] Y.1.1)).2 := by
        simp only [Sigma.sigma] at hb0d0 ha0c0 ⊢
        linarith
      simpa [show 2 * (Q + 1) + 2 = 2 * Q + 4 by omega] using
        type16_succ_gap_negative X Y hXY (p := Q + 1)
          (by simpa [show 2 * (Q + 1) + 2 = 2 * Q + 4 by omega] using hstrict)

/-- §17 Case 3 type14 branch: doubled polarized rank-one gene `gᵉ(1)` plus a
doubled minimal opposite-sign gene `g⁻ᵉ(2Q+3)` give a reducing step (no succ gap
needed). -/
lemma exists_step_type14_neg_partner {N Q : ℕ} {ε : GeneType}
    (hε : ε ≠ GeneType.NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    (g gneg : Gene)
    (hg_rank : g.rank = 1) (hg_type : g.type = ε)
    (hgneg_rank : gneg.rank = 2 * Q + 3) (hgneg_type : gneg.type = -ε)
    (hg_two : 2 ≤ X.1.1 g) (hgneg_two : 2 ≤ X.1.1 gneg)
    (hpos_below : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * Q + 2 → h.type = ε)
    (hYne : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : g ≠ gneg := by
    intro h; rw [h, hgneg_type] at hg_type
    exact (by cases ε <;> simp_all : ¬ (-ε = ε)) hg_type
  have hgap_odd : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := fun j hjlo hjhi hjodd =>
    type10_mid_gap_odd_of_Y_ne X Y h17_1 hjodd (by omega) (hYne j hjlo hjhi)
  have hgap_even : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Even j →
      (signature (Gene.ofRank 1 ε) +
          signature (Gene.ofRank 1 ε)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hjeven
    have hjge2 : 2 ≤ j := by obtain ⟨t, ht⟩ := hjeven; omega
    exact case3_gap_even hε X Y hXY hXPi h17_1 hjeven (by omega)
      (fun h hh hr => hpos_below h hh (by omega)) (hYne 1 (by omega) (by omega))
      (hYne (j - 1) (by omega) (by omega))
  have hg_rank' : g.rank = 2 * 0 + 1 := by omega
  have hgneg_rank' : gneg.rank = 2 * (Q + 1) + 1 := by omega
  have hg_eq : Gene.ofRank (2 * 0 + 1) ε = (Finsupp.single g 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g); rwa [hg_rank', hg_type] at h
  have hgneg_eq : Gene.ofRank (2 * (Q + 1) + 1) (-ε) =
      (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg); rwa [hgneg_rank', hgneg_type] at h
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
    hg_type hgneg_type hg_rank' hgneg_rank' hg_two hgneg_two hne hZle

/-- §17 Case 3 type16 branch: doubled polarized rank-one gene `gᵉ(1)` plus a
single minimal opposite-sign gene `g⁻ᵉ(2Q+3)`, given the successor gap. -/
lemma exists_step_type16_neg_partner {N Q : ℕ} {ε : GeneType}
    (hε : ε ≠ GeneType.NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hXPi : X.1.1 ∈ Variety.Pi)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    (g gneg : Gene)
    (hg_rank : g.rank = 1) (hg_type : g.type = ε)
    (hgneg_rank : gneg.rank = 2 * Q + 3) (hgneg_type : gneg.type = -ε)
    (hg_two : 2 ≤ X.1.1 g) (hgneg_one : 1 ≤ X.1.1 gneg)
    (hpos_below : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * Q + 2 → h.type = ε)
    (hYne : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0)
    (hgap_succ : signature (Gene.ofRank 1 ε) +
        signature (Chromosome.prime^[2 * Q + 4] X.1.1) ≤
      signature (Chromosome.prime^[2 * Q + 4] Y.1.1)) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : g ≠ gneg := by
    intro h; rw [h, hgneg_type] at hg_type
    exact (by cases ε <;> simp_all : ¬ (-ε = ε)) hg_type
  have hgap_odd : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := fun j hjlo hjhi hjodd =>
    type10_mid_gap_odd_of_Y_ne X Y h17_1 hjodd (by omega) (hYne j hjlo hjhi)
  have hgap_even : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Even j →
      (signature (Gene.ofRank 1 ε) +
          signature (Gene.ofRank 1 ε)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi hjeven
    have hjge2 : 2 ≤ j := by obtain ⟨t, ht⟩ := hjeven; omega
    exact case3_gap_even hε X Y hXY hXPi h17_1 hjeven (by omega)
      (fun h hh hr => hpos_below h hh (by omega)) (hYne 1 (by omega) (by omega))
      (hYne (j - 1) (by omega) (by omega))
  have hg_rank' : g.rank = 2 * 0 + 1 := by omega
  have hgneg_rank' : gneg.rank = 2 * (Q + 1) + 1 := by omega
  have hg_eq : Gene.ofRank (2 * 0 + 1) ε = (Finsupp.single g 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g); rwa [hg_rank', hg_type] at h
  have hgneg_eq : Gene.ofRank (2 * (Q + 1) + 1) (-ε) =
      (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg); rwa [hgneg_rank', hgneg_type] at h
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
    hg_type hgneg_type hg_rank' hgneg_rank' hg_two hgneg_one hne hZle

/-- §17 Case 3 negative-partner dispatch (sign-generic).  Given the rank-one
doubled polarized gene `gᵉ(1)` and *some* opposite-sign gene of `X`, extract the
minimal opposite-sign gene `g⁻ᵉ(2Q+3)`, verify its rank (odd, ≥3 by `hno_pair`),
and dispatch on its multiplicity into the Type14 (doubled) or Type16 (single, via
the successor gap) boundary.  This is the shared engine for both the same-sign
frontier (`SameSign.lean:124`) and the same-gene opposite-mass frontier
(`SameGene.lean`). -/
lemma exists_step_neg_partner_dispatch {m : ℕ} {ε : GeneType}
    (hε : ε ≠ GeneType.NonPolarized)
    (X Y : nMix2LambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ∀ h : Gene, 0 < X.1.1 h → Y.1.1 h ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank < (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hg_rank_one : g.rank = 1) (hg_type : g.type = ε)
    (hg_two : 2 ≤ X.1.1 g)
    (_ : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  classical
  have hXPi : X.1.1 ∈ Variety.Pi := Variety.mem_Pi_iff.mpr hXpol
  -- `-ε ≠ ε` for polarized `ε`.
  have hneg_ne : (-ε) ≠ ε := by cases ε <;> simp_all
  have hnegε_pol : (-ε) ≠ GeneType.NonPolarized := by cases ε <;> simp_all
  -- Level-1 symmetry (Label 3, odd level) and level-0 agreement.
  have ha1b1 : (signature (Chromosome.prime^[1] X.1.1)).1
             = (signature (Chromosome.prime^[1] X.1.1)).2 :=
    Mix2LambdaSection17.signature_prime_iterate_odd_eq_components_L3 X.1.2 (by decide)
  have h0 := sigma_zero_eq X Y hXY
  have ha0c0 : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 := congrArg Prod.fst h0
  have hb0d0 : (Sigma.sigma X.1.1 0).2 = (Sigma.sigma Y.1.1 0).2 := congrArg Prod.snd h0
  -- An opposite-sign (`-ε`) gene of `X` always exists: assuming otherwise chains
  -- the level-1 symmetry, level-0 agreement, and monotonicity into a strict
  -- self-inequality contradicting `hseed1`.
  have hwitness : ∃ gw : Gene, gw.type = -ε ∧ 0 < X.1.1 gw := by
    cases hgt : ε with
    | NonPolarized => exact absurd hgt hε
    | Positive =>
        -- need a Negative gene; negative mass `a1 < b0`.
        have hmass : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma X.1.1 0).2 := by
          by_contra hle
          push Not at hle
          have hD1D0 : (signature (Chromosome.prime^[1] Y.1.1)).2 ≤
              (signature Y.1.1).2 := ((signature_prime_le Y.1.1).trans inf_le_left).2
          simp only [Sigma.sigma] at hle hb0d0 ⊢
          have hs2 := hseed1.2
          -- b1 = a1 ≥ b0 = d0 ≥ d1 > b1
          have hb0X : (signature (Chromosome.prime^[0] X.1.1)).2 =
              (signature X.1.1).2 := by simp
          have hb0Y : (signature (Chromosome.prime^[0] Y.1.1)).2 =
              (signature Y.1.1).2 := by simp
          rw [hb0X, hb0Y] at hb0d0
          linarith [ha1b1]
        obtain ⟨gw, hgw_type, hgw_pos⟩ := Sigma.neg_gene_of_b0_gt_a1 X.1.1 hXPi hmass
        refine ⟨gw, ?_, hgw_pos⟩
        rw [hgw_type]; rfl
    | Negative =>
        -- need a Positive gene; positive mass `b1 < a0`, via the `-X` dual.
        have hnegXPi : (-X.1.1) ∈ Variety.Pi :=
          Variety.mem_Pi_iff.mpr
            (Chromosome.IsPolarized_iff_neg_polarized.mp (Variety.mem_Pi_iff.mp hXPi))
        have hmass : (Sigma.sigma (-X.1.1) 1).1 < (Sigma.sigma (-X.1.1) 0).2 := by
          rw [np_sigma_neg_swap, np_sigma_neg_swap, Prod.fst_swap, Prod.snd_swap]
          -- goal: (sigma X 1).2 < (sigma X 0).1  (positive mass)
          by_contra hle
          push Not at hle
          have hC1C0 : (signature (Chromosome.prime^[1] Y.1.1)).1 ≤
              (signature Y.1.1).1 := ((signature_prime_le Y.1.1).trans inf_le_left).1
          simp only [Sigma.sigma] at hle ha0c0 ⊢
          have hs1 := hseed1.1
          have ha0X : (signature (Chromosome.prime^[0] X.1.1)).1 =
              (signature X.1.1).1 := by simp
          have ha0Y : (signature (Chromosome.prime^[0] Y.1.1)).1 =
              (signature Y.1.1).1 := by simp
          rw [ha0X, ha0Y] at ha0c0
          linarith [ha1b1]
        obtain ⟨gw, hgw_type, hgw_pos⟩ := Sigma.neg_gene_of_b0_gt_a1 (-X.1.1) hnegXPi hmass
        rw [Chromosome.neg_apply] at hgw_pos
        refine ⟨-gw, ?_, hgw_pos⟩
        rw [Gene.neg_type, hgw_type]
  obtain ⟨gw, hgw_type, hgw_pos⟩ := hwitness
  -- Minimal opposite-sign (`-ε`) gene of `X`.
  set S : Finset Gene := X.1.1.support.filter (fun h => h.type = -ε) with hS_def
  have hSne : S.Nonempty :=
    ⟨gw, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (ne_of_gt hgw_pos), hgw_type⟩⟩
  obtain ⟨gopp, hgopp_S, hgopp_min⟩ := Finset.exists_min_image S Gene.rank hSne
  rw [hS_def, Finset.mem_filter] at hgopp_S
  have hgopp_pos : 0 < X.1.1 gopp :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hgopp_S.1)
  have hgopp_type : gopp.type = -ε := hgopp_S.2
  -- Minimality among opposite-sign genes.
  have hgopp_min' : ∀ h : Gene, 0 < X.1.1 h → h.type = -ε → gopp.rank ≤ h.rank := by
    intro h hh htype
    exact hgopp_min h (Finset.mem_filter.mpr
      ⟨Finsupp.mem_support_iff.mpr (ne_of_gt hh), htype⟩)
  -- `gopp` is polarized with odd rank.
  have hgopp_pol : gopp.type ≠ GeneType.NonPolarized := by rw [hgopp_type]; exact hnegε_pol
  have hgopp_odd : Odd gopp.rank :=
    Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi X.1.2 hgopp_pos hgopp_pol
  -- `gopp.rank ≥ 3`: rank 1 would give a rank-one opposite-sign pair with `g`.
  have hgopp_rank_ge : 3 ≤ gopp.rank := by
    rcases hgopp_odd with ⟨t, ht⟩
    by_contra hlt
    have ht0 : t = 0 := by omega
    have hgopp_rank1 : gopp.rank = 1 := by omega
    -- `g` (rank 1, type ε) and `gopp` (rank 1, type -ε) form a forbidden pair.
    cases hgt : ε with
    | NonPolarized => exact hε hgt
    | Positive =>
        exact hno_pair ⟨g, gopp, by rw [hg_rank_one, hgopp_rank1],
          by rw [hg_type, hgt], by rw [hgopp_type, hgt]; rfl, (by omega : 0 < X.1.1 g), hgopp_pos⟩
    | Negative =>
        exact hno_pair ⟨gopp, g, by rw [hgopp_rank1, hg_rank_one],
          by rw [hgopp_type, hgt]; rfl, by rw [hg_type, hgt], hgopp_pos, (by omega : 0 < X.1.1 g)⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, gopp.rank = 2 * Q + 3 := by
    rcases hgopp_odd with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
  -- Below `gopp.rank`, every gene of `X` other than `gopp` has sign `ε`.
  have hlow : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * Q + 3 → h ≠ gopp → h.type = ε := by
    intro h hh hrank hne
    have hhpos : 0 < X.1.1 h := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have hhpol : h.type ≠ GeneType.NonPolarized := IsPolarized_def'.mp hXpol h hh
    by_cases hhne : h.type = -ε
    · -- another opposite-sign gene: minimality forces `h.rank = gopp.rank`, hence `h = gopp`.
      exfalso
      have hge := hgopp_min' h hhpos hhne
      have hheq : h.rank = 2 * Q + 3 := by rw [hQ] at hge; omega
      exact hne (Gene.ext (by rw [hheq, hQ]) (by rw [hhne, hgopp_type]))
    · exact polarized_same_type_of_not_neg hε hhpol (by
        intro hcontra; exact hhne (by rw [hcontra]))
  have hpos_below : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * Q + 2 → h.type = ε := by
    intro h hh hrank
    refine hlow h hh (by omega) ?_
    intro he; subst he; rw [hQ] at hrank; omega
  -- `Y` does not vanish at any level `1 ≤ j ≤ 2Q+3`.
  have hYne : ∀ j, 1 ≤ j → j ≤ 2 * Q + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0 := by
    intro j hjlo hjhi hYzero
    -- If `prime^[j] Y = 0`, then all genes of `Y` have rank `< j ≤ 2Q+3`, but
    -- `X` has an opposite-sign gene of rank `2Q+3` forcing `Y`'s rank up.
    have hYzero3 : Chromosome.prime^[2 * Q + 3] Y.1.1 = 0 := by
      have hjle : j ≤ 2 * Q + 3 := hjhi
      have := (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := j)).2 hYzero
      rw [← Chromosome.prime_iterate_eq_zero_rank_le]
      intro h hh; exact le_trans (this h hh) hjle
    -- top-level `Y` genes have rank ≤ 2Q+3.
    have hYrank : ∀ h : Gene, 0 < Y.1.1 h → h.rank ≤ 2 * Q + 3 := by
      intro h hh
      exact (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := 2 * Q + 3)).2 hYzero3
        h (Finsupp.mem_support_iff.mpr (ne_of_gt hh))
    have hYpol_top : ∀ h : Gene, 0 < Y.1.1 h → h.rank = 2 * Q + 3 →
        h.type ≠ GeneType.NonPolarized := by
      intro h hh hhrank
      have hhodd : Odd h.rank := by rw [hhrank]; exact ⟨Q + 1, by ring⟩
      have hodd_part : 0 < Y.1.1.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]; exact hh
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
        (Finsupp.mem_support_iff.mpr hodd_part.ne')
    cases hgt : ε with
    | NonPolarized => exact hε hgt
    | Positive =>
        -- `gopp` is Negative; `Y` has no Negative gene at rank `2Q+3` (hcommon).
        have hgopp_neg : gopp.type = GeneType.Negative := by rw [hgopp_type, hgt]; rfl
        have hno_neg : Y.1.1 ⟨2 * Q + 3, GeneType.Negative, by omega⟩ = 0 := by
          have htop_eq : (⟨2 * Q + 3, GeneType.Negative, by omega⟩ : Gene) = gopp :=
            Gene.ext (by dsimp; rw [hQ]) hgopp_neg.symm
          have hle := hcommon gopp hgopp_pos
          rw [htop_eq]; omega
        have hYsnd0 := signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
          (W := Y.1.1) (p := Q + 1) hYpol_top hYrank hno_neg
        have hYsnd0' : (signature (Chromosome.prime^[2 * Q + 2] Y.1.1)).2 = 0 := by
          simpa [show 2 * (Q + 1) = 2 * Q + 2 by omega] using hYsnd0
        have hXsnd1 := one_le_signature_prime_pred_snd_of_negative (X := X.1.1)
          (gneg := gopp) hgopp_neg hgopp_pos
        have hXsnd1' : 1 ≤ (signature (Chromosome.prime^[2 * Q + 2] X.1.1)).2 := by
          simpa [hQ, show 2 * Q + 3 - 1 = 2 * Q + 2 by omega] using hXsnd1
        have hdom := (le_iff_dominates.mp hXY.le (2 * Q + 2)).2
        linarith
    | Negative =>
        have hgopp_posT : gopp.type = GeneType.Positive := by rw [hgopp_type, hgt]; rfl
        have hno_pos : Y.1.1 ⟨2 * Q + 3, GeneType.Positive, by omega⟩ = 0 := by
          have htop_eq : (⟨2 * Q + 3, GeneType.Positive, by omega⟩ : Gene) = gopp :=
            Gene.ext (by dsimp; rw [hQ]) hgopp_posT.symm
          have hle := hcommon gopp hgopp_pos
          rw [htop_eq]; omega
        have hYfst0 := signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
          (W := Y.1.1) (p := Q + 1) hYpol_top hYrank hno_pos
        have hYfst0' : (signature (Chromosome.prime^[2 * Q + 2] Y.1.1)).1 = 0 := by
          simpa [show 2 * (Q + 1) = 2 * Q + 2 by omega] using hYfst0
        have hXfst1 := one_le_signature_prime_pred_fst_of_positive (X := X.1.1)
          (gpos := gopp) hgopp_posT hgopp_pos
        have hXfst1' : 1 ≤ (signature (Chromosome.prime^[2 * Q + 2] X.1.1)).1 := by
          simpa [hQ, show 2 * Q + 3 - 1 = 2 * Q + 2 by omega] using hXfst1
        have hdom := (le_iff_dominates.mp hXY.le (2 * Q + 2)).1
        linarith
  -- Dispatch on the multiplicity of `gopp`.
  have hgopp_rank_q : gopp.rank = 2 * Q + 3 := hQ
  by_cases htwo : 2 ≤ X.1.1 gopp
  · exact exists_step_type14_neg_partner hε X Y hXY hXPi h17_1 g gopp
      hg_rank_one hg_type hgopp_rank_q hgopp_type hg_two htwo hpos_below hYne
  · have hone : X.1.1 gopp = 1 := by omega
    have hsucc := np_succ_gap_of_one hε X Y hXY hXPi h17_1 gopp hgopp_rank_q hgopp_type
      hone hlow hYne
    exact exists_step_type16_neg_partner hε X Y hXY hXPi h17_1 g gopp
      hg_rank_one hg_type hgopp_rank_q hgopp_type hg_two (by omega) hpos_below hYne hsucc

end Mix2LambdaPi
