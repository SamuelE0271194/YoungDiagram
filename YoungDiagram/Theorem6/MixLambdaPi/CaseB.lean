import YoungDiagram.Theorem6.MixLambdaPi.CaseA
import YoungDiagram.Theorem6.MixLambdaPi.CaseBProp
import YoungDiagram.Theorem6.MixLambdaPi.CaseB3

/-!
# §16 Case A core, Branch B for `Mix (Lambda, Pi)` (label 1).

Branch B of §16 Case A: the minimal-rank gene `g₁` of `X` is **polarized**
(WLOG `g₁ = g⁺(m)`, so `m` is odd in `Mix (Lambda, Pi)`).  Following §16 (Djoković)
we split on `m`:

* **Case 5** (`m = 1`): paper Case 5, primitives type6/type7 with bottom index `0`.
* **Case 3** (`m ≥ 3`): paper Case 3, primitives type6/type7/type8.
* (`m = 2` of §16 is vacuous here since polarized genes have odd rank.)

The `g₁ = g⁻(m)` charge is handled by sign-duality (`branchB_neg`).  This file also
hosts the final §16 Case A dispatcher `exists_mutation_le_caseA`, split off from
`CaseA.lean` to keep file sizes manageable.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixLambdaPi

/-- **a-propagation core** for §16 Branch B Case 5.  From `a_1 < c_1` (= `ha`) propagates
`a_X(j) + 1 ≤ a_Y(j)` to every even level `j ∈ [2, 2n'+2]`.  Works *below* the only
nonpolarized gene: `g₁ = g⁺(1)` vanishes for `j ≥ 1` (so `σ X = σ X'` with `X' = X - g₁`
having all genes `≥ 2n'+2`), and `g₁` contributes `+1` to `a_X(0)`, making
`a_X(0)-a_X(2) = #genes(X) = r_0-r_1`.  Monotone accumulation via `KEY_Y` + `twostep X'`. -/
lemma branchB_case5_aprop {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (n' : ℕ) (g₁ : Gene) (hg₁rank : g₁.rank = 1) (hg₁pos : g₁.type = .Positive)
    (hg₁mult : X.1.1 g₁ = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * n' + 2 ≤ g.rank) :
    ∀ j, 2 ≤ j → j ≤ 2 * n' + 2 → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 := by
  set X' : Chromosome := X.1.1 - Finsupp.single g₁ 1 with hX'def
  have hXadd : X.1.1 = X' + Finsupp.single g₁ 1 := by
    rw [hX'def]; ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : g₁ = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  have hshift : ∀ j, 1 ≤ j → Sigma.sigma X.1.1 j = Sigma.sigma X' j := by
    intro j hj
    have hprime0 : Chromosome.prime^[j] (Finsupp.single g₁ 1) = 0 := by
      rw [← prime_iterate_eq_zero_rank_le]
      intro g hg
      rw [Finsupp.support_single _ (by norm_num), Finset.mem_singleton] at hg
      subst hg; omega
    rw [hXadd, Sigma.sigma_linearity]
    simp only [Sigma.sigma, hprime0, map_zero, add_zero]
  -- #genes(X) = #genes(X') + 1
  have hgenes : X.1.1.sum (fun _ m => (m : ℚ)) = X'.sum (fun _ m => (m : ℚ)) + 1 := by
    conv_lhs => rw [hXadd]
    rw [Finsupp.sum_add_index (by simp) (by intros; push_cast; ring),
      Finsupp.sum_single_index (by simp)]
    push_cast; ring
  -- r_X(0) - r_X(1) = #genes(X)
  have hcellsX : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
      ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) = X.1.1.sum (fun _ m => (m : ℚ)) := by
    have hr0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
    have hr1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have hc : (X.1.1.rank : ℚ) - ((Chromosome.prime^[1] X.1.1).rank : ℚ) =
        X.1.1.sum (fun _ m => (m : ℚ)) := by rw [Function.iterate_one]; exact cells
    rw [hr0, hr1]; exact hc
  -- a_X 2-step drop = #genes(X') on the window (via shift to X' + twostep)
  have hXdrop : ∀ i, 1 ≤ i → i + 2 ≤ 2 * n' + 2 →
      (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 = X'.sum (fun _ m => (m : ℚ)) := by
    intro i hi1 hi2
    rw [hshift i hi1, hshift (i + 2) (by omega)]
    exact twostep (W := X') (i := i) (fun g hg => le_trans (by omega) (h2nd g hg))
  -- bottom: a_X(2) + 1 ≤ a_Y(2)
  have hbottom : (Sigma.sigma X.1.1 2).1 + 1 ≤ (Sigma.sigma Y.1.1 2).1 := by
    have hcond := cond_15_7_Mix_Lambda_Pi Y.1.2 0
    rw [if_pos (by decide : Even 0)] at hcond
    have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
    have hXrank : (X.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast X.2
    have hYrank : (Y.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast Y.2
    have hb1 : (Sigma.sigma X.1.1 1).2 ≤ (Sigma.sigma Y.1.1 1).2 :=
      (le_iff_dominates.mp hXY.le 1).2
    have ha0 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 :=
      (le_iff_dominates.mp hXY.le 0).1
    -- a_X(0) = a_{X'}(0) + 1
    have haX0 : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma X' 0).1 + 1 := by
      have hsig : Sigma.sigma X.1.1 0 = Sigma.sigma X' 0 + Sigma.sigma (Finsupp.single g₁ 1) 0 := by
        conv_lhs => rw [hXadd]; rw [Sigma.sigma_linearity]
      have hg₁sig : (Sigma.sigma (Finsupp.single g₁ 1 : Chromosome) 0).1 = 1 := by
        have h := Gene.ofRank_eq_gene (g := g₁); rw [hg₁rank, hg₁pos] at h
        simp only [Sigma.sigma, Function.iterate_zero, id_eq, ← h, signature_ofRank_one_positive]
      rw [hsig, Prod.fst_add, hg₁sig]
    have hX2 : (Sigma.sigma X.1.1 2).1 = (Sigma.sigma X' 2).1 :=
      congrArg Prod.fst (hshift 2 (by omega))
    have hX'02 : (Sigma.sigma X' 0).1 - (Sigma.sigma X' 2).1 = X'.sum (fun _ m => (m : ℚ)) :=
      twostep (W := X') (i := 0) (fun g hg => le_trans (by omega) (h2nd g hg))
    have hX02 : (Sigma.sigma X.1.1 0).1 - (Sigma.sigma X.1.1 2).1 =
        X'.sum (fun _ m => (m : ℚ)) + 1 := by rw [haX0, hX2]; linarith
    have hsX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
    obtain ⟨zX, hzX⟩ := sig_fst_isInt_even X.1.2 (by decide : Even 2)
    obtain ⟨zY, hzY⟩ := sig_fst_isInt_even Y.1.2 (by decide : Even 2)
    have hlt : (Sigma.sigma X.1.1 2).1 < (Sigma.sigma Y.1.1 2).1 := by
      linarith [hcond, hsY0, hsX0, hcellsX, hgenes, hX02, ha0, hb1, ha, hXrank, hYrank]
    rw [hzX, hzY] at hlt ⊢
    have hz : zX < zY := by exact_mod_cast hlt
    have hz1 : (zX : ℚ) + 1 ≤ (zY : ℚ) := by exact_mod_cast hz
    linarith
  -- monotone accumulation of f = a_Y - a_X over even 2-steps
  have hstep : ∀ i, 2 ≤ i → i + 2 ≤ 2 * n' + 2 → Even i →
      (Sigma.sigma Y.1.1 i).1 - (Sigma.sigma X.1.1 i).1 ≤
        (Sigma.sigma Y.1.1 (i + 2)).1 - (Sigma.sigma X.1.1 (i + 2)).1 := by
    intro i hi1 hi2 hei
    have hY := KEY_Y X Y hXY ha hei
    have hX := hXdrop i (by omega) hi2
    rw [hcellsX, hgenes] at hY
    linarith
  have hmono : ∀ t, 2 + 2 * t ≤ 2 * n' + 2 →
      (Sigma.sigma Y.1.1 2).1 - (Sigma.sigma X.1.1 2).1 ≤
        (Sigma.sigma Y.1.1 (2 + 2 * t)).1 - (Sigma.sigma X.1.1 (2 + 2 * t)).1 := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ k ih =>
      intro hr
      have heven : Even (2 + 2 * k) := ⟨1 + k, by ring⟩
      have hs := hstep (2 + 2 * k) (by omega) (by omega) heven
      have he : 2 + 2 * k + 2 = 2 + 2 * (k + 1) := by ring
      rw [he] at hs
      exact le_trans (ih (by omega)) hs
  intro j hj1 hj2 hej
  obtain ⟨t, ht⟩ : ∃ t, j = 2 + 2 * t := by obtain ⟨r, hr⟩ := hej; exact ⟨r - 1, by omega⟩
  subst ht
  obtain ⟨zX, hzX⟩ := sig_fst_isInt_even X.1.2 (show Even (2 + 2 * t) from ⟨1 + t, by ring⟩)
  obtain ⟨zY, hzY⟩ := sig_fst_isInt_even Y.1.2 (show Even (2 + 2 * t) from ⟨1 + t, by ring⟩)
  have hf := hmono t hj2
  rw [hzX, hzY] at hf ⊢
  linarith

/-- **Assembly** of §16 Branch B Case 5, `g₂` nonpolarized (type6, bottom `m = 0`).
Builds `g⁺(1)+g(k) → g⁺(k+1)` and proves `Z ≤ Y` over `0 < j < 2n'+3`: even-level
difference `(1,0)` absorbed by `hprop_even` (a-component), odd-level `(1/2,1/2)` by
`half_le_sigma_diff_at_r`.  Mirror of `exists_mutation_le_caseA_branchA_case1`. -/
lemma branchB_case5_assembly_type6 {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (n' : ℕ)
    (gm gk : Gene)
    (hgm_rank : gm.rank = 1) (hgm_pos : gm.type = .Positive)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hprop_even : ∀ j, 2 ≤ j → j ≤ 2 * n' + 2 → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hYwin : ∀ j, 1 ≤ j → j < 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hsigeq
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  have hle : (0 : ℕ) ≤ n' := Nat.zero_le n'
  let Y6' : Mix (Lambda, Pi) := Y6 hle hε
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * 0 + 1) .Positive = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm); rw [hgm_rank, hgm_pos] at h; exact h
  have hgk_eq : Gene.ofRank (2 * n' + 2) .NonPolarized = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk); rw [hgk_rank, hgk_np] at h; exact h
  have hX6_val : (X6 hle hε).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X6_eq, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X6 hle hε).1 + restval = X.1.1 := by
    rw [hX6_val]; exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Lambda, Pi) := ⟨Y6'.1 + restval, add_mem Y6'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X6 hle hε : Mix (Lambda, Pi)) + rest_M = X.1) ▸
    MixLambdaPi.Step.mk (X6 hle hε) Y6' rest_M
      (MixLambdaPi.Primitive.type6 GeneType.Positive hε hle), ?_⟩
  change Y6'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X6 hle hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 0
  · have h66 : signature (Chromosome.prime^[j] Y6'.1) =
        signature (Chromosome.prime^[j] (X6 hle hε).1) :=
      (sigma_type6_eq_before hle hε (hj := by omega)).symm
    rw [h66, ← hdecomp]; exact hXYj
  · have h_not_before : 2 * 0 < j := by omega
    by_cases hj_after : 2 * n' + 3 ≤ j
    · have h66 : signature (Chromosome.prime^[j] Y6'.1) =
          signature (Chromosome.prime^[j] (X6 hle hε).1) :=
        (sigma_type6_eq_after hle hε (hj := hj_after)).symm
      rw [h66, ← hdecomp]; exact hXYj
    · have h_mid : j < 2 * n' + 3 := by omega
      have hmid := sigma_type6_mid hle hε h_not_before h_mid
      have hY6_eq : signature (Chromosome.prime^[j] Y6'.1) =
          signature (Chromosome.prime^[j] (X6 hle hε).1) +
            (if Even (2 * n' + 2 - j) then signature (Gene.ofRank 1 GeneType.Positive)
             else ((1 : ℚ) / 2, (1 : ℚ) / 2)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY6_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * n' + 2 - j)
      · rw [if_pos hpar]
        have h_even_j : Even j := by
          have hp : (2 * n' + 2 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.even_iff]; omega
        rw [signature_ofRank_one_positive]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1 := by
          have hj2 : 2 ≤ j := by obtain ⟨t, ht⟩ := h_even_j; omega
          have h_sigma := hprop_even j hj2 (by omega) h_even_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · change (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          exact h_sigXj
        · change (signature (Chromosome.prime^[j] X.1.1)).2 + 0 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2
          rw [add_zero]; exact hXYj.2
      · rw [if_neg hpar]
        have hodd_j : Odd j := by
          have hp : (2 * n' + 2 - j) % 2 = 1 :=
            Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hpar)
          rw [Nat.odd_iff]; omega
        have hne' : signature (Chromosome.prime^[j] X.1.1) ≠
            signature (Chromosome.prime^[j] Y.1.1) := by
          intro h_eq
          exact hsigeq j (by omega)
            (hYwin j (by omega) (by rcases hodd_j with ⟨t, rfl⟩; omega))
            (by simpa [Sigma.sigma] using h_eq)
        rw [add_comm]
        exact half_le_sigma_diff_at_r X.1.2 Y.1.2 hodd_j hXYj hne'

/-- **Assembly** of §16 Branch B Case 5, `g₂ = g⁻(k)` (type7, bottom `m = 0`).
Builds `g⁺(1)+g⁻(k) → g(k+1)` and proves `Z ≤ Y` over `0 < j < 2n'+2`: even-level
difference `(1,0)` absorbed by `hprop_even`, odd-level `(1/2,1/2)` by `half_le`. -/
lemma branchB_case5_assembly_type7 {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (n' : ℕ)
    (gm gk : Gene)
    (hgm_rank : gm.rank = 1) (hgm_pos : gm.type = .Positive)
    (hgk_rank : gk.rank = 2 * n' + 1) (hgk_neg : gk.type = .Negative)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hprop_even : ∀ j, 2 ≤ j → j ≤ 2 * n' → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hYwin : ∀ j, 1 ≤ j → j ≤ 2 * n' + 1 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hsigeq
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  have hle : (0 : ℕ) ≤ n' := Nat.zero_le n'
  let Y7' : Mix (Lambda, Pi) := Y7 hle
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * 0 + 1) .Positive = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm); rw [hgm_rank, hgm_pos] at h; exact h
  have hgk_eq : Gene.ofRank (2 * n' + 1) .Negative = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk); rw [hgk_rank, hgk_neg] at h; exact h
  have hX7_val : (X7 hle hε).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X7_eq, GeneType.neg_positive, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X7 hle hε).1 + restval = X.1.1 := by
    rw [hX7_val]; exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Lambda, Pi) := ⟨Y7'.1 + restval, add_mem Y7'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X7 hle hε : Mix (Lambda, Pi)) + rest_M = X.1) ▸
    MixLambdaPi.Step.mk (X7 hle hε) Y7' rest_M
      (MixLambdaPi.Primitive.type7 GeneType.Positive hε hle), ?_⟩
  change Y7'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X7 hle hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 0
  · have h77 : signature (Chromosome.prime^[j] Y7'.1) =
        signature (Chromosome.prime^[j] (X7 hle hε).1) :=
      (sigma_type7_eq_before hle hε (hj := by omega)).symm
    rw [h77, ← hdecomp]; exact hXYj
  · have h_not_before : 2 * 0 < j := by omega
    by_cases hj_after : 2 * n' + 2 ≤ j
    · have h77 : signature (Chromosome.prime^[j] Y7'.1) =
          signature (Chromosome.prime^[j] (X7 hle hε).1) :=
        (sigma_type7_eq_after hle hε (hj := hj_after)).symm
      rw [h77, ← hdecomp]; exact hXYj
    · have h_mid : j < 2 * n' + 2 := by omega
      have hmid := sigma_type7_mid hle hε h_not_before h_mid
      have hY7_eq : signature (Chromosome.prime^[j] Y7'.1) =
          signature (Chromosome.prime^[j] (X7 hle hε).1) +
            (if Even (2 * n' + 1 - j) then ((1 : ℚ) / 2, (1 : ℚ) / 2)
             else signature (Gene.ofRank 1 GeneType.Positive)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY7_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * n' + 1 - j)
      · rw [if_pos hpar]
        have hodd_j : Odd j := by
          have hp : (2 * n' + 1 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.odd_iff]; omega
        have hne' : signature (Chromosome.prime^[j] X.1.1) ≠
            signature (Chromosome.prime^[j] Y.1.1) := by
          intro h_eq
          exact hsigeq j (by omega) (hYwin j (by omega) (by omega))
            (by simpa [Sigma.sigma] using h_eq)
        rw [add_comm]
        exact half_le_sigma_diff_at_r X.1.2 Y.1.2 hodd_j hXYj hne'
      · rw [if_neg hpar]
        have h_even_j : Even j := by
          have hp : (2 * n' + 1 - j) % 2 = 1 :=
            Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hpar)
          rw [Nat.even_iff]; omega
        rw [signature_ofRank_one_positive]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1 := by
          have hj2 : 2 ≤ j := by obtain ⟨t, ht⟩ := h_even_j; omega
          have hjle : j ≤ 2 * n' := by obtain ⟨t, ht⟩ := h_even_j; omega
          have h_sigma := hprop_even j hj2 hjle h_even_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · change (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          exact h_sigXj
        · change (signature (Chromosome.prime^[j] X.1.1)).2 + 0 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2
          rw [add_zero]; exact hXYj.2

/-- §16 Branch B, **Case 5** (`g₁ = g⁺(1)`).  `X` contains a negative or nonpolarized
gene `g₂` of minimal rank `k`; the mutation is `g⁺(1)+g(k) → g⁺(k+1)` (type6, bottom
`0`) or `g⁺(1)+g⁻(k) → g(k+1)` (type7, bottom `0`). -/
lemma branchB_case5 (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (_ : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pos : g₁.type = .Positive)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 1) (hm0 : m' = 0) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  subst hm0
  have hm1 : g₁.rank = 1 := by omega
  obtain ⟨g0, hg0mem, hg0np⟩ := branchB_case5_exists_negNP X Y hXY ha
  obtain ⟨g₂, hg₂mem, hg₂minS⟩ := Finset.exists_min_image
    (X.1.1.support.filter (fun g => g.type ≠ .Positive)) Gene.rank
    ⟨g0, Finset.mem_filter.mpr ⟨hg0mem, hg0np⟩⟩
  rw [Finset.mem_filter] at hg₂mem
  obtain ⟨hg₂supp, hg₂np⟩ := hg₂mem
  have hXg₂' : 0 < X.1.1 g₂ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂supp)
  have hk : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → g₂.rank ≤ g.rank :=
    fun g hg hgnp => hg₂minS g (Finset.mem_filter.mpr ⟨hg, hgnp⟩)
  have hne : g₁ ≠ g₂ := fun h => hg₂np (h ▸ hg₁pos)
  have hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]; exact hXg₂'
  cases hch : g₂.type with
  | Positive => exact absurd hch hg₂np
  | NonPolarized =>
    have hev : Even g₂.rank := rank_even_of_nonpolarized_mem X.1.2 hch hXg₂'
    obtain ⟨n', hn'⟩ : ∃ n', g₂.rank = 2 * n' + 2 := by
      have hge : 1 ≤ g₂.rank := by have := hg₁min g₂ hg₂supp; omega
      obtain ⟨t, ht⟩ := hev; exact ⟨t - 1, by omega⟩
    have hprop := branchB_case5_aprop_gen X Y hXY ha g₂.rank hk
    rw [hn'] at hprop
    have hYwin : ∀ j, 1 ≤ j → j < 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0 :=
      fun j _ hj => Ywin_below X Y hXY g₂ hXg₂' (by rw [hn']; omega)
    exact branchB_case5_assembly_type6 X Y hXY hsigeq n' g₁ g₂ hm1 hg₁pos hn' hch
      hXg₁ hXg₂ hne hprop hYwin
  | Negative =>
    have hodd : Odd g₂.rank :=
      rank_odd_of_polarized X.1.2 (by rw [hch]; decide) hXg₂'
    obtain ⟨n', hn'⟩ : ∃ n', g₂.rank = 2 * n' + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
    have hpropk := branchB_case5_aprop_gen X Y hXY ha g₂.rank hk
    rw [hn'] at hpropk
    have hprop : ∀ j, 2 ≤ j → j ≤ 2 * n' → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 :=
      fun j hj2 hjle hje => hpropk j hj2 (by omega) hje
    have hYwin : ∀ j, 1 ≤ j → j ≤ 2 * n' + 1 → Chromosome.prime^[j] Y.1.1 ≠ 0 := by
      intro j hj1 hj2
      rcases Nat.lt_or_ge j (2 * n' + 1) with hjlt | hjge
      · exact Ywin_below X Y hXY g₂ hXg₂' (by rw [hn']; omega)
      · -- j = 2n'+1 = g₂.rank: top boundary (gk = g⁻); b-mirror of Case 2 boundary
        have hjeq : j = 2 * n' + 1 := by omega
        rw [hjeq]
        exact branchB_case5_Ynonzero_top X Y hXY hcommon n' g₂ hn' hch hXg₂'
    exact branchB_case5_assembly_type7 X Y hXY hsigeq n' g₁ g₂ hm1 hg₁pos hn' hch
      hXg₁ hXg₂ hne hprop hYwin

/-- §16 Branch B, positive charge (`g₁ = g⁺(m)`).  Dispatch on `m = 1` vs `m ≥ 3`. -/
lemma branchB_pos (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pos : g₁.type = .Positive) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨m', hm'⟩ : ∃ m', g₁.rank = 2 * m' + 1 := by
    have hodd := rank_odd_of_polarized X.1.2 (by rw [hg₁pos]; decide) hXg₁
    rcases hodd with ⟨k, hk⟩; exact ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos m' with hm0 | hmpos
  · exact branchB_case5 m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hg₁pos m' hm' hm0
  · exact branchB_case3 m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hg₁pos m' hm' hmpos

/-- §16 Branch B, negative charge (`g₁ = g⁻(m)`), via sign-duality to `branchB_pos`
applied to `(-X, -Y)`. -/
lemma branchB_neg (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁neg : g₁.type = .Negative) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg₁pos' : (-g₁ : Gene).type = .Positive := by rw [Gene.neg_type, hg₁neg]; rfl
  set Xd : nMixLambdaPi (m + 2) :=
    ⟨- X.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, X.2]⟩ with Xd_def
  set Yd : nMixLambdaPi (m + 2) :=
    ⟨- Y.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, Y.2]⟩ with Yd_def
  have hXdYd : Xd.1 < Yd.1 := by change (- X.1) < (- Y.1); exact Chromosome.neg_lt_neg_iff.2 hXY
  have hcommond : ¬∃ g : Gene, 0 < Xd.1.1 g ∧ 0 < Yd.1.1 g := by
    refine fun ⟨g, hgX, hgY⟩ ↦ hcommon ⟨- g, ?_, ?_⟩
    · rw [← Chromosome.neg_apply]; convert hgX using 2; rfl
    · rw [← Chromosome.neg_apply]; convert hgY using 2; rfl
  have hsigeqd : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Yd.1.1 ≠ 0 ∧
      Sigma.sigma Xd.1.1 k = Sigma.sigma Yd.1.1 k := by
    refine fun ⟨k, hkpos, hYd_ne, hsig⟩ ↦ hsigeq ⟨k, hkpos, ?_, ?_⟩
    · refine fun hYzero ↦ hYd_ne ?_
      change Chromosome.prime^[k] (- Y.1.1) = 0
      rw [← prime_iterate_neg, hYzero, _root_.neg_zero]
    · have hsig_swap : (signature (Chromosome.prime^[k] (- X.1.1))).swap =
        (signature (Chromosome.prime^[k] (- Y.1.1))).swap := congrArg Prod.swap hsig
      rwa [← @prime_iterate_neg k X.1.1, ← @prime_iterate_neg k Y.1.1,
        signature_neg, signature_neg, Prod.swap_swap, Prod.swap_swap] at hsig_swap
  have hXpnd : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < Xd.1.1 g ∧ 0 < Xd.1.1 h := by
    refine fun ⟨g, h, hrank, hgpos, hhneg, hgX, hhX⟩ ↦ hXpn ⟨- h, - g, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Gene.neg_rank, hrank]
    · rw [Gene.neg_type, hhneg]; rfl
    · rw [Gene.neg_type, hgpos]; rfl
    · rw [← Chromosome.neg_apply]; convert hhX using 2; rfl
    · rw [← Chromosome.neg_apply]; convert hgX using 2; rfl
  have had : (Sigma.sigma Xd.1.1 1).1 < (Sigma.sigma Yd.1.1 1).1 := by
    change (signature (Chromosome.prime^[1] (- X.1.1))).1 <
      (signature (Chromosome.prime^[1] (- Y.1.1))).1
    rw [← @prime_iterate_neg 1 X.1.1, ← @prime_iterate_neg 1 Y.1.1,
      signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    have hXsym : (signature (Chromosome.prime^[1] X.1.1)).1 =
        (signature (Chromosome.prime^[1] X.1.1)).2 :=
      signature_prime_iterate_odd_eq_components X.1.2 (by decide)
    have hYsym : (signature (Chromosome.prime^[1] Y.1.1)).1 =
        (signature (Chromosome.prime^[1] Y.1.1)).2 :=
      signature_prime_iterate_odd_eq_components Y.1.2 (by decide)
    rw [← hXsym, ← hYsym]; exact ha
  have hXg₁d : 0 < Xd.1.1 (-g₁) := by
    change 0 < (- X.1.1) (-g₁); rw [Chromosome.neg_apply, neg_neg]; exact hXg₁
  have hg₁mind : ∀ g ∈ Xd.1.1.support, (-g₁ : Gene).rank ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff] at hg
    have hng : X.1.1 (-g) ≠ 0 := by
      change (- X.1.1) g ≠ 0 at hg; rwa [Chromosome.neg_apply] at hg
    have h := hg₁min (-g) (Finsupp.mem_support_iff.mpr hng)
    rw [Gene.neg_rank] at h ⊢; exact h
  obtain ⟨W, hstepW, hWY⟩ := branchB_pos m Xd Yd hXdYd hcommond hsigeqd hXpnd had
    (-g₁) hXg₁d hg₁mind hg₁pos'
  refine ⟨- W, ?_, ?_⟩
  · exact MixLambdaPi.Step.of_neg (by simpa only [neg_neg] using hstepW)
  · change (- W).1 ≤ Y.1.1
    rw [Mix.Lambda_Pi_neg_val]
    have hWY' : W.1 ≤ (- Y.1).1 := hWY
    rw [Mix.Lambda_Pi_neg_val] at hWY'
    simpa only [neg_neg] using Chromosome.neg_le_neg_iff.2 hWY'

/-- **Branch B** of §16 Case A: the minimal-rank gene `g₁` of `X` is polarized.
Dispatch on its charge. -/
lemma exists_mutation_le_caseA_branchB (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pol : g₁.type ≠ .NonPolarized) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  cases hch : g₁.type with
  | NonPolarized => exact absurd hch hg₁pol
  | Positive =>
    exact branchB_pos m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hch
  | Negative =>
    exact branchB_neg m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hch

/-- §16 Case A core for `Mix (Lambda, Pi)`: extract the minimal-rank gene of `X`
and dispatch on its polarization. -/
lemma exists_mutation_le_caseA (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXne : X.1.1 ≠ 0 := by
    intro h
    have hr0 : X.1.1.rank = 0 := rank_zero_iff.mpr h
    have hr : X.1.1.rank = m + 2 := X.2
    omega
  obtain ⟨g₁, hg₁mem, hg₁min⟩ := Finset.exists_min_image X.1.1.support Gene.rank
    (Finsupp.support_nonempty_iff.mpr hXne)
  rw [Finsupp.mem_support_iff] at hg₁mem
  have hXg₁ : 0 < X.1.1 g₁ := Nat.pos_of_ne_zero hg₁mem
  by_cases hpol : g₁.type = .NonPolarized
  · exact exists_mutation_le_caseA_branchA m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁
      hg₁min hpol
  · exact exists_mutation_le_caseA_branchB m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁
      hg₁min hpol

end MixLambdaPi
