import YoungDiagram.Theorem6.MixLambdaPi
import YoungDiagram.Theorem6.MixPiLambda
import YoungDiagram.Theorem6.MixLambdaPi.CaseB
import YoungDiagram.Theorem6.MixPiLambda.CaseA

/-!
# Case 4 (§15.10) for `Mix (Lambda, Pi)`.

This file factors the Case-4 obligation for `Mix (Lambda, Pi)` into:

* `exists_mutation_le_fifteen_ten_LP_caseA`: the sorried "Case A" core, where
  additionally `(sigma X 1).1 < (sigma Y 1).1`;
* `exists_mutation_le_fifteen_ten_LP`: the full Case 4, dispatching to Case A on
  the `<` branch and to its sign-dual (Case B) on the `¬<` branch.

This mirrors `Pi.exists_mutation_le_fifteen_ten` in `YoungDiagram/Theorem6/Pi.lean`.
The Case-B branch is fully proved via the negation lemmas; the Case-A core is
delegated to `MixLambdaPi.exists_mutation_le_caseA` / `MixPiLambda.exists_mutation_le_caseA`
(files `MixLambdaPi/CaseA.lean`, `MixPiLambda/CaseA.lean`), which dispatch on the
minimal-rank gene's polarization (§16 Branch A / Branch B); the two branch leaves
per variety are the remaining `sorry`s.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixVarietyJoint

/-- Case A of §15.10 for `Mix (Lambda, Pi)`: the additional hypothesis is
`(sigma X 1).1 < (sigma Y 1).1`. This is the sorried core. -/
lemma exists_mutation_le_fifteen_ten_LP_caseA (m : ℕ)
    (ihLP : ∀ k, k < m + 2 → ∀ X Y : nMixLambdaPi k, X.1 < Y.1 →
      ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (ihPL : ∀ k, k < m + 2 → ∀ X Y : nMixPiLambda k, X.1 < Y.1 →
      ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 :=
  MixLambdaPi.exists_mutation_le_caseA m X Y hXY hcommon hsigeq hXpn ha

/-- Case 4 (§15.10) for `Mix (Lambda, Pi)`. Dispatches to Case A on the branch
`(sigma X 1).1 < (sigma Y 1).1`; on the other branch builds the sign-dual and
reduces to Case A applied to `-X`, `-Y`. -/
lemma exists_mutation_le_fifteen_ten_LP (m : ℕ)
    (ihLP : ∀ k, k < m + 2 → ∀ X Y : nMixLambdaPi k, X.1 < Y.1 →
      ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (ihPL : ∀ k, k < m + 2 → ∀ X Y : nMixPiLambda k, X.1 < Y.1 →
      ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1
  · exact exists_mutation_le_fifteen_ten_LP_caseA m ihLP ihPL X Y hXY
      hcommon hsigeq hXpn ha
  · -- Case B: sign-dual of Case A.
    have ha_eq : (Sigma.sigma X.1.1 1).1 = (Sigma.sigma Y.1.1 1).1 :=
      le_antisymm (le_iff_dominates.mp hXY.le 1).1 (le_of_not_gt ha)
    have hYprime_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
      intro hYprime
      have hXprime_zero : Chromosome.prime^[1] X.1.1 = 0 := by
        have hle1 := le_iff_dominates.mp hXY.le 1
        simp only [hYprime, map_zero] at hle1
        exact signature_eq_zero (le_antisymm hle1 (signature_nonneg _))
      have hsig_all (k : ℕ) :
          signature (Chromosome.prime^[k] X.1.1) =
            signature (Chromosome.prime^[k] Y.1.1) := by
        cases k with
        | zero =>
            simp only [Function.iterate_zero, id_eq]
            have hsig_le := (le_iff_dominates.mp hXY.le) 0
            simp only [Function.iterate_zero, id] at hsig_le
            obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
            have hXsum := @signature_sum_eq_rank X.1.1
            have hYsum := @signature_sum_eq_rank Y.1.1
            have hXrank : (X.1.1.rank : ℚ) = m + 2 := by exact_mod_cast X.2
            have hYrank : (Y.1.1.rank : ℚ) = m + 2 := by exact_mod_cast Y.2
            exact Prod.ext (by linarith) (by linarith)
        | succ k =>
            rw [Function.iterate_one] at hXprime_zero hYprime
            simp only [Function.iterate_succ_apply, hXprime_zero, hYprime,
              iterate_map_zero, map_zero]
      exact (ne_of_lt hXY) <| Subtype.val_injective
        <| sigmaPair_Mix_Pi_Lambda.sigmaUnique_right X.1.2 Y.1.2 hsig_all
    have hsig_ne : Sigma.sigma X.1.1 1 ≠ Sigma.sigma Y.1.1 1 := fun hsig ↦
      hsigeq ⟨1, Nat.one_pos, hYprime_ne, hsig⟩
    have hb_ne : (Sigma.sigma X.1.1 1).2 ≠ (Sigma.sigma Y.1.1 1).2 := fun hb_eq ↦
      hsig_ne (Prod.ext ha_eq hb_eq)
    have hb_lt : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2 :=
      lt_of_le_of_ne (le_iff_dominates.mp hXY.le 1).2 hb_ne
    set Xd : nMixLambdaPi (m + 2) :=
      ⟨- X.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, X.2]⟩ with Xd_def
    set Yd : nMixLambdaPi (m + 2) :=
      ⟨- Y.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, Y.2]⟩ with Yd_def
    have hcommond : ¬∃ g : Gene, 0 < Xd.1.1 g ∧ 0 < Yd.1.1 g := by
      refine fun ⟨g, hgX, hgY⟩ ↦ hcommon ⟨- g, ?_, ?_⟩
      · rw [← Chromosome.neg_apply]
        convert hgX using 2; rfl
      · rw [← Chromosome.neg_apply]
        convert hgY using 2; rfl
    have hsigeqd : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Yd.1.1 ≠ 0 ∧
        Sigma.sigma Xd.1.1 k = Sigma.sigma Yd.1.1 k := by
      refine fun ⟨k, hkpos, hYd_ne, hsig⟩ ↦ hsigeq ⟨k, hkpos, ?_, ?_⟩
      · refine fun hYzero ↦ hYd_ne ?_
        change Chromosome.prime^[k] (- Y.1.1) = 0
        rw [← prime_iterate_neg, hYzero, _root_.neg_zero]
      · have hsig_swap : (signature (Chromosome.prime^[k] (- X.1.1))).swap =
          (signature (Chromosome.prime^[k] (- Y.1.1))).swap :=
            congrArg Prod.swap hsig
        rwa [← @prime_iterate_neg k X.1.1, ← @prime_iterate_neg k Y.1.1,
          signature_neg, signature_neg, Prod.swap_swap, Prod.swap_swap]
          at hsig_swap
    have hXpnd : ¬∃ (g h : Gene), g.rank = h.rank ∧
        g.type = .Positive ∧ h.type = .Negative ∧
        0 < Xd.1.1 g ∧ 0 < Xd.1.1 h := by
      refine fun ⟨g, h, hrank, hgpos, hhneg, hgX, hhX⟩ ↦
        hXpn ⟨- h, - g, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Gene.neg_rank, hrank]
      · rw [Gene.neg_type, hhneg]; rfl
      · rw [Gene.neg_type, hgpos]; rfl
      · rw [← Chromosome.neg_apply]; convert hhX using 2; rfl
      · rw [← Chromosome.neg_apply]; convert hgX using 2; rfl
    have had : (Sigma.sigma Xd.1.1 1).1 < (Sigma.sigma Yd.1.1 1).1 := by
      change (signature (Chromosome.prime^[1] (- X.1.1))).1 <
        (signature (Chromosome.prime^[1] (- Y.1.1))).1
      rwa [← @prime_iterate_neg 1 X.1.1, ← @prime_iterate_neg 1 Y.1.1,
        signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    have hXdYd : Xd.1 < Yd.1 := by
      change (- X.1) < (- Y.1)
      exact Chromosome.neg_lt_neg_iff.2 hXY
    obtain ⟨W, hstepW, hWY⟩ := exists_mutation_le_fifteen_ten_LP_caseA m ihLP ihPL
      Xd Yd hXdYd hcommond hsigeqd hXpnd had
    refine ⟨- W, ?_, ?_⟩
    · exact MixLambdaPi.Step.of_neg (by
        simpa only [neg_neg] using hstepW)
    · change (- W).1 ≤ Y.1.1
      rw [Mix.Lambda_Pi_neg_val]
      have : W.1 ≤ (- Y.1).1 := hWY
      rw [Mix.Lambda_Pi_neg_val] at this
      simpa only [neg_neg] using Chromosome.neg_le_neg_iff.2 this

/-- Case A of §15.10 for `Mix (Pi, Lambda)`: the additional hypothesis is
`(sigma X 1).1 < (sigma Y 1).1`. This is the sorried core. -/
lemma exists_mutation_le_fifteen_ten_PL_caseA (m : ℕ)
    (ihLP : ∀ k, k < m + 2 → ∀ X Y : nMixLambdaPi k, X.1 < Y.1 →
      ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (ihPL : ∀ k, k < m + 2 → ∀ X Y : nMixPiLambda k, X.1 < Y.1 →
      ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 :=
  MixPiLambda.exists_mutation_le_caseA m X Y hXY hcommon hsigeq hXpn ha

/-- Case 4 (§15.10) for `Mix (Pi, Lambda)`. Dispatches to Case A on the branch
`(sigma X 1).1 < (sigma Y 1).1`; on the other branch builds the sign-dual and
reduces to Case A applied to `-X`, `-Y`. -/
lemma exists_mutation_le_fifteen_ten_PL (m : ℕ)
    (ihLP : ∀ k, k < m + 2 → ∀ X Y : nMixLambdaPi k, X.1 < Y.1 →
      ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (ihPL : ∀ k, k < m + 2 → ∀ X Y : nMixPiLambda k, X.1 < Y.1 →
      ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1
  · exact exists_mutation_le_fifteen_ten_PL_caseA m ihLP ihPL X Y hXY
      hcommon hsigeq hXpn ha
  · -- Case B: sign-dual of Case A.
    have ha_eq : (Sigma.sigma X.1.1 1).1 = (Sigma.sigma Y.1.1 1).1 :=
      le_antisymm (le_iff_dominates.mp hXY.le 1).1 (le_of_not_gt ha)
    have hYprime_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
      intro hYprime
      have hXprime_zero : Chromosome.prime^[1] X.1.1 = 0 := by
        have hle1 := le_iff_dominates.mp hXY.le 1
        simp only [hYprime, map_zero] at hle1
        exact signature_eq_zero (le_antisymm hle1 (signature_nonneg _))
      have hsig_all (k : ℕ) :
          signature (Chromosome.prime^[k] X.1.1) =
            signature (Chromosome.prime^[k] Y.1.1) := by
        cases k with
        | zero =>
            simp only [Function.iterate_zero, id_eq]
            have hsig_le := (le_iff_dominates.mp hXY.le) 0
            simp only [Function.iterate_zero, id] at hsig_le
            obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
            have hXsum := @signature_sum_eq_rank X.1.1
            have hYsum := @signature_sum_eq_rank Y.1.1
            have hXrank : (X.1.1.rank : ℚ) = m + 2 := by exact_mod_cast X.2
            have hYrank : (Y.1.1.rank : ℚ) = m + 2 := by exact_mod_cast Y.2
            exact Prod.ext (by linarith) (by linarith)
        | succ k =>
            rw [Function.iterate_one] at hXprime_zero hYprime
            simp only [Function.iterate_succ_apply, hXprime_zero, hYprime,
              iterate_map_zero, map_zero]
      exact (ne_of_lt hXY) <| Subtype.val_injective
        <| sigmaPair_Mix_Pi_Lambda.sigmaUnique_left X.1.2 Y.1.2 hsig_all
    have hsig_ne : Sigma.sigma X.1.1 1 ≠ Sigma.sigma Y.1.1 1 := fun hsig ↦
      hsigeq ⟨1, Nat.one_pos, hYprime_ne, hsig⟩
    have hb_ne : (Sigma.sigma X.1.1 1).2 ≠ (Sigma.sigma Y.1.1 1).2 := fun hb_eq ↦
      hsig_ne (Prod.ext ha_eq hb_eq)
    have hb_lt : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2 :=
      lt_of_le_of_ne (le_iff_dominates.mp hXY.le 1).2 hb_ne
    set Xd : nMixPiLambda (m + 2) :=
      ⟨- X.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, X.2]⟩ with Xd_def
    set Yd : nMixPiLambda (m + 2) :=
      ⟨- Y.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, Y.2]⟩ with Yd_def
    have hcommond : ¬∃ g : Gene, 0 < Xd.1.1 g ∧ 0 < Yd.1.1 g := by
      refine fun ⟨g, hgX, hgY⟩ ↦ hcommon ⟨- g, ?_, ?_⟩
      · rw [← Chromosome.neg_apply]
        convert hgX using 2; rfl
      · rw [← Chromosome.neg_apply]
        convert hgY using 2; rfl
    have hsigeqd : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Yd.1.1 ≠ 0 ∧
        Sigma.sigma Xd.1.1 k = Sigma.sigma Yd.1.1 k := by
      refine fun ⟨k, hkpos, hYd_ne, hsig⟩ ↦ hsigeq ⟨k, hkpos, ?_, ?_⟩
      · refine fun hYzero ↦ hYd_ne ?_
        change Chromosome.prime^[k] (- Y.1.1) = 0
        rw [← prime_iterate_neg, hYzero, _root_.neg_zero]
      · have hsig_swap : (signature (Chromosome.prime^[k] (- X.1.1))).swap =
          (signature (Chromosome.prime^[k] (- Y.1.1))).swap :=
            congrArg Prod.swap hsig
        rwa [← @prime_iterate_neg k X.1.1, ← @prime_iterate_neg k Y.1.1,
          signature_neg, signature_neg, Prod.swap_swap, Prod.swap_swap]
          at hsig_swap
    have hXpnd : ¬∃ (g h : Gene), g.rank = h.rank ∧
        g.type = .Positive ∧ h.type = .Negative ∧
        0 < Xd.1.1 g ∧ 0 < Xd.1.1 h := by
      refine fun ⟨g, h, hrank, hgpos, hhneg, hgX, hhX⟩ ↦
        hXpn ⟨- h, - g, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Gene.neg_rank, hrank]
      · rw [Gene.neg_type, hhneg]; rfl
      · rw [Gene.neg_type, hgpos]; rfl
      · rw [← Chromosome.neg_apply]; convert hhX using 2; rfl
      · rw [← Chromosome.neg_apply]; convert hgX using 2; rfl
    have had : (Sigma.sigma Xd.1.1 1).1 < (Sigma.sigma Yd.1.1 1).1 := by
      change (signature (Chromosome.prime^[1] (- X.1.1))).1 <
        (signature (Chromosome.prime^[1] (- Y.1.1))).1
      rwa [← @prime_iterate_neg 1 X.1.1, ← @prime_iterate_neg 1 Y.1.1,
        signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    have hXdYd : Xd.1 < Yd.1 := by
      change (- X.1) < (- Y.1)
      exact Chromosome.neg_lt_neg_iff.2 hXY
    obtain ⟨W, hstepW, hWY⟩ := exists_mutation_le_fifteen_ten_PL_caseA m ihLP ihPL
      Xd Yd hXdYd hcommond hsigeqd hXpnd had
    refine ⟨- W, ?_, ?_⟩
    · exact MixPiLambda.Step.of_neg (by
        simpa only [neg_neg] using hstepW)
    · change (- W).1 ≤ Y.1.1
      rw [Mix.Pi_Lambda_neg_val]
      have : W.1 ≤ (- Y.1).1 := hWY
      rw [Mix.Pi_Lambda_neg_val] at this
      simpa only [neg_neg] using Chromosome.neg_le_neg_iff.2 this

end MixVarietyJoint
