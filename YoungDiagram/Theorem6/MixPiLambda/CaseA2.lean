import YoungDiagram.Theorem6.MixPiLambda.CaseAProp
import YoungDiagram.Theorem6.MixPiLambda.CaseA2Prop

/-!
# §16 Case A Branch A: Case 2 bottom-chain + boundary for `Mix (Pi, Lambda)`.

Parity-mirror of the corresponding pieces in `MixLambdaPi/CaseA.lean`.  For
`Mix (Pi, Lambda)` the minimal nonpolarized gene `g₁` has ODD rank `2m'+1`, so the
bottom-chain `b_m < d_m` (and the `a`-version for the `g⁻` charge) is anchored at the
odd level `2m'+1` and only applies for `m' ≥ 1` (the `m'=0`, i.e. `m=1`, case is the
separate `g₃` sub-case).  The Case-2 top boundary is `prime^[2n'+2] Y ≠ 0`.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- **§16 bottom-chain `b_m < d_m`** for Branch A Case 2, `Mix (Pi, Lambda)`, at the odd
anchor `m = 2m'+1` with `m' ≥ 1`.  Uses the odd branch of `cond_15_7_Mix_Pi_Lambda`,
rank antitonicity, the level-1 gap, and `twostep_snd = cells`. -/
lemma branchA_case2_bm_lt {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' : ℕ) (hm'pos : 1 ≤ m')
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank) :
    (Sigma.sigma X.1.1 (2 * m' + 1)).2 < (Sigma.sigma Y.1.1 (2 * m' + 1)).2 := by
  have e1 : 2 * m' - 1 + 1 = 2 * m' := by omega
  have e2 : 2 * m' - 1 + 2 = 2 * m' + 1 := by omega
  have hodd : ¬ Even (2 * m' - 1) := by
    rw [Nat.not_even_iff_odd]; exact ⟨m' - 1, by omega⟩
  have hcond := cond_15_7_Mix_Pi_Lambda Y.1.2 (2 * m' - 1)
  rw [if_neg hodd, e1, e2] at hcond
  have hdrop := rank_drop_le Y.1.2 (2 * m' - 1)
  rw [e1] at hdrop
  have hbX := twostep_snd (W := X.1.1) (i := 2 * m' - 1)
    (fun g hg => by have := hmin g hg; omega)
  rw [e2] at hbX
  have hcells : (X.1.1.rank : ℚ) - ((Chromosome.prime^[1] X.1.1).rank : ℚ) =
      X.1.1.sum (fun _ m => (m : ℚ)) := by
    rw [Function.iterate_one]; exact cells
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
    simpa [Sigma.sigma] using this
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
    simpa [Sigma.sigma] using this
  have hXrank : (X.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast X.2
  have hYrank : (Y.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast Y.2
  have hb1 : (Sigma.sigma X.1.1 1).2 ≤ (Sigma.sigma Y.1.1 1).2 :=
    (le_iff_dominates.mp hXY.le 1).2
  have hbX2m : (Sigma.sigma X.1.1 (2 * m' - 1)).2 ≤ (Sigma.sigma Y.1.1 (2 * m' - 1)).2 :=
    (le_iff_dominates.mp hXY.le (2 * m' - 1)).2
  linarith

/-- **§16 bottom-chain `a_m < c_m`** for Branch A Case 2, `Mix (Pi, Lambda)` (the
`g⁻` charge via sign-duality).  `a`-component analogue of `branchA_case2_bm_lt`. -/
lemma branchA_case2_am_lt {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' : ℕ) (hm'pos : 1 ≤ m')
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank) :
    (Sigma.sigma X.1.1 (2 * m' + 1)).1 < (Sigma.sigma Y.1.1 (2 * m' + 1)).1 := by
  have e1 : 2 * m' - 1 + 1 = 2 * m' := by omega
  have e2 : 2 * m' - 1 + 2 = 2 * m' + 1 := by omega
  have hodd : ¬ Even (2 * m' - 1) := by
    rw [Nat.not_even_iff_odd]; exact ⟨m' - 1, by omega⟩
  have hcond := cond_15_6_Mix_Pi_Lambda Y.1.2 (2 * m' - 1)
  rw [if_neg hodd, e1, e2] at hcond
  have hdrop := rank_drop_le Y.1.2 (2 * m' - 1)
  rw [e1] at hdrop
  have hbX := twostep (W := X.1.1) (i := 2 * m' - 1)
    (fun g hg => by have := hmin g hg; omega)
  rw [e2] at hbX
  have hcells : (X.1.1.rank : ℚ) - ((Chromosome.prime^[1] X.1.1).rank : ℚ) =
      X.1.1.sum (fun _ m => (m : ℚ)) := by
    rw [Function.iterate_one]; exact cells
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
    simpa [Sigma.sigma] using this
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
    simpa [Sigma.sigma] using this
  have hXrank : (X.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast X.2
  have hYrank : (Y.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast Y.2
  have hb1 : (Sigma.sigma X.1.1 1).2 ≤ (Sigma.sigma Y.1.1 1).2 :=
    (le_iff_dominates.mp hXY.le 1).2
  have haX2m : (Sigma.sigma X.1.1 (2 * m' - 1)).1 ≤ (Sigma.sigma Y.1.1 (2 * m' - 1)).1 :=
    (le_iff_dominates.mp hXY.le (2 * m' - 1)).1
  linarith

/-- **Top-boundary nonvanishing for §16 Branch A Case 2** (`Mix (Pi, Lambda)`,
`gk = g⁺(2n'+2)`): `prime^[2n'+2] Y ≠ 0`.  b-mirror style: if it vanished,
`prime^[2n'+1] Y` (which lives in `Mix (Lambda, Pi)`, oddPart ∈ Pi) would consist only of
rank-1 polarized genes, none positive (a positive `g⁺(1)` would trace to `Y gk = 0` by
disjointness), so its first signature component is `0`, contradicting `a_X(2n'+1) ≥ 1`. -/
lemma branchA_case2_Ynonzero_top {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (n' : ℕ) (gk : Gene) (hgk_rank : gk.rank = 2 * n' + 2)
    (hgk_pos : gk.type = .Positive) (hXgk : 0 < X.1.1 gk) :
    Chromosome.prime^[2 * n' + 2] Y.1.1 ≠ 0 := by
  push_neg at hcommon
  intro hYzero
  have haX : 1 ≤ (signature (Chromosome.prime^[2 * n' + 1] X.1.1)).1 := by
    have := one_le_signature_fst_of_contains_positive_mix X.1.2 hgk_pos hXgk
    rwa [hgk_rank, show 2 * n' + 2 - 1 = 2 * n' + 1 from by omega] at this
  have haY : 1 ≤ (signature (Chromosome.prime^[2 * n' + 1] Y.1.1)).1 :=
    le_trans haX (le_iff_dominates.mp hXY.le (2 * n' + 1)).1
  set W := Chromosome.prime^[2 * n' + 1] Y.1.1 with hWdef
  have hWprime : Chromosome.prime W = 0 := by
    rw [hWdef, ← Function.iterate_succ_apply' Chromosome.prime (2 * n' + 1) Y.1.1]
    exact hYzero
  have hWmem : W ∈ Mix (Lambda, Pi) := by
    have hodd : ¬ Even (2 * n' + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨n', by ring⟩
    have h := prime_mem_Mix_Pi_Lambda_iterate Y.1.2 (2 * n' + 1)
    rwa [if_neg hodd] at h
  have hWgenes : ∀ h ∈ W.support, h.signature.1 = 0 := by
    intro h hh
    have hr1 : h.rank = 1 := rank_one_of_prime_eq_zero hWprime hh
    have hpol : h.type ≠ .NonPolarized := by
      have hod : 0 < W.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos (by rw [hr1]; exact ⟨0, rfl⟩)]
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      exact IsPolarized_def'.mp (mem_Pi_iff.mp hWmem.2) h
        (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hod))
    have hnpos : h.type ≠ .Positive := by
      intro hpos
      have hWh : W h = Y.1.1 ⟨h.rank + (2 * n' + 1), h.type,
          Nat.le_add_right_of_le h.rank_pos⟩ := prime_iterate_coeff (2 * n' + 1) Y.1.1 h
      have hge : (⟨h.rank + (2 * n' + 1), h.type, Nat.le_add_right_of_le h.rank_pos⟩ : Gene) = gk :=
        Gene.ext (by show h.rank + (2 * n' + 1) = gk.rank; rw [hgk_rank]; omega)
          (by show h.type = gk.type; rw [hpos, hgk_pos])
      rw [hge] at hWh
      have hYgk : Y.1.1 gk = 0 := Nat.le_zero.mp (hcommon gk hXgk)
      rw [hYgk] at hWh
      exact (Finsupp.mem_support_iff.mp hh) hWh
    have hneg : h.type = .Negative := by
      cases ht : h.type with
      | NonPolarized => exact absurd ht hpol
      | Positive => exact absurd ht hnpos
      | Negative => rfl
    rw [Gene.signature_of_negative hneg, if_neg (by rw [hr1]; decide)]
    simp [hr1]
  have hW0 : (signature W).1 = 0 := by
    rw [signature_fst, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro h hh
    rw [hWgenes h hh, smul_zero]
  rw [hW0] at haY
  linarith

/-- **Branch A Case 1 driver** (`Mix (Pi, Lambda)`).  Chains the propagation core and the
type4 assembly. -/
lemma exists_mutation_le_caseA_branchA_case1_full {N : ℕ}
    (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hgap_nat : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (m' n' : ℕ) (hmn : m' < n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 1) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 1) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 1 ≤ g.rank)
    (ha_m : (Sigma.sigma X.1.1 (2 * m' + 1)).1 < (Sigma.sigma Y.1.1 (2 * m' + 1)).1) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : gm ≠ gk := by intro h; rw [h, hgk_rank] at hgm_rank; omega
  obtain ⟨hprop_odd, hYwin⟩ := exists_mutation_le_caseA_branchA_case1_propagate
    X Y hXY hgap_nat m' n' (le_of_lt hmn) gm gk hgm_rank hgm_np hgk_rank hgk_np
    hXgm hXgk hne hmin h2nd ha_m
  exact exists_mutation_le_caseA_branchA_case1 X Y hXY hsigeq m' n' (le_of_lt hmn)
    gm gk hgm_rank hgm_np hgk_rank hgk_np hXgm hXgk hne hprop_odd hYwin

/-- **Branch A Case 2 driver** (`g₂ = g⁺(k)`, `Mix (Pi, Lambda)`).  Chains the
`b`-propagation, the top boundary, and the type5 assembly. -/
lemma branchA_case2_full {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hgap_nat : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene) (hgm_rank : gm.rank = 2 * m' + 1) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_pos : gk.type = .Positive)
    (hgm1 : X.1.1 gm = 1) (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 2 ≤ g.rank)
    (hb_m : (Sigma.sigma X.1.1 (2 * m' + 1)).2 < (Sigma.sigma Y.1.1 (2 * m' + 1)).2) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : gm ≠ gk := by intro h; rw [h, hgk_rank] at hgm_rank; omega
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hprop := branchA_case2_bprop X Y hgap_nat m' n' hmn gm hgm_rank hgm_np hgm1 hmin
    (fun g hg => le_trans (by omega) (h2nd g hg)) hb_m
  have hYwin : ∀ j, 2 * m' + 1 ≤ j → j ≤ 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0 := by
    intro j _ hj2
    by_cases hjtop : j = 2 * n' + 2
    · subst hjtop
      exact branchA_case2_Ynonzero_top X Y hXY hcommon n' gk hgk_rank hgk_pos hXgk'
    · intro hYzero
      have hXj : Chromosome.prime^[j] X.1.1 ≠ 0 := by
        intro hXzero
        have hle := prime_iterate_eq_zero_rank_le.mpr hXzero gk
          (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hXgk'))
        rw [hgk_rank] at hle; omega
      have hsig_le := le_iff_dominates.mp hXY.le j
      rw [hYzero, map_zero] at hsig_le
      exact hXj (signature_eq_zero (le_antisymm hsig_le (signature_nonneg _)))
  exact exists_mutation_le_caseA_branchA_case2_assembly X Y hXY hsigeq m' n' hmn gm gk
    hgm_rank hgm_np hgk_rank hgk_pos hXgm hXgk hne hprop hYwin

/-- Branch A edge case: `X` is a single nonpolarized gene `g₁` (no second gene).  Vacuous:
`Y` of equal rank with `X ≤ Y` forces `Y = X` (the unique odd-rank gene shape). -/
lemma branchA_single_gene (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁) (hg₁NP : g₁.type = .NonPolarized)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 1) (hmult1 : X.1.1 g₁ = 1)
    (hsingle : X.1.1 = Finsupp.single g₁ 1) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  exfalso
  have hg₁_rank_eq : g₁.rank = m + 2 := by
    have h : X.1.1.rank = g₁.rank := by rw [hsingle, rank_single, one_smul]
    rw [X.2] at h; exact h.symm
  have hX_ne : Chromosome.prime^[m + 1] X.1.1 ≠ 0 := by
    have hval : Chromosome.prime^[m + 1] X.1.1 = Gene.ofRank 1 g₁.type := by
      rw [hsingle, ← Gene.ofRank_eq_gene, prime_iterate_ofRank, hg₁_rank_eq,
        show m + 2 - (m + 1) = 1 from by omega]
    rw [hval, Gene.ofRank_eq_gene' (by norm_num)]
    simp
  have hY_ne : Chromosome.prime^[m + 1] Y.1.1 ≠ 0 := by
    intro hYzero
    have hle := le_iff_dominates.mp hXY.le (m + 1)
    rw [hYzero, map_zero] at hle
    exact hX_ne (signature_eq_zero (le_antisymm hle (signature_nonneg _)))
  have hmaxY_ge : m + 2 ≤ Y.1.1.maxRank := by
    by_contra hlt
    push_neg at hlt
    exact hY_ne (prime_iterate_zero_of_maxRank_le (by omega))
  have hmaxY_le : Y.1.1.maxRank ≤ m + 2 := by
    have h := maxRank_le_rank Y.1.1; rwa [Y.2] at h
  have hmaxY : Y.1.1.maxRank = m + 2 := le_antisymm hmaxY_le hmaxY_ge
  obtain ⟨g₂, hg₂rank, hY_eq⟩ :=
    rank_eq_maxRank_single (by rw [Y.2, hmaxY]) (by rw [hmaxY]; omega)
  have hg₂rank' : g₂.rank = m + 2 := by rw [hg₂rank, hmaxY]
  have hg₂supp : g₂ ∈ Y.1.1.support := by rw [hY_eq]; simp
  have hg₂odd : Odd g₂.rank := by
    rw [hg₂rank', ← hg₁_rank_eq, hm']; exact ⟨m', by ring⟩
  have hg₂NP : g₂.type = .NonPolarized := by
    have hg₂Yodd : 0 < Y.1.1.oddPart g₂ := by
      rw [oddPart_eq, Finsupp.filter_apply, if_pos hg₂odd]
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂supp)
    exact IsNonPolarized_def'.mp (mem_Lambda_iff.mp Y.1.2.2) g₂
      (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hg₂Yodd))
  have hg₂eq : g₂ = g₁ := Gene.ext (by rw [hg₂rank', hg₁_rank_eq]) (hg₂NP.trans hg₁NP.symm)
  rw [hg₂eq] at hY_eq
  have hXYeq : X.1.1 = Y.1.1 := by rw [hsingle, hY_eq]
  exact (ne_of_lt hXY) (Subtype.ext hXYeq)

/-- Branch A Case 1, `b`-component sub-branch (`b_m < d_m`): the sign-dual of
`case1_full` (apply Case 1 to `-X`, `-Y`, then negate).  Level-1 asymmetry is sidestepped
since `case1_full` takes the self-dual total-rank gap. -/
lemma branchA_case1_neg (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 1)
    (g₂ : Gene) (n' : ℕ) (hg₂rank : g₂.rank = 2 * n' + 1)
    (hg₂NP : g₂.type = .NonPolarized) (hmn : m' < n')
    (hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂)
    (hg₂min : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * n' + 1 ≤ g.rank)
    (hb_m : (Sigma.sigma X.1.1 (2 * m' + 1)).2 < (Sigma.sigma Y.1.1 (2 * m' + 1)).2) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg₁neg : (-g₁ : Gene) = g₁ := Gene.ext (Gene.neg_rank g₁) (by rw [Gene.neg_type, hg₁NP]; rfl)
  have hg₂neg : (-g₂ : Gene) = g₂ := Gene.ext (Gene.neg_rank g₂) (by rw [Gene.neg_type, hg₂NP]; rfl)
  set Xd : nMixPiLambda (m + 2) :=
    ⟨- X.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, X.2]⟩ with Xd_def
  set Yd : nMixPiLambda (m + 2) :=
    ⟨- Y.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, Y.2]⟩ with Yd_def
  have hXdYd : Xd.1 < Yd.1 := by change (- X.1) < (- Y.1); exact Chromosome.neg_lt_neg_iff.2 hXY
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
  have hgap_d : (Chromosome.prime^[1] Xd.1.1).rank < (Chromosome.prime^[1] Yd.1.1).rank := by
    have e1 : Chromosome.prime^[1] Xd.1.1 = - (Chromosome.prime^[1] X.1.1) := by
      change Chromosome.prime^[1] (- X.1.1) = _; rw [prime_iterate_neg]
    have e2 : Chromosome.prime^[1] Yd.1.1 = - (Chromosome.prime^[1] Y.1.1) := by
      change Chromosome.prime^[1] (- Y.1.1) = _; rw [prime_iterate_neg]
    rw [e1, e2, rank_neg, rank_neg]; exact rank_gap_one X Y hXY ha
  have hsingle_neg : ∀ g, (Finsupp.single g₁ 1 : Chromosome) g =
      (Finsupp.single g₁ 1 : Chromosome) (-g) := by
    intro g
    have hiff : (g₁ = g) ↔ (g₁ = -g) := by
      constructor
      · rintro rfl; exact hg₁neg.symm
      · intro h
        have h2 : -g₁ = g := by rw [h, neg_neg]
        rw [← hg₁neg]; exact h2
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : g₁ = g
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hval : ∀ g, (Xd.1.1 - Finsupp.single g₁ 1 : Chromosome) g
      = (X.1.1 - Finsupp.single g₁ 1 : Chromosome) (-g) := by
    intro g; rw [Finsupp.tsub_apply, Finsupp.tsub_apply, hsingle_neg g]; congr 1
  have hXgm : 0 < Xd.1.1 g₁ := by
    change 0 < (- X.1.1) g₁; rw [Chromosome.neg_apply, hg₁neg]; exact hXg₁
  have hXgk : 0 < (Xd.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := by
    rw [hval g₂, hg₂neg]; exact hXg₂
  have hmin : ∀ g ∈ Xd.1.1.support, 2 * m' + 1 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff] at hg
    have hng : X.1.1 (-g) ≠ 0 := by
      change (- X.1.1) g ≠ 0 at hg; rwa [Chromosome.neg_apply] at hg
    have h := hg₁min (-g) (Finsupp.mem_support_iff.mpr hng)
    rw [hm', Gene.neg_rank] at h; exact h
  have h2nd : ∀ g ∈ (Xd.1.1 - Finsupp.single g₁ 1).support, 2 * n' + 1 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff, hval g] at hg
    have h := hg₂min (-g) (Finsupp.mem_support_iff.mpr hg)
    rwa [Gene.neg_rank] at h
  have ha_m_d : (Sigma.sigma Xd.1.1 (2 * m' + 1)).1 <
      (Sigma.sigma Yd.1.1 (2 * m' + 1)).1 := by
    change (signature (Chromosome.prime^[2 * m' + 1] (- X.1.1))).1 <
      (signature (Chromosome.prime^[2 * m' + 1] (- Y.1.1))).1
    rw [← @prime_iterate_neg (2 * m' + 1) X.1.1, ← @prime_iterate_neg (2 * m' + 1) Y.1.1,
      signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    exact hb_m
  obtain ⟨W, hstepW, hWY⟩ := exists_mutation_le_caseA_branchA_case1_full Xd Yd hXdYd
    hsigeqd hgap_d m' n' hmn g₁ g₂ hm' hg₁NP hg₂rank hg₂NP hXgm hXgk hmin h2nd ha_m_d
  refine ⟨- W, ?_, ?_⟩
  · exact MixPiLambda.Step.of_neg (by simpa only [neg_neg] using hstepW)
  · change (- W).1 ≤ Y.1.1
    rw [Mix.Pi_Lambda_neg_val]
    have hWY' : W.1 ≤ (- Y.1).1 := hWY
    rw [Mix.Pi_Lambda_neg_val] at hWY'
    simpa only [neg_neg] using Chromosome.neg_le_neg_iff.2 hWY'

/-- **Branch A Case 2 driver, `g₂ = g⁻(k)` charge** (via sign-duality to the `g⁺` driver
applied to `(-X, -Y)`).  Takes the anchor `a`-strict `ha_anchor` (from `am_lt` for `m'≥1`,
or directly from `ha` when `m'=0`). -/
lemma branchA_case2_full_neg {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene) (hgm_rank : gm.rank = 2 * m' + 1) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_neg : gk.type = .Negative)
    (hgm1 : X.1.1 gm = 1) (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 2 ≤ g.rank)
    (ha_anchor : (Sigma.sigma X.1.1 (2 * m' + 1)).1 < (Sigma.sigma Y.1.1 (2 * m' + 1)).1) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg₁neg : (-gm : Gene) = gm := Gene.ext (Gene.neg_rank gm) (by rw [Gene.neg_type, hgm_np]; rfl)
  set Xd : nMixPiLambda N := ⟨- X.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, X.2]⟩ with Xd_def
  set Yd : nMixPiLambda N := ⟨- Y.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, Y.2]⟩ with Yd_def
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
  have hgap_d : (Chromosome.prime^[1] Xd.1.1).rank < (Chromosome.prime^[1] Yd.1.1).rank := by
    have e1 : Chromosome.prime^[1] Xd.1.1 = - (Chromosome.prime^[1] X.1.1) := by
      change Chromosome.prime^[1] (- X.1.1) = _; rw [prime_iterate_neg]
    have e2 : Chromosome.prime^[1] Yd.1.1 = - (Chromosome.prime^[1] Y.1.1) := by
      change Chromosome.prime^[1] (- Y.1.1) = _; rw [prime_iterate_neg]
    rw [e1, e2, rank_neg, rank_neg]; exact rank_gap_one X Y hXY ha
  have hgm1_d : Xd.1.1 gm = 1 := by
    change (- X.1.1) gm = 1; rw [Chromosome.neg_apply, hg₁neg]; exact hgm1
  have hXgm_d : 0 < Xd.1.1 gm := by
    change 0 < (- X.1.1) gm; rw [Chromosome.neg_apply, hg₁neg]; exact hXgm
  have hsingle_neg : ∀ g, (Finsupp.single gm 1 : Chromosome) g =
      (Finsupp.single gm 1 : Chromosome) (-g) := by
    intro g
    have hiff : (gm = g) ↔ (gm = -g) := by
      constructor
      · rintro rfl; exact hg₁neg.symm
      · intro h
        have h2 : -gm = g := by rw [h, neg_neg]
        rw [← hg₁neg]; exact h2
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : gm = g
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hval : ∀ g, (Xd.1.1 - Finsupp.single gm 1 : Chromosome) g
      = (X.1.1 - Finsupp.single gm 1 : Chromosome) (-g) := by
    intro g; rw [Finsupp.tsub_apply, Finsupp.tsub_apply, hsingle_neg g]; congr 1
  have hgk'_rank : (-gk : Gene).rank = 2 * n' + 2 := by rw [Gene.neg_rank, hgk_rank]
  have hgk'_pos : (-gk : Gene).type = .Positive := by rw [Gene.neg_type, hgk_neg]; rfl
  have hXgk_d : 0 < (Xd.1.1 - Finsupp.single gm 1 : Chromosome) (-gk) := by
    rw [hval (-gk), neg_neg]; exact hXgk
  have hmin_d : ∀ g ∈ Xd.1.1.support, 2 * m' + 1 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff] at hg
    have hng : X.1.1 (-g) ≠ 0 := by
      change (- X.1.1) g ≠ 0 at hg; rwa [Chromosome.neg_apply] at hg
    have h := hmin (-g) (Finsupp.mem_support_iff.mpr hng); rwa [Gene.neg_rank] at h
  have h2nd_d : ∀ g ∈ (Xd.1.1 - Finsupp.single gm 1).support, 2 * n' + 2 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff, hval g] at hg
    have h := h2nd (-g) (Finsupp.mem_support_iff.mpr hg); rwa [Gene.neg_rank] at h
  have hb_m_d : (Sigma.sigma Xd.1.1 (2 * m' + 1)).2 <
      (Sigma.sigma Yd.1.1 (2 * m' + 1)).2 := by
    change (signature (Chromosome.prime^[2 * m' + 1] (- X.1.1))).2 <
      (signature (Chromosome.prime^[2 * m' + 1] (- Y.1.1))).2
    rw [← @prime_iterate_neg (2 * m' + 1) X.1.1, ← @prime_iterate_neg (2 * m' + 1) Y.1.1,
      signature_neg, signature_neg, Prod.snd_swap, Prod.snd_swap]
    exact ha_anchor
  obtain ⟨W, hstepW, hWY⟩ := branchA_case2_full Xd Yd hXdYd hcommond hsigeqd hgap_d m' n' hmn
    gm (-gk) hgm_rank hgm_np hgk'_rank hgk'_pos hgm1_d hXgm_d hXgk_d hmin_d h2nd_d hb_m_d
  refine ⟨- W, ?_, ?_⟩
  · exact MixPiLambda.Step.of_neg (by simpa only [neg_neg] using hstepW)
  · change (- W).1 ≤ Y.1.1
    rw [Mix.Pi_Lambda_neg_val]
    have hWY' : W.1 ≤ (- Y.1).1 := hWY
    rw [Mix.Pi_Lambda_neg_val] at hWY'
    simpa only [neg_neg] using Chromosome.neg_le_neg_iff.2 hWY'

/-- **§16 Case 2 `m=1`, `b₁=d₁` sub-case** (the PL-specific `g₃` leaf).  Here `g₁=g(1)`,
`g₂=g⁺(k)`, `a₁<c₁` (`ha`) and `b₁=d₁`, so `X - g₁ - g₂` contains a negative or
nonpolarized gene `g₃` of minimal rank `t`; the mutation `g₂+g₃ → g(k-1)+g(t+1)`
(`t` even) or `g₂+g₃ → g(k-1)+g⁺(t+1)` (`t` odd) gives `Z ≤ Y`.  Formalization target. -/
lemma branchA_case2_g3 (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ g₂ : Gene) (n' : ℕ)
    (hg₁NP : g₁.type = .NonPolarized) (hg₁rank : g₁.rank = 1)
    (hXg₁ : 0 < X.1.1 g₁) (hmult1 : X.1.1 g₁ = 1)
    (hg₂pos : g₂.type = .Positive) (hg₂rank : g₂.rank = 2 * n' + 2)
    (hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₂min : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, g₂.rank ≤ g.rank)
    (hb1 : (Sigma.sigma X.1.1 1).2 = (Sigma.sigma Y.1.1 1).2) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  clear hb1 hXg₁
  -- Extract the minimal-rank negative/nonpolarized gene `g₃` of `X - g₁ - g₂`.
  set Xr : Chromosome := X.1.1 - Finsupp.single g₁ 1 - Finsupp.single g₂ 1 with hXr
  have hSne : (Xr.support.filter (fun g => g.type ≠ .Positive)).Nonempty := by
    obtain ⟨g₃, hg₃mem, hg₃np⟩ :=
      branchA_g3_exists X Y hXY ha g₁ g₂ hg₁NP hg₁rank hmult1 hg₁min hg₂pos
    exact ⟨g₃, Finset.mem_filter.mpr ⟨hg₃mem, hg₃np⟩⟩
  obtain ⟨g₃, hg₃S, hg₃min_S⟩ :=
    Finset.exists_min_image (Xr.support.filter (fun g => g.type ≠ .Positive)) Gene.rank hSne
  have hg₃mem : g₃ ∈ Xr.support := (Finset.mem_filter.mp hg₃S).1
  have hg₃nepos : g₃.type ≠ .Positive := (Finset.mem_filter.mp hg₃S).2
  have hXrg₃ : 0 < Xr g₃ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₃mem)
  have hg₃ne₂ : g₃ ≠ g₂ := fun h => hg₃nepos (h ▸ hg₂pos)
  have hne : g₂ ≠ g₃ := fun h => hg₃nepos (h ▸ hg₂pos)
  have hg₃ne₁ : g₃ ≠ g₁ := by
    rintro rfl
    apply absurd hXrg₃
    rw [hXr, Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl, hmult1]
    simp
  have hXrg₃eq : Xr g₃ = X.1.1 g₃ := by
    simp only [hXr, Finsupp.tsub_apply, Finsupp.single_apply]
    rw [if_neg (Ne.symm hg₃ne₁), if_neg (Ne.symm hg₃ne₂)]
    omega
  have hXg₃pos : 0 < X.1.1 g₃ := hXrg₃eq ▸ hXrg₃
  have hXg₂pos : 0 < X.1.1 g₂ :=
    lt_of_lt_of_le hXg₂ (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
  have hXg₃sub : 0 < (X.1.1 - Finsupp.single g₂ 1 : Chromosome) g₃ := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hg₃ne₂), Nat.sub_zero]
    exact hXg₃pos
  -- `g₃` lies above `g₂`: `2n'+3 ≤ rank g₃` (a `g⁻(2n'+2)` would clash with `g₂` via `hXpn`).
  have hg₃X1 : g₃ ∈ (X.1.1 - Finsupp.single g₁ 1).support := by
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_apply,
      if_neg (Ne.symm hg₃ne₁), Nat.sub_zero]
    omega
  have hge : 2 * n' + 2 ≤ g₃.rank := hg₂rank ▸ hg₂min g₃ hg₃X1
  have hgt : 2 * n' + 3 ≤ g₃.rank := by
    rcases lt_or_ge (2 * n' + 2) g₃.rank with h | h
    · omega
    · exfalso
      have heq : g₃.rank = 2 * n' + 2 := le_antisymm h hge
      have hg₃neg : g₃.type = .Negative := by
        cases ht : g₃.type with
        | Positive => exact absurd ht hg₃nepos
        | Negative => rfl
        | NonPolarized =>
          exfalso
          have hodd := rank_odd_of_nonpolarized_mem X.1.2 ht hXg₃pos
          rw [heq] at hodd
          exact (Nat.not_odd_iff_even.mpr ⟨n' + 1, by ring⟩) hodd
      exact hXpn ⟨g₂, g₃, by rw [hg₂rank, heq], hg₂pos, hg₃neg, hXg₂pos, hXg₃pos⟩
  -- Parity of `X`'s polarized genes, and the survival threshold for the propagation.
  have hpar : ∀ g ∈ X.1.1.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank) := by
    intro g hg
    have hgpos : 0 < X.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
    exact ⟨fun hp => rank_even_of_polarized X.1.2 (by rw [hp]; decide) hgpos,
           fun hn => rank_even_of_polarized X.1.2 (by rw [hn]; decide) hgpos⟩
  have hsurv : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → (g.rank ≤ 1 ∨ g₃.rank ≤ g.rank) := by
    intro g hg hgnp
    by_cases hgg₁ : g = g₁
    · left; rw [hgg₁]; omega
    · right
      have hgg₂ : g ≠ g₂ := fun h => hgnp (h ▸ hg₂pos)
      have hgXr : g ∈ Xr.support := by
        rw [Finsupp.mem_support_iff, hXr, Finsupp.tsub_apply, Finsupp.tsub_apply,
          Finsupp.single_apply, if_neg (Ne.symm hgg₁), Finsupp.single_apply,
          if_neg (Ne.symm hgg₂), Nat.sub_zero, Nat.sub_zero]
        exact Finsupp.mem_support_iff.mp hg
      exact hg₃min_S g (Finset.mem_filter.mpr ⟨hgXr, hgnp⟩)
  have hprop := branchA_g3_aprop X Y hXY ha g₁ hg₁NP hg₁rank hmult1 hg₁min hpar g₃.rank hsurv
  -- Dispatch on the parity of `t = rank g₃`.
  cases hg₃type : g₃.type with
  | Positive => exact absurd hg₃type hg₃nepos
  | NonPolarized =>
    have hodd : Odd g₃.rank := rank_odd_of_nonpolarized_mem X.1.2 hg₃type hXg₃pos
    obtain ⟨nn, hnn⟩ : ∃ nn, g₃.rank = 2 * nn + 3 := by
      rcases hodd with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    have hmn : n' ≤ nn := by omega
    exact branchA_g3_assembly_type6 X Y hXY hsigeq n' nn hmn g₂ g₃ hg₂rank hg₂pos hnn hg₃type
      hXg₂pos hXg₃sub hne
      (fun j _ hj hoj => hprop j hoj (by rw [hnn]; exact hj))
      (fun j _ hj => Ywin_below_pl X Y hXY g₃ hXg₃pos (by rw [hnn]; omega))
  | Negative =>
    have heven : Even g₃.rank :=
      rank_even_of_polarized X.1.2 (by rw [hg₃type]; decide) hXg₃pos
    obtain ⟨nn, hnn⟩ : ∃ nn, g₃.rank = 2 * nn + 2 := by
      rcases heven with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    have hmn : n' ≤ nn := by omega
    exact branchA_g3_assembly_type7 X Y hXY hsigeq n' nn hmn g₂ g₃ hg₂rank hg₂pos hnn hg₃type
      hXg₂pos hXg₃sub hne
      (fun j _ hj hoj => hprop j hoj (by rw [hnn]; omega))
      (fun j _ hj => by
        rcases lt_or_eq_of_le hj with hlt | heq
        · exact Ywin_below_pl X Y hXY g₃ hXg₃pos (by rw [hnn]; omega)
        · subst heq
          exact branchA_g3_Ynonzero_top X Y hXY hcommon nn g₃ hnn hg₃type hXg₃pos)

/-- Branch A Case 2: the second gene `g₂` is polarized (§16 Case 2).  Dispatches on
`g₂`'s charge (`g⁺` direct / `g⁻` sign-dual) and, at `m'=0` (`m=1`), on `b₁` vs `d₁`. -/
lemma branchA_case2 (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 1) (hmult1 : X.1.1 g₁ = 1)
    (g₂ : Gene) (hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂)
    (hg₂min : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, g₂.rank ≤ g.rank)
    (hg₂pol : g₂.type ≠ .NonPolarized) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXg₂' : 0 < X.1.1 g₂ :=
    lt_of_lt_of_le hXg₂ (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
  have hg₂supp : g₂ ∈ X.1.1.support := Finsupp.mem_support_iff.mpr (by omega)
  have hg₂even : Even g₂.rank := rank_even_of_polarized X.1.2 hg₂pol hXg₂'
  have hge : 2 * m' + 1 ≤ g₂.rank := by rw [← hm']; exact hg₁min g₂ hg₂supp
  obtain ⟨n', hn'⟩ : ∃ n', g₂.rank = 2 * n' + 2 := by
    obtain ⟨k, hk⟩ := hg₂even; exact ⟨k - 1, by omega⟩
  have hmn : m' ≤ n' := by omega
  have hmin' : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank := fun g hg => hm' ▸ hg₁min g hg
  have h2nd' : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * n' + 2 ≤ g.rank :=
    fun g hg => hn' ▸ hg₂min g hg
  have hgap : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank :=
    rank_gap_one X Y hXY ha
  cases hch : g₂.type with
  | NonPolarized => exact absurd hch hg₂pol
  | Positive =>
    by_cases hm0 : m' = 0
    · subst hm0
      by_cases hb1 : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2
      · exact branchA_case2_full X Y hXY hcommon hsigeq hgap 0 n' hmn g₁ g₂ hm' hg₁NP hn' hch
          hmult1 hXg₁ hXg₂ hmin' h2nd' hb1
      · have hb1eq : (Sigma.sigma X.1.1 1).2 = (Sigma.sigma Y.1.1 1).2 :=
          le_antisymm (le_iff_dominates.mp hXY.le 1).2 (le_of_not_gt hb1)
        exact branchA_case2_g3 m X Y hXY hcommon hsigeq hXpn ha g₁ g₂ n' hg₁NP
          (by rw [hm']) hXg₁ hmult1 hch hn' hXg₂ hg₁min hg₂min hb1eq
    · exact branchA_case2_full X Y hXY hcommon hsigeq hgap m' n' hmn g₁ g₂ hm' hg₁NP hn' hch
        hmult1 hXg₁ hXg₂ hmin' h2nd' (branchA_case2_bm_lt X Y hXY ha m' (by omega) hmin')
  | Negative =>
    by_cases hm0 : m' = 0
    · subst hm0
      exact branchA_case2_full_neg X Y hXY hcommon hsigeq ha 0 n' hmn g₁ g₂ hm' hg₁NP hn' hch
        hmult1 hXg₁ hXg₂ hmin' h2nd' ha
    · exact branchA_case2_full_neg X Y hXY hcommon hsigeq ha m' n' hmn g₁ g₂ hm' hg₁NP hn' hch
        hmult1 hXg₁ hXg₂ hmin' h2nd' (branchA_case2_am_lt X Y hXY ha m' (by omega) hmin')

/-- Branch A, multiplicity-one sub-case (`X g₁ = 1`).  Extract `g₂` of minimal rank in
`X - g₁` and split on its polarization (§16 Cases 1–2); no second gene → vacuous edge. -/
lemma branchA_mult_one (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 1) (hmult1 : X.1.1 g₁ = 1) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hsupp : (X.1.1 - Finsupp.single g₁ 1).support.Nonempty
  · obtain ⟨g₂, hg₂mem, hg₂min⟩ := Finset.exists_min_image _ Gene.rank hsupp
    rw [Finsupp.mem_support_iff] at hg₂mem
    have hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := Nat.pos_of_ne_zero hg₂mem
    have hg₂ne : g₂ ≠ g₁ := by
      intro h; subst h
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl, hmult1] at hXg₂
      simp at hXg₂
    have hXg₂' : 0 < X.1.1 g₂ :=
      lt_of_lt_of_le hXg₂ (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
    have hg₂supp : g₂ ∈ X.1.1.support := Finsupp.mem_support_iff.mpr (by omega)
    by_cases hg₂pol : g₂.type = .NonPolarized
    · have hg₂odd : Odd g₂.rank := rank_odd_of_nonpolarized_mem X.1.2 hg₂pol hXg₂'
      have hge : 2 * m' + 1 ≤ g₂.rank := by rw [← hm']; exact hg₁min g₂ hg₂supp
      have hne_rank : g₂.rank ≠ 2 * m' + 1 := by
        intro heq
        exact hg₂ne (Gene.ext (by rw [heq, hm']) (hg₂pol.trans hg₁NP.symm))
      obtain ⟨n', hn'⟩ : ∃ n', g₂.rank = 2 * n' + 1 := by
        obtain ⟨k, hk⟩ := hg₂odd; exact ⟨k, by omega⟩
      have hmn : m' < n' := by omega
      rcases branchA_dichotomy X Y hXY hcommon hsigeq m' g₁ hg₁NP hm' hXg₁ with ha_m | hb_m
      · exact exists_mutation_le_caseA_branchA_case1_full X Y hXY hsigeq
          (rank_gap_one X Y hXY ha) m' n' hmn g₁ g₂ hm' hg₁NP hn' hg₂pol hXg₁ hXg₂
          (fun g hg => hm' ▸ hg₁min g hg) (fun g hg => hn' ▸ hg₂min g hg) ha_m
      · exact branchA_case1_neg m X Y hXY hsigeq ha g₁ hXg₁ hg₁min hg₁NP m' hm'
          g₂ n' hn' hg₂pol hmn hXg₂ (fun g hg => hn' ▸ hg₂min g hg) hb_m
    · exact branchA_case2 m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hg₁NP m' hm'
        hmult1 g₂ hXg₂ hg₂min hg₂pol
  · rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hsupp
    have hsingle : X.1.1 = Finsupp.single g₁ 1 := by
      ext g
      rcases eq_or_ne g g₁ with rfl | hgne
      · rw [Finsupp.single_apply, if_pos rfl, hmult1]
      · have hz : (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g = 0 := by rw [hsupp]; rfl
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (fun h => hgne h.symm),
          Nat.sub_zero] at hz
        rw [hz, Finsupp.single_apply, if_neg (fun h => hgne h.symm)]
    exact branchA_single_gene m X Y hXY hcommon g₁ hXg₁ hg₁NP m' hm' hmult1 hsingle

/-- **Branch A** of §16 Case A for `Mix (Pi, Lambda)`: minimal-rank gene `g₁`
nonpolarized (odd rank).  Dispatch on whether `X ⊇ 2g(m)`. -/
lemma exists_mutation_le_caseA_branchA (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨m', hm'⟩ : ∃ m', g₁.rank = 2 * m' + 1 := by
    have hodd : Odd g₁.rank := rank_odd_of_nonpolarized_mem X.1.2 hg₁NP hXg₁
    obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩
  by_cases hmult : 2 ≤ X.1.1 g₁
  · exact branchA_R2 X Y hXY hcommon hsigeq m' g₁ hg₁NP hm' hmult
  · exact branchA_mult_one m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hg₁NP m' hm'
      (by omega)

end MixPiLambda
