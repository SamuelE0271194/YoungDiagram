import YoungDiagram.Theorem6.MixLambdaPi.Case1
import YoungDiagram.Theorem6.MixLambdaPi.Case3
import YoungDiagram.Theorem6.MixLambdaPi.Drops
import YoungDiagram.Theorem6.MixLambdaPi.SigmaWindow
import YoungDiagram.Theorem6.MixLambdaPi.Propagation

/-!
# §16 Case A core for `Mix (Lambda, Pi)` (label 1).

This file dispatches the Case A core of §15.10 / §16 on the polarization of the
minimal-rank gene `g₁` of `X`, mirroring `Pi.exists_mutation_le_fifteen_ten_caseA`
in `YoungDiagram/Theorem6/Pi/CaseA.lean`.

Following §16 (Djoković), after the disjoint / sigma-agreement / polarized-pair
reductions (handled by the dispatcher in `MixVarietyJoint`), we let `g₁` be a gene
of minimal rank `m` in `X` and split:

* **Branch A** (`g₁ = g(m)` nonpolarized): paper Cases 1–2 (primitives type4–7);
* **Branch B** (`g₁ = g^±(m)` polarized): paper Cases 3–5 (primitives type6–8).

Each branch propagates a single strict level `a_m < c_m` / `b_m < d_m` across a
window using `cond_15_6/7_Mix_Lambda_Pi` (`Drops.lean`) and the window signature
identities in `SigmaWindow.lean`, half-integer increments handled as in
`half_le_sigma_diff_at_r`.  The two branches are the current formalization
targets.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixLambdaPi

/-- **Branch A** of §16 Case A: the minimal-rank gene `g₁` of `X` is nonpolarized
(`g₁ = g(m)`, so `m` is even).  Paper Cases 1–2. -/
lemma exists_mutation_le_caseA_branchA (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

/-- **Propagation core** of §16 Branch A Case 1.  From the strict start
`a_X(2m'+2) < a_Y(2m'+2)` (`ha_m`), the level-1 gap `ha`, and the fact that `X` has
no gene of rank strictly between `2m'+2` and `2n'+2` (`h2nd`, giving `X` a constant
sigma drop on the window), the §16 inequality chain
`c_i - c_{i+2} ≤ s_i - s_{i+1} ≤ s_0 - s_1 ≤ r_0 - r_1 - 1 = r_i - r_{i+1} = a_i - a_{i+2}`
propagates the strict *integer* inequality `a_X(j) + 1 ≤ a_Y(j)` to every even level
`j` in `[2m'+2, 2n'+2]`; and `Y` is nonzero throughout the window.  This is the hard,
reusable core; the assembly below consumes its two conclusions. -/
lemma exists_mutation_le_caseA_branchA_case1_propagate {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 2) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 2 ≤ g.rank)
    (ha_m : (Sigma.sigma X.1.1 (2 * m' + 2)).1 < (Sigma.sigma Y.1.1 (2 * m' + 2)).1) :
    (∀ j, 2 * m' + 2 ≤ j → j ≤ 2 * n' + 2 → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1) ∧
    (∀ j, 2 * m' + 2 ≤ j → j < 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0) := by
  refine ⟨?_, ?_⟩
  · -- Goal 1 (hprop_even): the §16 drop-chain telescoping (proved in Propagation.lean).
    exact branchA_case1_hprop_even X Y hXY ha m' n' hmn gm gk hgm_rank hgm_np hgk_rank hgk_np
      hXgm hXgk hne hmin h2nd ha_m
  · -- Goal 2 (hYwin): Y is nonzero on the window since X has gene gk of rank
    -- 2n'+2 > j, so prime^[j] X ≠ 0, and Y dominates X.
    intro j _ hj2
    have hXgk0 : 0 < X.1.1 gk :=
      lt_of_lt_of_le hXgk (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
    have hgk_supp : gk ∈ X.1.1.support :=
      Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hXgk0)
    have hXj : Chromosome.prime^[j] X.1.1 ≠ 0 := by
      intro hzero
      have hle := (prime_iterate_eq_zero_rank_le).mpr hzero gk hgk_supp
      rw [hgk_rank] at hle
      omega
    intro hYzero
    have hsig_le : signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
    rw [hYzero, map_zero] at hsig_le
    exact hXj (signature_eq_zero (le_antisymm hsig_le (signature_nonneg _)))

/-- **Assembly** of §16 Branch A Case 1, given the propagation outputs
(`hprop_even`, `hYwin`).  Builds the `type4` step `g(m)+g(k) → g⁻(m-1)+g⁺(k+1)`
(ε = `.Negative`) and proves `Z ≤ Y` over the window via
`sigma_type4_eq_before/_eq_after/_mid`: outside the window the source/target
signatures agree (reduce to `hXY`); inside, the even-level difference `(1,0)` is
absorbed by `hprop_even` and the odd-level difference `(1/2,1/2)` by
`half_le_sigma_diff_at_r` (its `≠` hypothesis from `hsigeq` + `hYwin`).  Template:
`MixLambdaPi.exists_mutation_le_disjoint_pair` in `Case3.lean`. -/
lemma exists_mutation_le_caseA_branchA_case1 {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 2) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hprop_even : ∀ j, 2 * m' + 2 ≤ j → j ≤ 2 * n' + 2 → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hYwin : ∀ j, 2 * m' + 2 ≤ j → j < 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hsigeq
  have hε : GeneType.Negative ≠ .NonPolarized := by decide
  let Y4' : Mix (Lambda, Pi) := Y4 hmn hε
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * m' + 2) .NonPolarized = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm)
    rw [hgm_rank, hgm_np] at h
    exact h
  have hgk_eq : Gene.ofRank (2 * n' + 2) .NonPolarized = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk)
    rw [hgk_rank, hgk_np] at h
    exact h
  have hX4_val : (X4 hmn).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X4_eq, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X4 hmn).1 + restval = X.1.1 := by
    rw [hX4_val]
    exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Lambda, Pi) := ⟨Y4'.1 + restval, add_mem Y4'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X4 hmn : Mix (Lambda, Pi)) + rest_M = X.1) ▸
    MixLambdaPi.Step.mk (X4 hmn) Y4' rest_M
      (MixLambdaPi.Primitive.type4 GeneType.Negative hε hmn), ?_⟩
  change Y4'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X4 hmn).1) + signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) :=
    le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * m' + 1
  · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
        signature (Chromosome.prime^[j] (X4 hmn).1) :=
      (sigma_type4_eq_before hmn hε (hj := hj)).symm
    rw [hY4X4, ← hdecomp]
    exact hXYj
  · have h_not_before : 2 * m' + 1 < j := by omega
    by_cases hj_after : 2 * n' + 3 ≤ j
    · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
          signature (Chromosome.prime^[j] (X4 hmn).1) :=
        (sigma_type4_eq_after hmn hε (hj := hj_after)).symm
      rw [hY4X4, ← hdecomp]
      exact hXYj
    · have h_mid : j < 2 * n' + 3 := by omega
      have hmid := sigma_type4_mid hmn hε h_not_before h_mid
      have hY4_eq : signature (Chromosome.prime^[j] Y4'.1) =
          signature (Chromosome.prime^[j] (X4 hmn).1) +
            (if Even (2 * n' + 2 - j) then signature (Gene.ofRank 1 (-GeneType.Negative))
             else ((1 : ℚ) / 2, (1 : ℚ) / 2)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY4_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * n' + 2 - j)
      · rw [if_pos hpar]
        have h_even_j : Even j := by
          have hp : (2 * n' + 2 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.even_iff]; omega
        have h_sig_pos : signature (Gene.ofRank 1 (-GeneType.Negative)) = ((1 : ℚ), (0 : ℚ)) := by
          rw [GeneType.neg_negative, signature_ofRank_one_positive]
        rw [h_sig_pos]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1 := by
          have h_sigma := hprop_even j (by omega) (by omega) h_even_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · show (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          exact h_sigXj
        · show (signature (Chromosome.prime^[j] X.1.1)).2 + 0 ≤
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

/-- **Branch B** of §16 Case A: the minimal-rank gene `g₁` of `X` is polarized
(`g₁ = g^±(m)`, so `m` is odd).  Paper Cases 3–5. -/
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
  sorry

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
