import YoungDiagram.Theorem6.Case4A
import YoungDiagram.Theorem6.Case4B.Common

open Variety hiding prime prime_def
open Chromosome Sigma

/-!
Case 4b, even rank-gap and even lower rank.

The proof currently remains as the unfinished window estimate inherited from the
original Case A block. The common type-2 mutation construction is factored out in
`Case4B.Common`.
-/

set_option linter.unusedVariables false in
lemma exists_mutation_le_case4b_evenGap_evenRank
    {n : ℕ} (X Y : nPi n) (hXY : X.1 < Y.1)
    {g₁ g₂ : Gene}
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (ha : (sigma X.1 1).1 < (sigma Y.1 1).1)
    (hε₁ : ¬ g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Negative)
    (hXg₁ : X.1.val g₁ ≠ 0)
    (hXg₁pos : 0 < X.1.val g₁)
    (hg₁min : ∀ g ∈ X.1.val.support, g₁.rank ≤ g.rank)
    (hg₁_ge2 : 2 ≤ g₁.rank)
    (hg₁_one : X.1.val g₁ = 1)
    (hg₂pos : 0 < X.1.val g₂)
    (hg₂rank : g₁.rank < g₂.rank)
    (hg₂min : ∀ g' : Gene, 0 < X.1.val g' → g₁.rank < g'.rank → g₂.rank ≤ g'.rank)
    (hε₂ : ¬ g₂.type = -g₁.type)
    (hparity : Even (g₂.rank - g₁.rank))
    (h_g1_rank_even : Even g₁.rank) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 :=
  exists_mutation_le_case4b_evenGap_of_sigma_window X Y hXg₁ hg₁_ge2 hg₁_one
    hg₂pos hg₂rank hε₂ <| by
      intro hε hle hm j
      have hXYj : sigma X.1.val j ≤ sigma Y.1.val j :=
        le_iff_dominates.mp hXY.le j
      obtain ⟨hcase1, hcase2, hcase3⟩ :=
        sigma_type2_mn_rank g₁.type hε hg₂rank hm
      by_cases hjl : j ≤ g₁.rank - 2
      · rw [← hcase1 j hjl]
        exact ⟨by simp only [Prod.fst_add]; linarith [hXYj.1],
                by simp only [Prod.snd_add]; linarith [hXYj.2]⟩
      · by_cases hjr : g₂.rank + 2 ≤ j
        · rw [← hcase2 j hjr]
          exact ⟨by simp only [Prod.fst_add]; linarith [hXYj.1],
                  by simp only [Prod.snd_add]; linarith [hXYj.2]⟩
        · -- Middle window: `g₁.rank - 1 ≤ j ≤ g₂.rank + 1`.
          push Not at hjl hjr
          have hjl' : g₁.rank - 1 ≤ j := by omega
          have hjr' : j ≤ g₂.rank + 1 := by omega
          have hdelta := hcase3 j hjl' hjr'
          have hε_neg : g₁.type = GeneType.Negative := by
            have hnodd : ¬Even ((g₁.rank : ℤ) - 1) := by
              obtain ⟨k, hk⟩ := h_g1_rank_even
              intro ⟨m, hm⟩
              omega
            simp only [GeneType.negOnePow_smul, if_neg hnodd,
                       GeneType.neg_negative] at hε₁
            match h : g₁.type with
            | .Positive => exact absurd h hε₁
            | .Negative => rfl
            | .NonPolarized =>
              exact absurd h hε
          have haj_lt_cj : ∀ j, g₁.rank - 1 ≤ j → j ≤ g₂.rank →
              (sigma X.1.val j).1 < (sigma Y.1.val j).1 := by
            have ham1_lt_cm1 :
                (sigma X.1.val (g₁.rank - 1)).1 <
                (sigma Y.1.val (g₁.rank - 1)).1 := by
              have hc1_ci_rank1 :
                  (sigma Y.1 1).1 - (sigma Y.1 (g₁.rank - 1)).1 ≤
                  (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 2)).2 :=
                Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
              have hd0_di_rank1 :
                  (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 2)).2 ≤
                  (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 2)).2 := by
                have hb0_eq_d0 : (sigma X.1 0).2 = (sigma Y.1 0).2 :=
                  sigma_zero_snd_eq X Y hXY.le
                have hbm2_le_dm2 :
                    (sigma X.1 (g₁.rank - 2)).2 ≤
                    (sigma Y.1 (g₁.rank - 2)).2 :=
                  (le_iff_dominates.mp hXY.le (g₁.rank - 2)).2
                linarith
              have hb0_bi_rank1 :
                  (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 2)).2 =
                  (sigma X.1 1).1 - (sigma X.1 (g₁.rank - 1)).1 := by
                have h : (sigma X.1 0).2 -
                    (sigma X.1 (g₁.rank - 1 - 1)).2 =
                    (sigma X.1 1).1 -
                    (sigma X.1 (g₁.rank - 1)).1 :=
                  x_actual_negative_prefix_equalities
                    (fun g' _ hg'_pos =>
                      hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                    (by omega) (by omega)
                simpa [show g₁.rank - 1 - 1 = g₁.rank - 2 from by omega] using h
              have hstrict :
                  (sigma Y.1 0).1 - (sigma Y.1 1).1 <
                  (sigma X.1 0).1 - (sigma X.1 1).1 := by
                have ha0_eq : (sigma X.1 0).1 = (sigma Y.1 0).1 :=
                  sigma_zero_fst_eq X Y hXY.le
                linarith
              have ha0_eq : (sigma X.1 0).1 = (sigma Y.1 0).1 :=
                sigma_zero_fst_eq X Y hXY.le
              linarith [hc1_ci_rank1, hd0_di_rank1, hb0_bi_rank1, hstrict]
            have ham_lt_cm :
                (sigma X.1.val g₁.rank).1 <
                (sigma Y.1.val g₁.rank).1 := by
              have hc1_ci_rank :
                  (sigma Y.1 1).1 - (sigma Y.1 g₁.rank).1 ≤
                  (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 1)).2 :=
                Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
              have hd0_di_rank :
                  (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 1)).2 ≤
                  (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 1)).2 := by
                have hb0_eq_d0 : (sigma X.1 0).2 = (sigma Y.1 0).2 :=
                  sigma_zero_snd_eq X Y hXY.le
                have hbm1_le_dm1 :
                    (sigma X.1 (g₁.rank - 1)).2 ≤
                    (sigma Y.1 (g₁.rank - 1)).2 :=
                  (le_iff_dominates.mp hXY.le (g₁.rank - 1)).2
                linarith
              have hb0_bi_rank :
                  (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 1)).2 =
                  (sigma X.1 1).1 - (sigma X.1 g₁.rank).1 :=
                x_actual_negative_prefix_equalities
                  (fun g' _ hg'_pos =>
                    hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                  (by omega) (le_refl g₁.rank)
              have hstrict :
                  (sigma Y.1 0).1 - (sigma Y.1 1).1 <
                  (sigma X.1 0).1 - (sigma X.1 1).1 := by
                have ha0_eq : (sigma X.1 0).1 = (sigma Y.1 0).1 :=
                  sigma_zero_fst_eq X Y hXY.le
                linarith
              have ha0_eq : (sigma X.1 0).1 = (sigma Y.1 0).1 :=
                sigma_zero_fst_eq X Y hXY.le
              linarith [hc1_ci_rank, hd0_di_rank, hb0_bi_rank, hstrict]
            have hfst_diff_le : ∀ i, g₁.rank ≤ i → i ≤ g₂.rank - 1 →
                (sigma Y.1.val i).1 - (sigma Y.1.val (i + 1)).1 ≤
                (sigma X.1.val i).1 - (sigma X.1.val (i + 1)).1 := by
              intro i hi1 hi2
              by_cases hi_even : Even i
              · have hci_le_c0 :
                    (sigma Y.1.val i).1 - (sigma Y.1.val (i + 1)).1 ≤
                    (sigma Y.1.val 0).1 - (sigma Y.1.val 1).1 := by
                  have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val i Y.1.2
                  simp only [if_pos hi_even] at h
                  exact h
                have hc0_le_a0 :
                    (sigma Y.1.val 0).1 - (sigma Y.1.val 1).1 ≤
                    (sigma X.1.val 0).1 - (sigma X.1.val 1).1 - 1 := by
                  obtain ⟨nX1, hnX1⟩ := sigma_isNat X.1.val 1 X.1.2
                  obtain ⟨nY1, hnY1⟩ := sigma_isNat Y.1.val 1 Y.1.2
                  have ha0_eq : (sigma X.1.val 0).1 = (sigma Y.1.val 0).1 :=
                    sigma_zero_fst_eq X Y hXY.le
                  have hX1 : (sigma X.1.val 1).1 = ↑nX1.1 :=
                    congr_arg Prod.fst hnX1
                  have hY1 : (sigma Y.1.val 1).1 = ↑nY1.1 :=
                    congr_arg Prod.fst hnY1
                  have hlt1 : (nX1.1 : ℚ) + 1 ≤ nY1.1 := by
                    have h : (sigma X.1.val 1).1 < (sigma Y.1.val 1).1 := ha
                    rw [hX1, hY1] at h
                    exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp h)
                  rw [← ha0_eq, hX1, hY1]
                  linarith
                have ha0_eq_am :
                    (sigma X.1.val 0).1 - (sigma X.1.val 1).1 - 1 =
                    (sigma X.1.val g₁.rank).1 -
                      (sigma X.1.val (g₁.rank + 1)).1 := by
                  have hLHS : (sigma X.1.val 0).1 - (sigma X.1.val 1).1 =
                      ∑ g ∈ X.1.val.support.filter (fun g =>
                        0 < g.rank ∧
                        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                      (X.1.val g : ℚ) := by
                    rw [sigma_fst_diff X.1.val 0 X.1.2,
                        Sigma.prime_iterate_sum_pos_eq X.1.val 0 ⟨0, rfl⟩]
                  have hRHS : (sigma X.1.val g₁.rank).1 -
                      (sigma X.1.val (g₁.rank + 1)).1 =
                      ∑ g ∈ X.1.val.support.filter (fun g =>
                        g₁.rank < g.rank ∧
                        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                      (X.1.val g : ℚ) := by
                    rw [sigma_fst_diff X.1.val g₁.rank X.1.2,
                        Sigma.prime_iterate_sum_pos_eq X.1.val g₁.rank h_g1_rank_even]
                  have hg₁_posfam :
                      g₁.type = Int.negOnePow
                        ((g₁.rank : ℤ) - 1) • GeneType.Positive := by
                    have h1 : Int.negOnePow ((g₁.rank : ℤ) - 1) • GeneType.Positive =
                        GeneType.Negative := by
                      have h := Sigma.altType_even g₁.rank h_g1_rank_even
                        GeneType.Positive
                      simp only [Sigma.altType, GeneType.neg_positive] at h
                      exact h
                    rw [h1]
                    exact hε_neg
                  have hfilter_split :
                      X.1.val.support.filter (fun g =>
                        0 < g.rank ∧
                        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive) =
                      {g₁} ∪ X.1.val.support.filter (fun g =>
                        g₁.rank < g.rank ∧
                        g.type = Int.negOnePow
                          ((g.rank : ℤ) - 1) • GeneType.Positive) := by
                    ext g
                    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
                               Finsupp.mem_support_iff]
                    constructor
                    · rintro ⟨hsupp, _, htype⟩
                      by_cases heq : g = g₁
                      · left
                        exact heq
                      · right
                        refine ⟨hsupp, ?_, htype⟩
                        have hge := hg₁min g (Finsupp.mem_support_iff.mpr hsupp)
                        rcases Nat.lt_or_eq_of_le hge with h | h
                        · exact h
                        · exfalso
                          apply heq
                          exact Gene.ext h.symm
                            (by rw [← h, ← hg₁_posfam] at htype; exact htype)
                    · rintro (rfl | ⟨hsupp, hrank', htype⟩)
                      · exact ⟨by rw [hg₁_one]; exact one_ne_zero,
                                by omega, hg₁_posfam⟩
                      · exact ⟨hsupp, by omega, htype⟩
                  have hdisjoint : Disjoint {g₁} (X.1.val.support.filter (fun g =>
                      g₁.rank < g.rank ∧
                      g.type = Int.negOnePow
                        ((g.rank : ℤ) - 1) • GeneType.Positive)) := by
                    simp only [Finset.disjoint_left,
                               Finset.mem_singleton,
                               Finset.mem_filter]
                    rintro g rfl ⟨_, hlt, _⟩
                    exact absurd hlt (lt_irrefl _)
                  have hsum :
                      ∑ g ∈ X.1.val.support.filter (fun g =>
                        0 < g.rank ∧
                        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                      (X.1.val g : ℚ) =
                      1 + ∑ g ∈ X.1.val.support.filter (fun g =>
                        g₁.rank < g.rank ∧
                        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                      (X.1.val g : ℚ) := by
                    rw [hfilter_split, Finset.sum_union hdisjoint, Finset.sum_singleton,
                        show (X.1.val g₁ : ℚ) = 1 from by exact_mod_cast hg₁_one]
                  linarith [hLHS, hRHS, hsum]
                have ham_eq_ai :
                    (sigma X.1.val g₁.rank).1 -
                      (sigma X.1.val (g₁.rank + 1)).1 =
                    (sigma X.1.val i).1 -
                      (sigma X.1.val (i + 1)).1 := by
                  have hLHS : (sigma X.1.val g₁.rank).1 -
                      (sigma X.1.val (g₁.rank + 1)).1 =
                      ∑ g ∈ X.1.val.support.filter (fun g =>
                        g₁.rank < g.rank ∧
                        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                      (X.1.val g : ℚ) := by
                    rw [sigma_fst_diff X.1.val g₁.rank X.1.2,
                        Sigma.prime_iterate_sum_pos_eq X.1.val g₁.rank h_g1_rank_even]
                  have hRHS : (sigma X.1.val i).1 -
                      (sigma X.1.val (i + 1)).1 =
                      ∑ g ∈ X.1.val.support.filter (fun g =>
                        i < g.rank ∧
                        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                      (X.1.val g : ℚ) := by
                    rw [sigma_fst_diff X.1.val i X.1.2,
                        Sigma.prime_iterate_sum_pos_eq X.1.val i hi_even]
                  have hfilter_eq :
                      X.1.val.support.filter (fun g =>
                        g₁.rank < g.rank ∧
                        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive) =
                      X.1.val.support.filter (fun g =>
                        i < g.rank ∧
                        g.type = Int.negOnePow
                          ((g.rank : ℤ) - 1) • GeneType.Positive) := by
                    ext g
                    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                    constructor
                    · rintro ⟨hg_supp, hg_rank, hg_type⟩
                      exact ⟨hg_supp,
                        by have := hg₂min g (Nat.pos_of_ne_zero hg_supp) hg_rank; omega,
                        hg_type⟩
                    · rintro ⟨hg_supp, hg_rank, hg_type⟩
                      exact ⟨hg_supp, by omega, hg_type⟩
                  rw [hLHS, hRHS, hfilter_eq]
                linarith
              · have hci_le_c1 :
                    (sigma Y.1.val i).1 - (sigma Y.1.val (i + 1)).1 ≤
                    (sigma Y.1.val 1).1 - (sigma Y.1.val 2).1 := by
                  have hi_pos : 1 ≤ i := by omega
                  have hi_pred_even : Even (i - 1) := by
                    simp only [Nat.even_iff] at *
                    omega
                  have sigma_shift : ∀ k, sigma Y.1.val.prime k =
                      sigma Y.1.val (k + 1) := fun k => by
                    change signature (prime^[k] Y.1.val.prime) =
                        signature (prime^[k + 1] Y.1.val)
                    rw [Function.iterate_succ_apply]
                  have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val.prime (i - 1)
                    (Variety.prime_mem_Pi Y.1.2)
                  simp only [if_pos hi_pred_even] at h
                  simp only [sigma_shift] at h
                  simp only [Nat.sub_add_cancel hi_pos] at h
                  exact h
                have hc1_le_d0 :
                    (sigma Y.1.val 1).1 - (sigma Y.1.val 2).1 ≤
                    (sigma Y.1.val 0).2 - (sigma Y.1.val 1).2 :=
                  Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                have hd0_le_b0 :
                    (sigma Y.1.val 0).2 - (sigma Y.1.val 1).2 ≤
                    (sigma X.1.val 0).2 - (sigma X.1.val 1).2 := by
                  have hb0_eq_d0 : (sigma X.1 0).2 = (sigma Y.1 0).2 :=
                    sigma_zero_snd_eq X Y hXY.le
                  have hb1_le_d1 : (sigma X.1 1).2 ≤ (sigma Y.1 1).2 :=
                    (le_iff_dominates.mp hXY.le 1).2
                  linarith
                have hb0_eq_ai :
                    (sigma X.1.val 0).2 -
                      (sigma X.1.val 1).2 =
                    (sigma X.1.val i).1 -
                      (sigma X.1.val (i + 1)).1 := by
                  have hLHS : (sigma X.1.val 0).2 -
                      (sigma X.1.val 1).2 =
                      ∑ g ∈ X.1.val.support.filter (fun g =>
                        0 < g.rank ∧
                        g.type = Sigma.altType g.rank GeneType.Negative),
                      (X.1.val g : ℚ) := by
                    have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
                    have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
                    simp only [Function.iterate_zero, id] at h1 h2
                    exact h1.trans h2
                  have hRHS : (sigma X.1.val i).1 -
                      (sigma X.1.val (i + 1)).1 =
                      ∑ g ∈ X.1.val.support.filter (fun g =>
                        i < g.rank ∧
                        g.type = Sigma.altType g.rank GeneType.Negative),
                      (X.1.val g : ℚ) := by
                    have hkodd : Int.negOnePow (i : ℤ) = -1 :=
                      Int.negOnePow_odd _
                        (by exact_mod_cast Nat.not_even_iff_odd.mp hi_even)
                    have h1 := Sigma.sigma_fst_diff X.1.val i X.1.2
                    have h2 := Sigma.prime_iterate_sum_eq X.1.val i GeneType.Positive
                    simp only [hkodd, GeneType.neg_one_smul,
                               GeneType.neg_positive] at h2
                    exact h1.trans h2
                  have hfilter_eq :
                      X.1.val.support.filter (fun g =>
                        0 < g.rank ∧
                        g.type = Sigma.altType g.rank GeneType.Negative) =
                      X.1.val.support.filter (fun g =>
                        i < g.rank ∧
                        g.type = Sigma.altType g.rank GeneType.Negative) :=
                    support_filter_negative_eq_tail_of_even
                      hXpn hXg₁pos hg₁min hg₂min h_g1_rank_even hε_neg hi2
                  rw [hLHS, hRHS, hfilter_eq]
                linarith
            intro j hjl hjr
            rcases Nat.eq_or_lt_of_le hjl with rfl | hjl'
            · exact ham1_lt_cm1
            · have hjl'' : g₁.rank ≤ j := by omega
              obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjl''
              revert hjr
              induction d with
              | zero =>
                intro _
                simpa using ham_lt_cm
              | succ k ihk =>
                intro hjr
                have hprev := ihk (by omega) (by omega) (by omega) (by omega)
                have hdiff := hfst_diff_le (g₁.rank + k) (by omega) (by omega)
                obtain ⟨nX_k, hnX_k⟩ :=
                  sigma_isNat X.1.val (g₁.rank + k) X.1.2
                obtain ⟨nY_k, hnY_k⟩ :=
                  sigma_isNat Y.1.val (g₁.rank + k) Y.1.2
                obtain ⟨nX_s, hnX_s⟩ :=
                  sigma_isNat X.1.val (g₁.rank + k + 1) X.1.2
                obtain ⟨nY_s, hnY_s⟩ :=
                  sigma_isNat Y.1.val (g₁.rank + k + 1) Y.1.2
                rw [hnX_k, hnY_k] at hprev hdiff
                rw [hnX_s, hnY_s] at hdiff
                have hks : g₁.rank + Nat.succ k = g₁.rank + k + 1 := by omega
                rw [hks, hnX_s, hnY_s]
                have h1 : (↑nX_k.1 : ℚ) + 1 ≤ ↑nY_k.1 := by
                  exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp hprev)
                linarith
          have hbj_lt_dj : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank + 1 →
              (sigma X.1.val j).2 < (sigma Y.1.val j).2 := by
            have hbm_lt_dm :
                (sigma X.1.val g₁.rank).2 <
                (sigma Y.1.val g₁.rank).2 := by
              have hstrict :
                  (sigma Y.1 0).1 - (sigma Y.1 1).1 <
                  (sigma X.1 0).1 - (sigma X.1 1).1 := by
                linarith [sigma_zero_fst_eq X Y hXY.le]
              have hb1_le_d1 : (sigma X.1 1).2 ≤ (sigma Y.1 1).2 :=
                (le_iff_dominates.mp hXY.le 1).2
              have hb12_eq :
                  (sigma X.1 1).2 - (sigma X.1 2).2 =
                  (sigma X.1 0).1 - (sigma X.1 1).1 := by
                have h := x_side_equalities
                  (fun g' _ hg'_pos =>
                    hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                  (show 1 < g₁.rank from hg₁_ge2)
                simp only [show ¬Even 1 from by norm_num, ↓reduceIte] at h
                exact h
              have hd12_le :
                  (sigma Y.1 1).2 - (sigma Y.1 2).2 ≤
                  (sigma Y.1 0).1 - (sigma Y.1 1).1 := by
                have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (2 - 1) Y.1.2
                simp only [show ¬Even (2 - 1 : ℕ) from by norm_num, if_false] at h
                exact h
              have hd2_gt_b2 : (sigma X.1 2).2 < (sigma Y.1 2).2 := by
                linarith
              have no_neg_gene_rank_g : ∀ g' ∈ X.1.val.support,
                  g'.rank = g₁.rank → g'.type = .Negative := by
                intro g' hg'_supp hg'_rank
                have hg'_ne_np :=
                  IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
                have hg'_ne_pos : g'.type ≠ .Positive := fun hg'_pos => hXpn
                  ⟨g', g₁, hg'_rank, hg'_pos, hε_neg,
                   Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp),
                   hXg₁pos⟩
                cases ht' : g'.type with
                | Positive => exact absurd ht' hg'_ne_pos
                | Negative => rfl
                | NonPolarized => exact absurd ht' hg'_ne_np
              have hc1_ci_rank1 :
                  (sigma Y.1 1).1 - (sigma Y.1 (g₁.rank - 1)).1 ≤
                  (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 2)).2 :=
                Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
              have hb0_b2_rank1 :
                  (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 2)).2 =
                  (sigma X.1 2).2 - (sigma X.1 g₁.rank).2 := by
                have h := Sigma.b0_eq_b2_negative g₁.rank hg₁_ge2 hg₁min
                  no_neg_gene_rank_g
                  (show g₁.rank - 2 ≤ g₁.rank - 1 from by omega)
                simp only [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h
                exact h
              have hd0_di_rank1 :
                  (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 2)).2 ≤
                  (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 2)).2 :=
                theorem6_snd_gap_le_of_dominates X Y hXY.le
              have hd2_c1_rank1 :
                  (sigma Y.1 2).2 - (sigma Y.1 g₁.rank).2 ≤
                  (sigma Y.1 1).1 - (sigma Y.1 (g₁.rank - 1)).1 := by
                by_cases hrank2 : g₁.rank = 2
                · simp only [hrank2, sub_self, le_refl]
                · have h : g₁.rank - 1 ≥ 2 := by omega
                  have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
                  rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
              have hd2_di1_rank1 :
                  (sigma Y.1 2).2 - (sigma Y.1 g₁.rank).2 ≤
                  (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 2)).2 :=
                hd2_c1_rank1.trans hc1_ci_rank1
              linarith [hd2_di1_rank1, hd0_di_rank1, hb0_b2_rank1, hd2_gt_b2]
            have hbm1_lt_dm1 : g₁.rank > 2 →
                (sigma X.1.val (g₁.rank - 1)).2 <
                (sigma Y.1.val (g₁.rank - 1)).2 := by
              intro hgt
              have hge4 : g₁.rank ≥ 4 := by
                obtain ⟨k, hk⟩ := h_g1_rank_even
                omega
              have hstrict :
                  (sigma Y.1 0).1 - (sigma Y.1 1).1 <
                  (sigma X.1 0).1 - (sigma X.1 1).1 := by
                linarith [sigma_zero_fst_eq X Y hXY.le]
              have hb1_le_d1 : (sigma X.1 1).2 ≤ (sigma Y.1 1).2 :=
                (le_iff_dominates.mp hXY.le 1).2
              have hb12_eq :
                  (sigma X.1 1).2 - (sigma X.1 2).2 =
                  (sigma X.1 0).1 - (sigma X.1 1).1 := by
                have h := x_side_equalities
                  (fun g' _ hg'_pos =>
                    hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                  (show 1 < g₁.rank from hg₁_ge2)
                simp only [show ¬Even 1 from by norm_num, ↓reduceIte] at h
                exact h
              have hd12_le :
                  (sigma Y.1 1).2 - (sigma Y.1 2).2 ≤
                  (sigma Y.1 0).1 - (sigma Y.1 1).1 := by
                have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (2 - 1) Y.1.2
                simp only [show ¬Even (2 - 1 : ℕ) from by norm_num, if_false] at h
                exact h
              have hd2_gt_b2 : (sigma X.1 2).2 < (sigma Y.1 2).2 := by
                linarith
              have no_neg_gene_rank_g : ∀ g' ∈ X.1.val.support,
                  g'.rank = g₁.rank → g'.type = .Negative := by
                intro g' hg'_supp hg'_rank
                have hg'_ne_np :=
                  IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
                have hg'_ne_pos : g'.type ≠ .Positive := fun hg'_pos => hXpn
                  ⟨g', g₁, hg'_rank, hg'_pos, hε_neg,
                   Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp),
                   hXg₁pos⟩
                cases ht' : g'.type with
                | Positive => exact absurd ht' hg'_ne_pos
                | Negative => rfl
                | NonPolarized => exact absurd ht' hg'_ne_np
              have hd2_c1_rank_m1 :
                  (sigma Y.1 2).2 - (sigma Y.1 (g₁.rank - 1)).2 ≤
                  (sigma Y.1 1).1 - (sigma Y.1 (g₁.rank - 2)).1 := by
                have h := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2
                  (show g₁.rank - 2 ≥ 2 from by omega)
                rwa [show g₁.rank - 2 + 1 = g₁.rank - 1 from by omega] at h
              have hc1_ci_rank_m1 :
                  (sigma Y.1 1).1 - (sigma Y.1 (g₁.rank - 2)).1 ≤
                  (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 3)).2 := by
                have h := Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2
                  (show g₁.rank - 2 ≥ 1 from by omega)
                simp only [show g₁.rank - 2 - 1 = g₁.rank - 3 from by omega] at h
                exact h
              have hd0_di_rank_m1 :
                  (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 3)).2 ≤
                  (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 3)).2 :=
                theorem6_snd_gap_le_of_dominates X Y hXY.le
              have hb0_b2_rank_m1 :
                  (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 3)).2 =
                  (sigma X.1 2).2 - (sigma X.1 (g₁.rank - 1)).2 := by
                have h := Sigma.b0_eq_b2_negative g₁.rank hg₁_ge2 hg₁min
                  no_neg_gene_rank_g
                  (show g₁.rank - 3 ≤ g₁.rank - 1 from by omega)
                simp only [show g₁.rank - 3 + 2 = g₁.rank - 1 from by omega] at h
                exact h
              linarith [hd2_c1_rank_m1, hc1_ci_rank_m1,
                        hd0_di_rank_m1, hb0_b2_rank_m1, hd2_gt_b2]
            have hdi_sub_le_bi_sub : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank →
                  (sigma Y.1.val j).2 - (sigma Y.1.val (j + 1)).2 ≤
                  (sigma X.1.val j).2 - (sigma X.1.val (j + 1)).2 := by
                sorry
            intro j hj1 hj2
            obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj1
            induction d with
            | zero =>
              simpa using hbm_lt_dm
            | succ d ih =>
              have ihd := ih (by omega) (by omega)
              have hstep :=
                hdi_sub_le_bi_sub (g₁.rank + d) (by omega) (by omega)
              obtain ⟨nX_d, hnX_d⟩ :=
                sigma_isNat X.1.val (g₁.rank + d) X.1.2
              obtain ⟨nY_d, hnY_d⟩ :=
                sigma_isNat Y.1.val (g₁.rank + d) Y.1.2
              obtain ⟨nX_s, hnX_s⟩ :=
                sigma_isNat X.1.val (g₁.rank + d + 1) X.1.2
              obtain ⟨nY_s, hnY_s⟩ :=
                sigma_isNat Y.1.val (g₁.rank + d + 1) Y.1.2
              rw [hnX_d, hnY_d] at ihd hstep
              rw [hnX_s, hnY_s] at hstep
              have hks : g₁.rank + Nat.succ d = g₁.rank + d + 1 := by omega
              rw [hks, hnX_s, hnY_s]
              have h1 : (↑nX_d.2 : ℚ) + 1 ≤ ↑nY_d.2 := by
                exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp ihd)
              linarith
          have hε_ne_pos : g₁.type ≠ .Positive := hε_neg ▸ by decide
          simp only [if_neg hε_ne_pos] at hdelta
          obtain ⟨nX, hnX⟩ := sigma_isNat X.1.val j X.1.2
          obtain ⟨nY, hnY⟩ := sigma_isNat Y.1.val j Y.1.2
          rw [hnX, hnY] at hXYj
          rcases (show j = g₁.rank - 1 ∨
                       (g₁.rank ≤ j ∧ j ≤ g₂.rank) ∨
                       j = g₂.rank + 1 from by omega)
              with hjbd | ⟨hjl2, hjr2⟩ | hjbd2
          · -- Left boundary: delta = `(1, 0)`.
            rw [if_neg (by omega : ¬((j > g₁.rank - 1) ∧ (j < g₂.rank + 1))),
                if_pos hjbd] at hdelta
            have haj := haj_lt_cj j (by omega) (by omega)
            rw [hnX, hnY] at haj
            have hd1 : (sigma (Pi.Y2 hε hle hm).val j).1 -
                       (sigma (Pi.X2 hε hle hm).val j).1 = 1 :=
              congr_arg Prod.fst hdelta
            have hd2 : (sigma (Pi.Y2 hε hle hm).val j).2 -
                       (sigma (Pi.X2 hε hle hm).val j).2 = 0 :=
              congr_arg Prod.snd hdelta
            have ha1 : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 :=
              by exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp haj)
            exact ⟨by simp only [Prod.fst_add, hnX, hnY]; linarith,
                   by simp only [Prod.snd_add, hnX, hnY]; linarith [hXYj.2]⟩
          · -- Interior: delta = `(1, 1)`.
            rw [if_pos (show (j > g₁.rank - 1) ∧ (j < g₂.rank + 1)
                        from ⟨by omega, by omega⟩)] at hdelta
            have haj := haj_lt_cj j (by omega) hjr2
            have hbj := hbj_lt_dj j hjl2 (by omega)
            rw [hnX, hnY] at haj hbj
            have hd1 : (sigma (Pi.Y2 hε hle hm).val j).1 -
                       (sigma (Pi.X2 hε hle hm).val j).1 = 1 :=
              congr_arg Prod.fst hdelta
            have hd2 : (sigma (Pi.Y2 hε hle hm).val j).2 -
                       (sigma (Pi.X2 hε hle hm).val j).2 = 1 :=
              congr_arg Prod.snd hdelta
            have ha1 : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 :=
              by exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp haj)
            have hb1 : (↑nX.2 : ℚ) + 1 ≤ ↑nY.2 :=
              by exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp hbj)
            exact ⟨by simp only [Prod.fst_add, hnX, hnY]; linarith,
                   by simp only [Prod.snd_add, hnX, hnY]; linarith⟩
          · -- Right boundary: delta = `(0, 1)`.
            rw [if_neg (by omega : ¬((j > g₁.rank - 1) ∧ (j < g₂.rank + 1))),
                if_neg (by omega : j ≠ g₁.rank - 1)] at hdelta
            have hbj := hbj_lt_dj j (by omega) (by omega)
            rw [hnX, hnY] at hbj
            have hd1 : (sigma (Pi.Y2 hε hle hm).val j).1 -
                       (sigma (Pi.X2 hε hle hm).val j).1 = 0 :=
              congr_arg Prod.fst hdelta
            have hd2 : (sigma (Pi.Y2 hε hle hm).val j).2 -
                       (sigma (Pi.X2 hε hle hm).val j).2 = 1 :=
              congr_arg Prod.snd hdelta
            have hb1 : (↑nX.2 : ℚ) + 1 ≤ ↑nY.2 :=
              by exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp hbj)
            exact ⟨by simp only [Prod.fst_add, hnX, hnY]; linarith [hXYj.1],
                   by simp only [Prod.snd_add, hnX, hnY]; linarith⟩
