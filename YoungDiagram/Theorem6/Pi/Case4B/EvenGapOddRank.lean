import YoungDiagram.Theorem6.Pi.Case4A
import YoungDiagram.Theorem6.Pi.Case4B.Common

open Variety hiding prime prime_def
open Chromosome Sigma

namespace Pi

/-! Case 4b, even rank-gap and odd lower rank. -/

lemma exists_mutation_le_case4b_evenGap_oddRank
    {n : ℕ} (X Y : nPi n) (hXY : X.1 < Y.1)
    {g₁ g₂ : Gene}
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1)
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
    (h_g1_rank_odd : ¬Even g₁.rank) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  refine exists_mutation_le_case4b_evenGap_of_sigma_window X Y hXg₁ hg₁_ge2 hg₁_one
    hg₂pos hg₂rank hε₂ ?_
  intro hε hle hm j
  have hXYj : sigma X.1.val j ≤ sigma Y.1.val j :=
    le_iff_dominates.mp hXY.le j
  obtain ⟨hcase1, hcase2, hcase3⟩ :=
    sigma_type2_mn_rank g₁.type hε hg₂rank hm
  by_cases hjl : j ≤ g₁.rank - 2
  · rw [← hcase1 j hjl]
    exact ⟨by simp [Prod.fst_add]; linarith [hXYj.1],
            by simp [Prod.snd_add]; linarith [hXYj.2]⟩
  · by_cases hjr : g₂.rank + 2 ≤ j
    · rw [← hcase2 j hjr]
      exact ⟨by simp [Prod.fst_add]; linarith [hXYj.1],
              by simp [Prod.snd_add]; linarith [hXYj.2]⟩
    · push Not at hjl hjr
      have hjl' : g₁.rank - 1 ≤ j := by omega
      have hjr' : j ≤ g₂.rank + 1 := by omega
      have hdelta := hcase3 j hjl' hjr'
      have hodd : Odd g₁.rank := Nat.not_even_iff_odd.mp h_g1_rank_odd
      have hg₁_ge3 : 3 ≤ g₁.rank := by obtain ⟨k, hk⟩ := hodd; omega
      have hε_pos : g₁.type = GeneType.Positive :=
        gene_type_eq_positive_of_odd_of_ne_negOnePow_negative hodd hε hε₁
      have hg₂_odd : Odd g₂.rank := by
        obtain ⟨a, ha⟩ := hodd
        obtain ⟨b, hb⟩ := hparity
        exact ⟨a + b, by omega⟩
      have hg₂_pos : g₂.type = .Positive := by
        rw [gene_type_eq_of_X_pos_not_opposite X hε hg₂pos hε₂, hε_pos]
      have hstrict :
          (sigma Y.1 0).1 - (sigma Y.1 1).1 <
          (sigma X.1 0).1 - (sigma X.1 1).1 :=
        fst_zero_gap_strict_of_fst_one_lt X Y hXY.le ha
      have hd2_gt_b2 : (sigma X.1 2).2 < (sigma Y.1 2).2 :=
        snd_two_lt_of_fst_one_lt_and_min_rank X Y hXY.le ha hg₁min hg₁_ge2
      have all_rel :
          (sigma X.1 g₁.rank).1 < (sigma Y.1 g₁.rank).1 ∧
          (sigma X.1 (g₁.rank + 1)).1 < (sigma Y.1 (g₁.rank + 1)).1 ∧
          (sigma X.1 g₁.rank).2 < (sigma Y.1 g₁.rank).2 ∧
          (sigma X.1 (g₁.rank - 1)).2 < (sigma Y.1 (g₁.rank - 1)).2 := by
        have hc1_ci_rank :
            (sigma Y.1 1).1 - (sigma Y.1 g₁.rank).1 ≤
            (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 1)).2 :=
          Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
        have hd0_di_rank :
            (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 1)).2 ≤
            (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 1)).2 :=
          theorem6_snd_gap_le_of_dominates X Y hXY.le
        have hb0_bi : ∀ j, 1 ≤ j → j ≤ g₁.rank + 1 →
            (sigma X.1 0).2 - (sigma X.1 (j - 1)).2 =
            (sigma X.1 1).1 - (sigma X.1 j).1 := by
          intro j hj1 hj2
          by_cases hj : j = 1
          · subst hj
            simp
          · have no_neg_gene_rank_g : ∀ g' ∈ X.1.val.support,
                g'.rank = g₁.rank → g'.type = .Positive := fun g' hg'_supp hg'_rank =>
              support_same_rank_type_eq_positive X hXpn hε_pos hXg₁pos hg'_supp hg'_rank
            have h := Sigma.b0_bi_eq_a1_ai1 X.1.val X.1.2 (j - 1)
              (fun g hg_supp hrank_le => no_neg_gene_rank_g g hg_supp (by
                have := hg₁min g hg_supp; omega))
            rwa [Nat.sub_add_cancel hj1] at h
        have hb0_bi_rank := hb0_bi g₁.rank (by omega) (by omega)
        have ha_lt_c_rank : (sigma X.1 g₁.rank).1 < (sigma Y.1 g₁.rank).1 :=
          fst_lt_of_gap_chain X Y hXY.le hstrict hc1_ci_rank hd0_di_rank hb0_bi_rank
        have hc1_ci_rank1 :
            (sigma Y.1 1).1 - (sigma Y.1 (g₁.rank + 1)).1 ≤
            (sigma Y.1 0).2 - (sigma Y.1 g₁.rank).2 :=
          Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
        have hd0_di_rank1 :
            (sigma Y.1 0).2 - (sigma Y.1 g₁.rank).2 ≤
            (sigma X.1 0).2 - (sigma X.1 g₁.rank).2 :=
          theorem6_snd_gap_le_of_dominates X Y hXY.le
        have hb0_bi_rank1 := hb0_bi (g₁.rank + 1) (by omega) (le_refl _)
        simp only [Nat.add_sub_cancel] at hb0_bi_rank1
        have ha_lt_c_rank1 :
            (sigma X.1 (g₁.rank + 1)).1 < (sigma Y.1 (g₁.rank + 1)).1 :=
          fst_lt_of_gap_chain X Y hXY.le hstrict hc1_ci_rank1 hd0_di_rank1 hb0_bi_rank1
        have hd2_c1_rank :
            (sigma Y.1 2).2 - (sigma Y.1 g₁.rank).2 ≤
            (sigma Y.1 1).1 - (sigma Y.1 (g₁.rank - 1)).1 := by
          have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 (show g₁.rank - 1 ≥ 2 by omega)
          rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
        have hd2_c1_rank1 :
            (sigma Y.1 2).2 - (sigma Y.1 (g₁.rank - 1)).2 ≤
            (sigma Y.1 1).1 - (sigma Y.1 (g₁.rank - 2)).1 := by
          by_cases hrank3 : g₁.rank = 3
          · simp [hrank3]
          · have hg₁_ge5 : 5 ≤ g₁.rank := by obtain ⟨k, hk⟩ := hodd; omega
            have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 (show g₁.rank - 2 ≥ 2 by omega)
            rwa [show g₁.rank - 2 + 1 = g₁.rank - 1 from by omega] at this
        have hd2_di1_rank :
            (sigma Y.1 2).2 - (sigma Y.1 g₁.rank).2 ≤
            (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 2)).2 :=
          hd2_c1_rank.trans (Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega))
        have hd2_di1_rank1 :
            (sigma Y.1 2).2 - (sigma Y.1 (g₁.rank - 1)).2 ≤
            (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 3)).2 :=
          hd2_c1_rank1.trans (Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2
            (by obtain ⟨k, hk⟩ := hodd; omega))
        have hd0_di_rank2 :
            (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 2)).2 ≤
            (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 2)).2 :=
          theorem6_snd_gap_le_of_dominates X Y hXY.le
        have hd0_di_rank3 :
            (sigma Y.1 0).2 - (sigma Y.1 (g₁.rank - 3)).2 ≤
            (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 3)).2 :=
          theorem6_snd_gap_le_of_dominates X Y hXY.le
        have hb0_b2_rank :
            (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 2)).2 =
            (sigma X.1 2).2 - (sigma X.1 g₁.rank).2 := by
          have h := Sigma.b0_eq_b2_positive g₁.rank hg₁min (le_refl (g₁.rank - 2))
          simpa [show g₁.rank - 2 + 2 = g₁.rank from by omega] using h
        have hb0_b2_rank1 :
            (sigma X.1 0).2 - (sigma X.1 (g₁.rank - 3)).2 =
            (sigma X.1 2).2 - (sigma X.1 (g₁.rank - 1)).2 := by
          have h := Sigma.b0_eq_b2_positive g₁.rank hg₁min
            (show g₁.rank - 3 ≤ g₁.rank - 2 from by omega)
          simpa [show g₁.rank - 3 + 2 = g₁.rank - 1 from by
            obtain ⟨k, hk⟩ := hodd; omega] using h
        have hb_lt_d_rank : (sigma X.1 g₁.rank).2 < (sigma Y.1 g₁.rank).2 :=
          snd_lt_of_gap_chain X Y hd2_gt_b2 hd2_di1_rank hd0_di_rank2 hb0_b2_rank
        have hb_lt_d_rank1 :
            (sigma X.1 (g₁.rank - 1)).2 < (sigma Y.1 (g₁.rank - 1)).2 :=
          snd_lt_of_gap_chain X Y hd2_gt_b2 hd2_di1_rank1 hd0_di_rank3 hb0_b2_rank1
        exact ⟨ha_lt_c_rank, ha_lt_c_rank1, hb_lt_d_rank, hb_lt_d_rank1⟩
      obtain ⟨ha_lt_c_rank, ha_lt_c_rank1, hb_lt_d_rank, hb_lt_d_rank1⟩ := all_rel
      have hdi_sub_le_bi_sub : ∀ j, g₁.rank - 1 ≤ j → j ≤ g₂.rank - 1 →
          (sigma Y.1.val j).2 - (sigma Y.1.val (j + 1)).2 ≤
          (sigma X.1.val j).2 - (sigma X.1.val (j + 1)).2 := by
        intro j hj1 hj2
        by_cases hjeven : Even j
        · have hdj_le_d0 :
              (sigma Y.1.val j).2 - (sigma Y.1.val (j + 1)).2 ≤
              (sigma Y.1.val 0).2 - (sigma Y.1.val 1).2 :=
            snd_drop_even_le_snd_drop_zero Y.1.2 hjeven
          have hd0_le_b0 :
              (sigma Y.1.val 0).2 - (sigma Y.1.val 1).2 ≤
              (sigma X.1.val 0).2 - (sigma X.1.val 1).2 :=
            snd_zero_gap_le_of_dominates X Y hXY.le
          have hb0_eq_bj :
              (sigma X.1.val 0).2 - (sigma X.1.val 1).2 =
              (sigma X.1.val j).2 - (sigma X.1.val (j + 1)).2 := by
            have hLHS : (sigma X.1.val 0).2 - (sigma X.1.val 1).2 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  0 < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Negative),
                (X.1.val g : ℚ) := by
              have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
              have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
              simp only [Function.iterate_zero, id] at h1 h2
              exact h1.trans h2
            have hRHS : (sigma X.1.val j).2 - (sigma X.1.val (j + 1)).2 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  j < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Negative),
                (X.1.val g : ℚ) := by
              have h1 := Sigma.sigma_snd_diff X.1.val j X.1.2
              have h2 := Sigma.prime_iterate_sum_eq X.1.val j GeneType.Negative
              simp only [show Int.negOnePow (j : ℤ) = 1 from
                Int.negOnePow_even _ (by exact_mod_cast hjeven),
                one_smul] at h2
              exact h1.trans h2
            have hfilter_eq :
                X.1.val.support.filter (fun g =>
                  0 < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Negative) =
                X.1.val.support.filter (fun g =>
                  j < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Negative) :=
              support_filter_negative_eq_tail_of_odd hXpn hXg₁pos hg₁min
                hg₂min h_g1_rank_odd hε_pos hj2
            rw [hLHS, hRHS, hfilter_eq]
          linarith
        · have hdj_le_c01 :
              (sigma Y.1.val j).2 - (sigma Y.1.val (j + 1)).2 ≤
              (sigma Y.1.val 0).1 - (sigma Y.1.val 1).1 := by
            simpa [hjeven] using Sigma.cond_15_6_compare_k_to_0 Y.1.val j Y.1.2
          have hc01_le_a01_sub1 :
              (sigma Y.1.val 0).1 - (sigma Y.1.val 1).1 ≤
              (sigma X.1.val 0).1 - (sigma X.1.val 1).1 - 1 :=
            fst_zero_gap_le_sub_one_of_fst_one_lt X Y hXY.le ha
          have ha01_sub1_eq_am_sub1 :
              (sigma X.1.val 0).1 - (sigma X.1.val 1).1 - 1 =
              (sigma X.1.val (g₁.rank - 1)).1 - (sigma X.1.val g₁.rank).1 - 1 := by
            have h := x_side_equalities
              (fun g' _ hg' => hg₁min g' (Finsupp.mem_support_iff.mpr hg'.ne'))
              (show g₁.rank - 1 < g₁.rank by omega)
            rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
            have heven_sub1 : Even (g₁.rank - 1) := by
              obtain ⟨r, hr⟩ := hodd; exact ⟨r, by omega⟩
            simp only [if_pos heven_sub1] at h
            linarith
          have ham_sub1_eq_bm :
              (sigma X.1.val (g₁.rank - 1)).1 - (sigma X.1.val g₁.rank).1 - 1 =
              (sigma X.1.val g₁.rank).2 - (sigma X.1.val (g₁.rank + 1)).2 := by
            have hLHS : (sigma X.1.val (g₁.rank - 1)).1 -
                (sigma X.1.val g₁.rank).1 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  g₁.rank - 1 < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive),
                (X.1.val g : ℚ) := by
              have h := Sigma.sigma_fst_diff X.1.val (g₁.rank - 1) X.1.2
              rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
              rw [h, Sigma.prime_iterate_sum_pos_eq X.1.val (g₁.rank - 1)
                      (show Even (g₁.rank - 1) by
                        obtain ⟨r, hr⟩ := hodd; exact ⟨r, by omega⟩)]
              rfl
            have hRHS : (sigma X.1.val g₁.rank).2 -
                (sigma X.1.val (g₁.rank + 1)).2 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive),
                (X.1.val g : ℚ) := by
              rw [Sigma.sigma_snd_diff X.1.val g₁.rank X.1.2,
                  Sigma.prime_iterate_sum_neg_eq X.1.val g₁.rank h_g1_rank_odd]
              rfl
            have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
              rw [Sigma.altType_odd g₁.rank h_g1_rank_odd]; exact hε_pos
            have hfilter_split :
                X.1.val.support.filter (fun g =>
                  g₁.rank - 1 < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive) =
                {g₁} ∪ X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive) :=
              support_filter_rank_pred_altType_split hg₁_one hg₁_altType
            have hdisjoint : Disjoint {g₁} (X.1.val.support.filter (fun g =>
                g₁.rank < g.rank ∧ g.type =
                Sigma.altType g.rank GeneType.Positive)) := by
              simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_filter]
              rintro g rfl ⟨_, hlt, _⟩; exact absurd hlt (lt_irrefl _)
            rw [hLHS, hfilter_split, Finset.sum_union hdisjoint, Finset.sum_singleton,
                show (X.1.val g₁ : ℚ) = 1 from by exact_mod_cast hg₁_one, hRHS]
            ring
          have hbm_eq_bj :
              (sigma X.1.val g₁.rank).2 - (sigma X.1.val (g₁.rank + 1)).2 =
              (sigma X.1.val j).2 - (sigma X.1.val (j + 1)).2 := by
            have hLHS : (sigma X.1.val g₁.rank).2 -
                (sigma X.1.val (g₁.rank + 1)).2 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive),
                (X.1.val g : ℚ) := by
              rw [Sigma.sigma_snd_diff X.1.val g₁.rank X.1.2,
                  Sigma.prime_iterate_sum_neg_eq X.1.val g₁.rank h_g1_rank_odd]
              rfl
            have hRHS : (sigma X.1.val j).2 -
                (sigma X.1.val (j + 1)).2 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  j < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive),
                (X.1.val g : ℚ) := by
              rw [Sigma.sigma_snd_diff X.1.val j X.1.2,
                  Sigma.prime_iterate_sum_neg_eq X.1.val j hjeven]
              rfl
            have hj1' : g₁.rank ≤ j := by
              obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hjeven
              obtain ⟨r, hr⟩ := hodd; omega
            have hfilter_eq :
                X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive) =
                X.1.val.support.filter (fun g =>
                  j < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive) :=
              support_filter_tail_eq hg₂min hj1' hj2
            rw [hLHS, hRHS, hfilter_eq]
          linarith
      have hbj_lt_dj : ∀ j, g₁.rank - 1 ≤ j → j ≤ g₂.rank →
          (sigma X.1.val j).2 < (sigma Y.1.val j).2 := by
        intro j hj1 hj2
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj1
        induction d with
        | zero => simpa using hb_lt_d_rank1
        | succ d ih =>
          have ihd := ih (by omega) (by omega)
          have hstep := hdi_sub_le_bi_sub (g₁.rank - 1 + d) (by omega) (by omega)
          obtain ⟨nX_d, hnX_d⟩ := sigma_isNat X.1.val (g₁.rank - 1 + d) X.1.2
          obtain ⟨nY_d, hnY_d⟩ := sigma_isNat Y.1.val (g₁.rank - 1 + d) Y.1.2
          obtain ⟨nX_s, hnX_s⟩ := sigma_isNat X.1.val (g₁.rank - 1 + d + 1) X.1.2
          obtain ⟨nY_s, hnY_s⟩ := sigma_isNat Y.1.val (g₁.rank - 1 + d + 1) Y.1.2
          rw [hnX_d, hnY_d] at ihd hstep
          rw [hnX_s, hnY_s] at hstep
          rw [show g₁.rank - 1 + Nat.succ d = g₁.rank - 1 + d + 1 from by omega,
              hnX_s, hnY_s]
          have h1 : (↑nX_d.2 : ℚ) + 1 ≤ ↑nY_d.2 := by
            exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp ihd)
          linarith
      have hci_sub_le_ai_sub : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank →
          (sigma Y.1.val j).1 - (sigma Y.1.val (j + 1)).1 ≤
          (sigma X.1.val j).1 - (sigma X.1.val (j + 1)).1 := by
        intro j hj1 hj2
        by_cases hjeven : Even j
        · have hj2' : j ≤ g₂.rank - 1 := by
            obtain ⟨a, ha⟩ := hjeven
            obtain ⟨b, hb⟩ := hg₂_odd; omega
          have hcj_le_c01 :
              (sigma Y.1.val j).1 - (sigma Y.1.val (j + 1)).1 ≤
              (sigma Y.1.val 0).1 - (sigma Y.1.val 1).1 := by
            simpa [hjeven] using Sigma.cond_15_6_compare_k_to_0 Y.1.val j Y.1.2
          have hc01_le_a01_sub1 :
              (sigma Y.1.val 0).1 - (sigma Y.1.val 1).1 ≤
              (sigma X.1.val 0).1 - (sigma X.1.val 1).1 - 1 :=
            fst_zero_gap_le_sub_one_of_fst_one_lt X Y hXY.le ha
          have ha01_sub1_eq_am_sub1 :
              (sigma X.1.val 0).1 - (sigma X.1.val 1).1 - 1 =
              (sigma X.1.val (g₁.rank - 1)).1 - (sigma X.1.val g₁.rank).1 - 1 := by
            have h := x_side_equalities
              (fun g' _ hg' => hg₁min g' (Finsupp.mem_support_iff.mpr hg'.ne'))
              (show g₁.rank - 1 < g₁.rank by omega)
            rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
            have heven_sub1 : Even (g₁.rank - 1) := by
              obtain ⟨r, hr⟩ := hodd; exact ⟨r, by omega⟩
            simp only [if_pos heven_sub1] at h
            linarith
          have ham_sub1_eq_bm :
              (sigma X.1.val (g₁.rank - 1)).1 - (sigma X.1.val g₁.rank).1 - 1 =
              (sigma X.1.val g₁.rank).2 - (sigma X.1.val (g₁.rank + 1)).2 := by
            have hLHS : (sigma X.1.val (g₁.rank - 1)).1 -
                (sigma X.1.val g₁.rank).1 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  g₁.rank - 1 < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive),
                (X.1.val g : ℚ) := by
              have h := Sigma.sigma_fst_diff X.1.val (g₁.rank - 1) X.1.2
              rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
              rw [h, Sigma.prime_iterate_sum_pos_eq X.1.val (g₁.rank - 1)
                      (show Even (g₁.rank - 1) by
                        obtain ⟨r, hr⟩ := hodd; exact ⟨r, by omega⟩)]
              rfl
            have hRHS : (sigma X.1.val g₁.rank).2 -
                (sigma X.1.val (g₁.rank + 1)).2 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive),
                (X.1.val g : ℚ) := by
              rw [Sigma.sigma_snd_diff X.1.val g₁.rank X.1.2,
                  Sigma.prime_iterate_sum_neg_eq X.1.val g₁.rank h_g1_rank_odd]
              rfl
            have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
              rw [Sigma.altType_odd g₁.rank h_g1_rank_odd]; exact hε_pos
            have hfilter_split :
                X.1.val.support.filter (fun g =>
                  g₁.rank - 1 < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive) =
                {g₁} ∪ X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive) :=
              support_filter_rank_pred_altType_split hg₁_one hg₁_altType
            have hdisjoint : Disjoint {g₁} (X.1.val.support.filter (fun g =>
                g₁.rank < g.rank ∧ g.type =
                Sigma.altType g.rank GeneType.Positive)) := by
              simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_filter]
              rintro g rfl ⟨_, hlt, _⟩; exact absurd hlt (lt_irrefl _)
            rw [hLHS, hfilter_split, Finset.sum_union hdisjoint, Finset.sum_singleton,
                show (X.1.val g₁ : ℚ) = 1 from by exact_mod_cast hg₁_one, hRHS]
            ring
          have hbm_eq_aj :
              (sigma X.1.val g₁.rank).2 - (sigma X.1.val (g₁.rank + 1)).2 =
              (sigma X.1.val j).1 - (sigma X.1.val (j + 1)).1 := by
            have hLHS : (sigma X.1.val g₁.rank).2 -
                (sigma X.1.val (g₁.rank + 1)).2 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive),
                (X.1.val g : ℚ) := by
              rw [Sigma.sigma_snd_diff X.1.val g₁.rank X.1.2,
                  Sigma.prime_iterate_sum_neg_eq X.1.val g₁.rank h_g1_rank_odd]
              rfl
            have hRHS : (sigma X.1.val j).1 -
                (sigma X.1.val (j + 1)).1 =
                ∑ g ∈ X.1.val.support.filter (fun g =>
                  j < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive),
                (X.1.val g : ℚ) := by
              rw [Sigma.sigma_fst_diff X.1.val j X.1.2,
                  Sigma.prime_iterate_sum_pos_eq X.1.val j hjeven]
              rfl
            have hfilter_eq :
                X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive) =
                X.1.val.support.filter (fun g =>
                  j < g.rank ∧
                  g.type = Sigma.altType g.rank GeneType.Positive) :=
              support_filter_tail_eq hg₂min hj1 hj2'
            rw [hLHS, hRHS, hfilter_eq]
          linarith
        · by_cases hjtop : j = g₂.rank
          · subst hjtop
            have hcj_le_c12 :
                (sigma Y.1.val g₂.rank).1 - (sigma Y.1.val (g₂.rank + 1)).1 ≤
                (sigma Y.1.val 1).1 - (sigma Y.1.val 2).1 :=
              fst_drop_odd_le_fst_drop_one Y.1.2
                (Nat.not_even_iff_odd.mpr hg₂_odd)
            have hc12_le_d01 :
                (sigma Y.1.val 1).1 - (sigma Y.1.val 2).1 ≤
                (sigma Y.1.val 0).2 - (sigma Y.1.val 1).2 := by
              simpa using Sigma.cond_15_7 Y.1.val 0 Y.1.2
            have hd01_le_b01 :
                (sigma Y.1.val 0).2 - (sigma Y.1.val 1).2 ≤
                (sigma X.1.val 0).2 - (sigma X.1.val 1).2 :=
              snd_zero_gap_le_of_dominates X Y hXY.le
            have hb01_eq_aj :
                (sigma X.1.val 0).2 - (sigma X.1.val 1).2 =
                (sigma X.1.val g₂.rank).1 - (sigma X.1.val (g₂.rank + 1)).1 := by
              have hLHS : (sigma X.1.val 0).2 - (sigma X.1.val 1).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    0 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative),
                  (X.1.val g : ℚ) := by
                have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
                have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
                simp only [Function.iterate_zero, id] at h1 h2
                exact h1.trans h2
              have hRHS : (sigma X.1.val g₂.rank).1 - (sigma X.1.val (g₂.rank + 1)).1 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    g₂.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative),
                  (X.1.val g : ℚ) := by
                have hkodd : Int.negOnePow (g₂.rank : ℤ) = -1 :=
                  Int.negOnePow_odd _ (by exact_mod_cast hg₂_odd)
                have h1 := Sigma.sigma_fst_diff X.1.val g₂.rank X.1.2
                have h2 := Sigma.prime_iterate_sum_eq X.1.val g₂.rank GeneType.Positive
                simp only [hkodd, GeneType.neg_one_smul, GeneType.neg_positive] at h2
                exact h1.trans h2
              have hfilter_eq :
                  X.1.val.support.filter (fun g =>
                    0 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative) =
                  X.1.val.support.filter (fun g =>
                    g₂.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative) := by
                ext g
                simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                refine ⟨?_, fun ⟨hg_supp, _, hg_type⟩ => ⟨hg_supp, g.rank_pos, hg_type⟩⟩
                rintro ⟨hg_supp, _, hg_type⟩
                rcases Nat.lt_or_eq_of_le
                    (hg₁min g (Finsupp.mem_support_iff.mpr hg_supp)) with hlt | heq
                · have hg₂_le : g₂.rank ≤ g.rank :=
                    hg₂min g (Nat.pos_of_ne_zero hg_supp) hlt
                  rcases Nat.lt_or_eq_of_le hg₂_le with hlt₂ | heq₂
                  · exact ⟨hg_supp, hlt₂, hg_type⟩
                  · exfalso
                    have halttype :
                        Sigma.altType g.rank GeneType.Negative = GeneType.Negative := by
                      rw [show g.rank = g₂.rank from by omega,
                          Sigma.altType_odd g₂.rank (Nat.not_even_iff_odd.mpr hg₂_odd)]
                    rw [halttype] at hg_type
                    exact hXpn ⟨g₂, g, by omega, hg₂_pos, hg_type, hg₂pos,
                      Nat.pos_of_ne_zero hg_supp⟩
                · exfalso
                  have halttype :
                      Sigma.altType g.rank GeneType.Negative = GeneType.Negative := by
                    rw [show g.rank = g₁.rank from by omega,
                        Sigma.altType_odd g₁.rank h_g1_rank_odd]
                  rw [halttype] at hg_type
                  exact hXpn ⟨g₁, g, by omega, hε_pos, hg_type, hXg₁pos,
                    Nat.pos_of_ne_zero hg_supp⟩
              rw [hLHS, hRHS, hfilter_eq]
            linarith
          · have hj2' : j ≤ g₂.rank - 1 := by omega
            have hcj_le_c12 :
                (sigma Y.1.val j).1 - (sigma Y.1.val (j + 1)).1 ≤
                (sigma Y.1.val 1).1 - (sigma Y.1.val 2).1 :=
              fst_drop_odd_le_fst_drop_one Y.1.2 hjeven
            have hc12_le_d01 :
                (sigma Y.1.val 1).1 - (sigma Y.1.val 2).1 ≤
                (sigma Y.1.val 0).2 - (sigma Y.1.val 1).2 := by
              simpa using Sigma.cond_15_7 Y.1.val 0 Y.1.2
            have hd01_le_b01 :
                (sigma Y.1.val 0).2 - (sigma Y.1.val 1).2 ≤
                (sigma X.1.val 0).2 - (sigma X.1.val 1).2 :=
              snd_zero_gap_le_of_dominates X Y hXY.le
            have hb01_eq_aj :
                (sigma X.1.val 0).2 - (sigma X.1.val 1).2 =
                (sigma X.1.val j).1 - (sigma X.1.val (j + 1)).1 := by
              have hLHS : (sigma X.1.val 0).2 - (sigma X.1.val 1).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    0 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative),
                  (X.1.val g : ℚ) := by
                have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
                have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
                simp only [Function.iterate_zero, id] at h1 h2
                exact h1.trans h2
              have hRHS : (sigma X.1.val j).1 - (sigma X.1.val (j + 1)).1 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    j < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative),
                  (X.1.val g : ℚ) := by
                have hkodd : Int.negOnePow (j : ℤ) = -1 :=
                  Int.negOnePow_odd _ (by exact_mod_cast Nat.not_even_iff_odd.mp hjeven)
                have h1 := Sigma.sigma_fst_diff X.1.val j X.1.2
                have h2 := Sigma.prime_iterate_sum_eq X.1.val j GeneType.Positive
                simp only [hkodd, GeneType.neg_one_smul, GeneType.neg_positive] at h2
                exact h1.trans h2
              have hfilter_eq :
                  X.1.val.support.filter (fun g =>
                    0 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative) =
                  X.1.val.support.filter (fun g =>
                    j < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative) :=
                support_filter_negative_eq_tail_of_odd hXpn hXg₁pos hg₁min
                  hg₂min h_g1_rank_odd hε_pos hj2'
              rw [hLHS, hRHS, hfilter_eq]
            linarith
      have haj_lt_cj : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank + 1 →
          (sigma X.1.val j).1 < (sigma Y.1.val j).1 := by
        intro j hj1 hj2
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj1
        induction d with
        | zero => simpa using ha_lt_c_rank
        | succ d ih =>
          have ihd := ih (by omega) (by omega)
          have hstep := hci_sub_le_ai_sub (g₁.rank + d) (by omega) (by omega)
          obtain ⟨nX_d, hnX_d⟩ := sigma_isNat X.1.val (g₁.rank + d) X.1.2
          obtain ⟨nY_d, hnY_d⟩ := sigma_isNat Y.1.val (g₁.rank + d) Y.1.2
          obtain ⟨nX_s, hnX_s⟩ := sigma_isNat X.1.val (g₁.rank + d + 1) X.1.2
          obtain ⟨nY_s, hnY_s⟩ := sigma_isNat Y.1.val (g₁.rank + d + 1) Y.1.2
          rw [hnX_d, hnY_d] at ihd hstep
          rw [hnX_s, hnY_s] at hstep
          rw [show g₁.rank + Nat.succ d = g₁.rank + d + 1 from by omega, hnX_s, hnY_s]
          have h1 : (↑nX_d.1 : ℚ) + 1 ≤ ↑nY_d.1 := by
            exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp ihd)
          linarith
      rcases (show j = g₁.rank - 1 ∨
                    (g₁.rank ≤ j ∧ j ≤ g₂.rank) ∨
                    j = g₂.rank + 1 from by omega)
          with hjbd | ⟨hjl2, hjr2⟩ | hjbd2
      · have hdelta_eq :
            sigma (Pi.Y2 hε hle hm).val j =
            sigma (Pi.X2 hε hle hm).val j + (0, 1) := by
          apply theorem6_sigma_eq_add_of_sub_eq
          rwa [if_neg (by omega : ¬((j > g₁.rank - 1) ∧ (j < g₂.rank + 1))),
              if_pos hjbd, if_pos hε_pos] at hdelta
        rw [hdelta_eq]
        have hbj := hbj_lt_dj j (by omega) (by omega)
        have hb1 := theorem6_sigma_snd_add_one_le_of_lt X.1.2 Y.1.2 j hbj
        refine ⟨?_, ?_⟩
        · simp only [Prod.fst_add]; linarith [hXYj.1]
        · simp only [Prod.snd_add, add_assoc]; linarith
      · have hdelta_eq :
            sigma (Pi.Y2 hε hle hm).val j =
            sigma (Pi.X2 hε hle hm).val j + (1, 1) := by
          apply theorem6_sigma_eq_add_of_sub_eq
          rwa [if_pos (show (j > g₁.rank - 1) ∧ (j < g₂.rank + 1)
                      from ⟨by omega, by omega⟩)] at hdelta
        rw [hdelta_eq]
        have haj := haj_lt_cj j hjl2 (by omega)
        have hbj := hbj_lt_dj j (by omega) hjr2
        have ha1 := theorem6_sigma_fst_add_one_le_of_lt X.1.2 Y.1.2 j haj
        have hb1 := theorem6_sigma_snd_add_one_le_of_lt X.1.2 Y.1.2 j hbj
        refine ⟨?_, ?_⟩
        · simp only [Prod.fst_add, add_assoc]; linarith
        · simp only [Prod.snd_add, add_assoc]; linarith
      · have hdelta_eq :
            sigma (Pi.Y2 hε hle hm).val j =
            sigma (Pi.X2 hε hle hm).val j + (1, 0) := by
          apply theorem6_sigma_eq_add_of_sub_eq
          rwa [if_neg (by omega : ¬((j > g₁.rank - 1) ∧ (j < g₂.rank + 1))),
              if_neg (by omega : j ≠ g₁.rank - 1), if_pos hε_pos] at hdelta
        rw [hdelta_eq]
        have haj := haj_lt_cj j (by omega) (by omega)
        have ha1 := theorem6_sigma_fst_add_one_le_of_lt X.1.2 Y.1.2 j haj
        refine ⟨?_, ?_⟩
        · simp only [Prod.fst_add, add_assoc]; linarith
        · simp only [Prod.snd_add]; linarith [hXYj.2]

end Pi
