import YoungDiagram.Theorem6.Pi.Prelim

open Variety hiding prime prime_def
open Chromosome

namespace Pi

private lemma sigma_eq_add_of_sub_eq {p q δ : ℚ × ℚ} (h : p - q = δ) : p = q + δ := by
  rw [← h]; abel

private lemma sigma_fst_add_one_le_of_lt {X Y : Chromosome}
    (hX : X ∈ Variety.Pi) (hY : Y ∈ Variety.Pi) (i : ℕ)
    (h : (Sigma.sigma X i).1 < (Sigma.sigma Y i).1) :
    (Sigma.sigma X i).1 + 1 ≤ (Sigma.sigma Y i).1 := by
  obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X i hX
  obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y i hY
  rw [hnX, hnY] at h ⊢
  have h' : (nX.1 : ℚ) < nY.1 := by simpa using h
  change (nX.1 : ℚ) + 1 ≤ nY.1
  exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp h')

private lemma sigma_snd_add_one_le_of_lt {X Y : Chromosome}
    (hX : X ∈ Variety.Pi) (hY : Y ∈ Variety.Pi) (i : ℕ)
    (h : (Sigma.sigma X i).2 < (Sigma.sigma Y i).2) :
    (Sigma.sigma X i).2 + 1 ≤ (Sigma.sigma Y i).2 := by
  obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X i hX
  obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y i hY
  rw [hnX, hnY] at h ⊢
  have h' : (nX.2 : ℚ) < nY.2 := by simpa using h
  change (nX.2 : ℚ) + 1 ≤ nY.2
  exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp h')

private lemma snd_gap_le_of_dominates {n i : ℕ} (X Y : nPi n) (hXY : X.1 ≤ Y.1) :
    (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 i).2 ≤
      (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 i).2 := by
  have h0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 := sigma_zero_snd_eq X Y hXY
  have hi : (Sigma.sigma X.1 i).2 ≤ (Sigma.sigma Y.1 i).2 :=
    (le_iff_dominates.mp hXY i).2
  linarith

private lemma fst_lt_of_gap_chain {n i j : ℕ} (X Y : nPi n) (hXY : X.1 ≤ Y.1)
    (hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
      (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1)
    (hc1_ci : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 i).1 ≤
      (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 j).2)
    (hd0_di : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 j).2 ≤
      (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 j).2)
    (hb0_bi : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 j).2 =
      (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 i).1) :
    (Sigma.sigma X.1 i).1 < (Sigma.sigma Y.1 i).1 := by
  have := sigma_zero_fst_eq X Y hXY
  linarith

private lemma snd_lt_of_gap_chain {n i j : ℕ} (X Y : nPi n)
    (hd2_gt_b2 : (Sigma.sigma X.1 2).2 < (Sigma.sigma Y.1 2).2)
    (hd2_di : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 i).2 ≤
      (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 j).2)
    (hd0_di : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 j).2 ≤
      (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 j).2)
    (hb0_b2 : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 j).2 =
      (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 i).2) :
    (Sigma.sigma X.1 i).2 < (Sigma.sigma Y.1 i).2 := by
  linarith

private lemma gene_type_eq_negative_of_even {g : Gene} (heven : Even g.rank)
    (hε : g.type ≠ .NonPolarized)
    (hε₁ : ¬ g.type = Int.negOnePow (g.rank - 1) • GeneType.Negative) : g.type = .Negative := by
  have hfamily := gene_type_eq_negOnePow_positive_of_ne_negOnePow_negative hε hε₁
  have hodd : ¬ Even ((g.rank : ℤ) - 1) := by simp [heven]
  simpa [GeneType.negOnePow_smul, GeneType.neg_positive, hodd] using hfamily

private lemma gene_type_eq_positive_of_odd {g : Gene} (hodd : Odd g.rank)
    (hε : g.type ≠ .NonPolarized)
    (hε₁ : ¬ g.type = Int.negOnePow (g.rank - 1) • GeneType.Negative) : g.type = .Positive := by
  have hfamily := gene_type_eq_negOnePow_positive_of_ne_negOnePow_negative hε hε₁
  have h_even : Even ((g.rank : ℤ) - 1) := by simp [hodd]
  simpa [GeneType.negOnePow_smul, GeneType.neg_positive, h_even] using hfamily

-- Case 3 is the type-2 mutation window check with several parity subcases.
lemma exists_mutation_le_case3
    {n : ℕ} (X Y : nPi n) (hXY : X.1 < Y.1)
    {g₁ : Gene}
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1)
    (hε₁ : ¬ g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Negative)
    (hXg₁ : X.1.val g₁ ≠ 0)
    (hXg₁pos : 0 < X.1.val g₁)
    (hg₁min : ∀ g ∈ X.1.val.support, g₁.rank ≤ g.rank)
    (hg₁_ge2 : 2 ≤ g₁.rank)
    (h2g₁ : 2 ≤ X.1.val g₁) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
    -- Case 3: g₁ is polarized, appears with multiplicity ≥ 2
    have hε : g₁.type ≠ .NonPolarized :=
      IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
    have hg₁_ofRank : Gene.ofRank g₁.rank g₁.type = Finsupp.single g₁ 1 :=
      @Gene.ofRank_eq_gene g₁
    have hsrc_val : (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 : Chromosome) =
        Finsupp.single g₁ 2 := by
      simp only [Pi.X2_eq, hg₁_ofRank]
      ext g; simp [Finsupp.single_apply]; split_ifs with heq <;> simp
    have hsrc_le : ∀ g : Gene,
        (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 : Chromosome) g ≤ X.1.val g := by
      intro g
      rw [hsrc_val, Finsupp.single_apply]
      split_ifs with heq
      · subst heq; exact h2g₁
      · exact Nat.zero_le _
    -- rest = X.1 − Pi.X2, still in Pi
    let rest : Pi :=
      ⟨X.1.val - (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 : Chromosome),
        Variety.sub_mem_Pi _ X.1.2⟩
    have hdecomp : X.1 = Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 + rest :=
      Subtype.val_injective
        (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
    -- Z is the type2 mutation result: Pi.Y2 + rest
    let Z : Pi := Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2 + rest
    have hstep : Pi.Step X.1 Z :=
      hdecomp.symm ▸ Pi.Step.mk
        (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2)
        (Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2)
        rest
        (Pi.Primitive.type2 g₁.type hε (le_refl g₁.rank) hg₁_ge2)
    -- b₁ - b₂ = a₀ - a₁ via x_side_equalities at j = 1 (odd)
    have hb12_eq : (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 =
        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
      have h := x_side_equalities
        (fun g' _ hg'_pos => hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
        (show 1 < g₁.rank from hg₁_ge2)
      simpa [show ¬Even 1 from by norm_num] using h
    -- a₀ - a₁ > c₀ - c₁
    have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
      have := sigma_zero_fst_eq X Y hXY.le
      linarith
    -- c₀ - c₁ ≥ d₁ - d₂
    have hd12_le : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 ≤
        (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
      have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (2 - 1) Y.1.2
      simpa [show ¬Even (2 - 1 : ℕ) from by norm_num] using h
    have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
      (le_iff_dominates.mp hXY.le 1).2
    -- b₁ - b₂ > d₁ - d₂
    have hb12_gt_d12 : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 <
        (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 := by linarith
    -- d₂ > b₂
    have hd2_gt_b2 : (Sigma.sigma X.1 2).2 < (Sigma.sigma Y.1 2).2 := by linarith
    -- sigma_type2_same_rank: hleft for i ≤ m - 2, hright for i ≥ m + 2, hwindow on the gap
    obtain ⟨hleft, hright, hwindow⟩ :=
      Sigma.sigma_type2_same_rank g₁.type hε hg₁_ge2
    have hZ_split : ∀ i, Sigma.sigma Z.val i =
        Sigma.sigma (Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2).val i +
        Sigma.sigma rest.val i := fun i => by
      change Sigma.sigma
        (Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2 + rest : Variety.Pi).val i = _
      simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
    have hX_split : ∀ i, Sigma.sigma X.1.val i =
        Sigma.sigma (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2).val i +
        Sigma.sigma rest.val i := fun i => by
      have hval : X.1.val =
          (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2).val + rest.val := by
        simpa [AddSubmonoid.coe_add] using congrArg Subtype.val hdecomp
      simp only [hval, Sigma.sigma, iterate_map_add, map_add]
    refine ⟨Z, hstep, ?_⟩
    change Z.val ≤ Y.1.val
    rw [le_iff_dominates]
    intro i
    change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
    have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
      le_iff_dominates.mp hXY.le i
    by_cases hi1 : i ≤ g₁.rank - 2
    · -- Left of window
      rw [hZ_split, ← hleft i hi1, ← hX_split]; exact hXY_i
    · by_cases hi2 : g₁.rank + 2 ≤ i
      · -- Right of window
        rw [hZ_split, ← hright i hi2, ← hX_split]; exact hXY_i
      · -- Window: i ∈ {g₁.rank - 1, g₁.rank, g₁.rank + 1}
        have hi_range : i = g₁.rank - 1 ∨ i = g₁.rank ∨ i = g₁.rank + 1 := by omega
        by_cases heven : Even g₁.rank
        · -- g₁.rank is even: g₁.type = .Negative
          have hc1_ci_rank : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 ≤
              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
            Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
          have hd0_di_rank : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 :=
            snd_gap_le_of_dominates X Y hXY.le
          have hb0_bi : ∀ j, 1 ≤ j → j ≤ g₁.rank →
              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (j - 1)).2 =
              (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 j).1 :=
            fun j hj1 hj2 => x_actual_negative_prefix_equalities
              (fun g' _ hg'_pos =>
                hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne')) hj1 hj2
          have hb0_bi_rank := hb0_bi g₁.rank (by omega) le_rfl
          have hc1_ci_rank1 : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 ≤
              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
            Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
          have hd0_di_rank1 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 ≤
              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 :=
            snd_gap_le_of_dominates X Y hXY.le
          have hb0_bi_rank1 := hb0_bi (g₁.rank - 1) (by omega) (by omega)
          rw [show g₁.rank - 1 - 1 = g₁.rank - 2 from by omega] at hb0_bi_rank1
          have ha_lt_c_rank : (Sigma.sigma X.1 g₁.rank).1 <
              (Sigma.sigma Y.1 g₁.rank).1 :=
            fst_lt_of_gap_chain X Y hXY.le hstrict hc1_ci_rank hd0_di_rank hb0_bi_rank
          have ha_lt_c_rank1 : (Sigma.sigma X.1 (g₁.rank - 1)).1 <
              (Sigma.sigma Y.1 (g₁.rank - 1)).1 :=
            fst_lt_of_gap_chain X Y hXY.le hstrict hc1_ci_rank1 hd0_di_rank1 hb0_bi_rank1
          have hd2_c1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
              (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
            by_cases hrank2 : g₁.rank = 2
            · simp [hrank2]
            · have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 (show g₁.rank - 1 ≥ 2 by omega)
              rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
          have hd2_di1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
            hd2_c1_rank1.trans hc1_ci_rank1
          have hg₁_type : g₁.type = .Negative := gene_type_eq_negative_of_even heven hε hε₁
          -- all min-rank genes are Negative (else a pos-neg pair of equal rank exists)
          have no_neg_gene_rank_g : ∀ g' ∈ X.1.val.support,
              g'.rank = g₁.rank → g'.type = .Negative := by
            intro g' hg'_supp hg'_rank
            have hg'_ne_np : g'.type ≠ .NonPolarized :=
              IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
            have hg'_ne_pos : g'.type ≠ .Positive := fun hg'_pos => hXpn
              ⟨g', g₁, hg'_rank, hg'_pos, hg₁_type,
                Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp), hXg₁pos⟩
            cases ht' : g'.type with
            | Positive => exact absurd ht' hg'_ne_pos
            | Negative => rfl
            | NonPolarized => exact absurd ht' hg'_ne_np
          have grank_bounds : g₁.rank ≥ 2 := hg₁_ge2
          have hb0_b2_rank1 : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
              (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 g₁.rank).2 := by
            have h := Sigma.b0_eq_b2_negative g₁.rank grank_bounds hg₁min
              no_neg_gene_rank_g (show g₁.rank - 2 ≤ g₁.rank - 1 by omega)
            rwa [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h
          have hb0_b2_rank : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 =
              (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 (g₁.rank + 1)).2 := by
            have h := Sigma.b0_eq_b2_negative g₁.rank grank_bounds hg₁min
              no_neg_gene_rank_g le_rfl
            rwa [show g₁.rank - 1 + 2 = g₁.rank + 1 from by omega] at h
          have hd2_c1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank + 1)).2 ≤
              (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 :=
            Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 hg₁_ge2
          have hd2_di1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank + 1)).2 ≤
              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
            hd2_c1_rank.trans hc1_ci_rank
          have hb_lt_d_rank : (Sigma.sigma X.1 g₁.rank).2 <
              (Sigma.sigma Y.1 g₁.rank).2 :=
            snd_lt_of_gap_chain X Y hd2_gt_b2 hd2_di1_rank1 hd0_di_rank1 hb0_b2_rank1
          have hb_lt_d_rank1 : (Sigma.sigma X.1 (g₁.rank + 1)).2 <
              (Sigma.sigma Y.1 (g₁.rank + 1)).2 :=
            snd_lt_of_gap_chain X Y hd2_gt_b2 hd2_di1_rank hd0_di_rank hb0_b2_rank
          have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
              if i = g₁.rank then (1, 1)
              else if i = g₁.rank - 1 then (1, 0)
              else (0, 1) := by
            rw [hZ_split, hX_split, add_sub_add_right_eq_sub]
            have hibounds : g₁.rank - 1 ≤ i ∧ i ≤ g₁.rank + 1 := by
              rcases hi_range with rfl | rfl | rfl <;> omega
            rw [hwindow i hibounds.1 hibounds.2]
            simp [hg₁_type]
          rcases hi_range with hi | hi | hi
          · subst hi
            have hZX_eq : Sigma.sigma Z.val (g₁.rank - 1) =
                Sigma.sigma X.1.val (g₁.rank - 1) + (1, 0) :=
              sigma_eq_add_of_sub_eq <| by
                simpa [show g₁.rank - 1 ≠ g₁.rank from by omega] using hZX_diff
            rw [hZX_eq]
            exact ⟨sigma_fst_add_one_le_of_lt X.1.2 Y.1.2 (g₁.rank - 1) ha_lt_c_rank1,
              by simpa using hXY_i.2⟩
          · subst hi
            have hZX_eq : Sigma.sigma Z.val g₁.rank = Sigma.sigma X.1.val g₁.rank + (1, 1) :=
              sigma_eq_add_of_sub_eq <| by simpa using hZX_diff
            rw [hZX_eq]
            exact ⟨sigma_fst_add_one_le_of_lt X.1.2 Y.1.2 g₁.rank ha_lt_c_rank,
              sigma_snd_add_one_le_of_lt X.1.2 Y.1.2 g₁.rank hb_lt_d_rank⟩
          · subst hi
            have hZX_eq : Sigma.sigma Z.val (g₁.rank + 1) =
                Sigma.sigma X.1.val (g₁.rank + 1) + (0, 1) :=
              sigma_eq_add_of_sub_eq <| by
                simpa [show g₁.rank + 1 ≠ g₁.rank from by omega,
                  show g₁.rank + 1 ≠ g₁.rank - 1 from by omega] using hZX_diff
            rw [hZX_eq]
            refine ⟨by simpa using hXY_i.1, ?_⟩
            exact sigma_snd_add_one_le_of_lt X.1.2 Y.1.2 (g₁.rank + 1) hb_lt_d_rank1
        · -- g₁.rank is odd
          have hodd : Odd g₁.rank := Nat.not_even_iff_odd.mp heven
          have hg₁_ge3 : 3 ≤ g₁.rank := by
            obtain ⟨k, hk⟩ := hodd; omega
          have all_rel :
              (Sigma.sigma X.1 g₁.rank).1       < (Sigma.sigma Y.1 g₁.rank).1       ∧
              (Sigma.sigma X.1 (g₁.rank + 1)).1 < (Sigma.sigma Y.1 (g₁.rank + 1)).1 ∧
              (Sigma.sigma X.1 g₁.rank).2       < (Sigma.sigma Y.1 g₁.rank).2       ∧
              (Sigma.sigma X.1 (g₁.rank - 1)).2 < (Sigma.sigma Y.1 (g₁.rank - 1)).2 := by
            have hc1_ci_rank : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
              Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
            have hd0_di_rank : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 :=
              snd_gap_le_of_dominates X Y hXY.le
            have hb0_bi : ∀ j, 1 ≤ j → j ≤ g₁.rank + 1 →
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (j - 1)).2 =
                (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 j).1 := by
              intro j hj1 hj2
              by_cases hj : j = 1
              · subst hj; simp
              · have hg₁_type : g₁.type = .Positive := gene_type_eq_positive_of_odd hodd hε hε₁
                have no_neg_gene_rank_g : ∀ g' ∈ X.1.val.support,
                    g'.rank = g₁.rank → g'.type = .Positive := by
                  intro g' hg'_supp hg'_rank
                  have hg'_ne_np : g'.type ≠ .NonPolarized :=
                    IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
                  have hg'_ne_neg : g'.type ≠ .Negative := fun hg'_neg => hXpn
                    ⟨g₁, g', hg'_rank.symm, hg₁_type, hg'_neg, hXg₁pos,
                      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp)⟩
                  cases ht' : g'.type with
                  | Positive => rfl
                  | Negative => exact absurd ht' hg'_ne_neg
                  | NonPolarized => exact absurd ht' hg'_ne_np
                have h := Sigma.b0_bi_eq_a1_ai1 X.1.val X.1.2 (j - 1)
                  (fun g hg_supp _ => no_neg_gene_rank_g g hg_supp
                    (by have := hg₁min g hg_supp; omega))
                rwa [Nat.sub_add_cancel hj1] at h
            have hb0_bi_rank := hb0_bi g₁.rank (by omega) (by omega)
            have ha_lt_c_rank : (Sigma.sigma X.1 g₁.rank).1 <
                (Sigma.sigma Y.1 g₁.rank).1 :=
              fst_lt_of_gap_chain X Y hXY.le hstrict hc1_ci_rank hd0_di_rank hb0_bi_rank
            have hc1_ci_rank1 : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank + 1)).1 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 g₁.rank).2 :=
              Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
            have hd0_di_rank1 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 g₁.rank).2 :=
              snd_gap_le_of_dominates X Y hXY.le
            have hb0_bi_rank1 := hb0_bi (g₁.rank + 1) (by omega) le_rfl
            rw [show g₁.rank + 1 - 1 = g₁.rank from by omega] at hb0_bi_rank1
            have ha_lt_c_rank1 : (Sigma.sigma X.1 (g₁.rank + 1)).1 <
                (Sigma.sigma Y.1 (g₁.rank + 1)).1 :=
              fst_lt_of_gap_chain X Y hXY.le hstrict hc1_ci_rank1 hd0_di_rank1 hb0_bi_rank1
            have hd2_c1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
              have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 (show g₁.rank - 1 ≥ 2 by omega)
              rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
            have hd2_c1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 2)).1 := by
              by_cases hrank3 : g₁.rank = 3
              · simp [hrank3]
              · obtain ⟨k, hk⟩ := hodd
                have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 (show g₁.rank - 2 ≥ 2 by omega)
                rwa [show g₁.rank - 2 + 1 = g₁.rank - 1 from by omega] at this
            -- chain to d₀ - d_{rank-2}
            have hd2_di1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
              hd2_c1_rank.trans (Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega))
            -- chain to d₀ - d_{rank-3}
            have hd2_di1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 3)).2 :=
              hd2_c1_rank1.trans (Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2
                (by obtain ⟨k, hk⟩ := hodd; omega))
            have hd0_di_rank2 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 ≤
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 :=
              snd_gap_le_of_dominates X Y hXY.le
            have hd0_di_rank3 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 3)).2 ≤
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 3)).2 :=
              snd_gap_le_of_dominates X Y hXY.le
            have hb0_b2_rank : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
                (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 g₁.rank).2 := by
              have h := Sigma.b0_eq_b2_positive g₁.rank hg₁min le_rfl
              rwa [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h
            have hb0_b2_rank1 : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 3)).2 =
                (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
              have h := Sigma.b0_eq_b2_positive g₁.rank hg₁min
                (show g₁.rank - 3 ≤ g₁.rank - 2 by omega)
              rwa [show g₁.rank - 3 + 2 = g₁.rank - 1 from by
                obtain ⟨k, hk⟩ := hodd; omega] at h
            have hb_lt_d_rank : (Sigma.sigma X.1 g₁.rank).2 <
                (Sigma.sigma Y.1 g₁.rank).2 :=
              snd_lt_of_gap_chain X Y hd2_gt_b2 hd2_di1_rank hd0_di_rank2 hb0_b2_rank
            have hb_lt_d_rank1 : (Sigma.sigma X.1 (g₁.rank - 1)).2 <
                (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
              snd_lt_of_gap_chain X Y hd2_gt_b2 hd2_di1_rank1 hd0_di_rank3 hb0_b2_rank1
            exact ⟨ha_lt_c_rank, ha_lt_c_rank1, hb_lt_d_rank, hb_lt_d_rank1⟩
          obtain ⟨ha_lt_c_rank, ha_lt_c_rank1, hb_lt_d_rank, hb_lt_d_rank1⟩ := all_rel
          have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
              if i = g₁.rank then (1, 1)
              else if i = g₁.rank - 1 then (0, 1)
              else (1, 0) := by
            rw [hZ_split, hX_split, add_sub_add_right_eq_sub]
            have hibounds : g₁.rank - 1 ≤ i ∧ i ≤ g₁.rank + 1 := by
              rcases hi_range with rfl | rfl | rfl <;> omega
            rw [hwindow i hibounds.1 hibounds.2]
            have htype_pos : g₁.type = .Positive := gene_type_eq_positive_of_odd hodd hε hε₁
            simp [htype_pos]
          rcases hi_range with hi | hi | hi
          · subst hi
            have hZX_eq : Sigma.sigma Z.val (g₁.rank - 1) =
                Sigma.sigma X.1.val (g₁.rank - 1) + (0, 1) :=
              sigma_eq_add_of_sub_eq <| by
                simpa [show g₁.rank - 1 ≠ g₁.rank from by omega] using hZX_diff
            rw [hZX_eq]
            refine ⟨by simpa using hXY_i.1, ?_⟩
            exact sigma_snd_add_one_le_of_lt X.1.2 Y.1.2 (g₁.rank - 1) hb_lt_d_rank1
          · subst hi
            have hZX_eq : Sigma.sigma Z.val g₁.rank = Sigma.sigma X.1.val g₁.rank + (1, 1) :=
              sigma_eq_add_of_sub_eq <| by simpa using hZX_diff
            rw [hZX_eq]
            exact ⟨sigma_fst_add_one_le_of_lt X.1.2 Y.1.2 g₁.rank ha_lt_c_rank,
              sigma_snd_add_one_le_of_lt X.1.2 Y.1.2 g₁.rank hb_lt_d_rank⟩
          · subst hi
            have hZX_eq : Sigma.sigma Z.val (g₁.rank + 1) =
                Sigma.sigma X.1.val (g₁.rank + 1) + (1, 0) :=
              sigma_eq_add_of_sub_eq <| by
                simpa [show g₁.rank + 1 ≠ g₁.rank from by omega,
                  show g₁.rank + 1 ≠ g₁.rank - 1 from by omega] using hZX_diff
            rw [hZX_eq]
            exact ⟨sigma_fst_add_one_le_of_lt X.1.2 Y.1.2 (g₁.rank + 1) ha_lt_c_rank1,
              by simpa using hXY_i.2⟩

end Pi
