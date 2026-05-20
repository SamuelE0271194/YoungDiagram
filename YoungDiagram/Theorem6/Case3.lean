import YoungDiagram.Theorem6.Prelim

open Variety hiding prime prime_def
open Chromosome

set_option maxHeartbeats 900000 in
-- Case 3 is the type-2 mutation window check with several parity subcases,
-- so keep the heartbeat increase scoped to this declaration.
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
    -- Case 3: 2 * g₁ ≤ X (g₁ appears with multiplicity ≥ 2)
    -- g₁ is polarized (not NonPolarized)
    have hε : g₁.type ≠ .NonPolarized :=
      IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
    -- Gene.ofRank g₁.rank g₁.type = Finsupp.single g₁ 1
    have hg₁_ofRank : Gene.ofRank g₁.rank g₁.type = Finsupp.single g₁ 1 :=
      @Gene.ofRank_eq_gene g₁
    -- Pi.X2 (with m = n = g₁.rank) equals Finsupp.single g₁ 2
    have hsrc_val : (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 : Chromosome) =
        Finsupp.single g₁ 2 := by
      simp only [Pi.X2_eq, hg₁_ofRank]
      ext g; simp [Finsupp.single_apply]; split_ifs with heq <;> simp
    -- Pi.X2 ≤ X.1.val pointwise
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
    -- X.1 decomposes as Pi.X2 + rest
    have hdecomp : X.1 = Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 + rest :=
      Subtype.val_injective
        (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
    -- Z is the type2 mutation result: Pi.Y2 + rest
    let Z : Pi := Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2 + rest
    -- Construct the Pi-step
    have hstep : Pi.Step X.1 Z :=
      hdecomp.symm ▸ Pi.Step.mk
        (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2)
        (Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2)
        rest
        (Pi.Primitive.type2 g₁.type hε (le_refl g₁.rank) hg₁_ge2)
    -- b₁ - b₂ = a₀ - a₁
    have hb12_eq : (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 =
        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
      -- g₁.type is in the Positive family (not Negative by hε₁,
       --not NonPolarized by polarization)
      have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁
        (Finsupp.mem_support_iff.mpr hXg₁)
      have hg₁_pos_type : g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Positive := by
        simp only [GeneType.negOnePow_smul, GeneType.neg_positive, GeneType.neg_negative]
          at hε₁ ⊢
        split_ifs with heven
        · simp only [if_pos heven] at hε₁
          cases ht : g₁.type with
          | Positive => rfl
          | Negative => exact absurd ht hε₁
          | NonPolarized => exact absurd ht hpol
        · simp only [if_neg heven] at hε₁
          cases ht : g₁.type with
          | Positive => exact absurd ht hε₁
          | Negative => rfl
          | NonPolarized => exact absurd ht hpol
      -- Gene.ofRankAlt g₁.rank Positive = single g₁ 1
      have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Positive = Finsupp.single g₁ 1
          := by
        rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]
        congr 1; exact Gene.ext rfl hg₁_pos_type.symm
      -- Apply x_side_equalities at j = 1 (odd), using g₁ as the minimal Positive-family gene
      have h := x_side_equalities
        (fun g' _ hg'_pos => hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
        (show 1 < g₁.rank from hg₁_ge2)
      simp only [show ¬Even 1 from by norm_num, ↓reduceIte] at h
      exact h
    -- a₀ - a₁ > c₀ - c₁
    have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
      have ha₀ := sigma_zero_fst_eq X Y hXY.le
      linarith
    -- c₀ - c₁ ≥ d₁ - d₂
    have hd12_le : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 ≤
        (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
      have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (2 - 1) Y.1.2
      simp only [show ¬Even (2 - 1 : ℕ) from by norm_num, if_false] at h
      exact h
    -- b₁ ≤ d₁ from X ≤ Y at level 1
    have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
      (le_iff_dominates.mp hXY.le 1).2
    -- b₁ - b₂ > d₁ - d₂: chain hb12_eq > hstrict ≥ hd12_le
    have hb12_gt_d12 : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 <
        (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 := by
      linarith [hb12_eq, hstrict, hd12_le]
    -- d₂ > b₂: from b₁ ≤ d₁ and b₁ - b₂ > d₁ - d₂
    have hd2_gt_b2 : (Sigma.sigma X.1 2).2 < (Sigma.sigma Y.1 2).2 := by
      linarith [hb1_le_d1, hb12_gt_d12]
    -- Extract the three parts of sigma_type2_same_rank:
    -- hleft : sigma(Pi.X2) = sigma(Pi.Y2) for i ≤ m - 2
    -- hright : sigma(Pi.X2) = sigma(Pi.Y2) for i ≥ m + 2
    -- hwindow : the nonzero differences at i = m-1, m, m+1
    obtain ⟨hleft, hright, hwindow⟩ :=
      Sigma.sigma_type2_same_rank g₁.type hε hg₁_ge2
    -- sigma(Z.val) = sigma(Pi.Y2.val) + sigma(rest.val)
    have hZ_split : ∀ i, Sigma.sigma Z.val i =
        Sigma.sigma (Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2).val i +
        Sigma.sigma rest.val i := fun i => by
      change Sigma.sigma
        (Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2 + rest : Variety.Pi).val i = _
      simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
    -- sigma(X.1.val) = sigma(Pi.X2.val) + sigma(rest.val)
    have hX_split : ∀ i, Sigma.sigma X.1.val i =
        Sigma.sigma (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2).val i +
        Sigma.sigma rest.val i := fun i => by
      have hval : X.1.val =
          (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2).val + rest.val := by
        have h := congrArg Subtype.val hdecomp
        simp only [AddSubmonoid.coe_add] at h; exact h
      simp only [hval, Sigma.sigma, iterate_map_add, map_add]
    -- Prove Z ≤ Y.1 by checking each index
    refine ⟨Z, hstep, ?_⟩
    change Z.val ≤ Y.1.val
    rw [le_iff_dominates]
    intro i
    change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
    have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
      le_iff_dominates.mp hXY.le i
    by_cases hi1 : i ≤ g₁.rank - 2
    · -- Left of window: sigma(Pi.Y2) i = sigma(Pi.X2) i, so sigma Z i = sigma X.1 i
      rw [hZ_split, ← hleft i hi1, ← hX_split]; exact hXY_i
    · by_cases hi2 : g₁.rank + 2 ≤ i
      · -- Right of window: sigma(Pi.Y2) i = sigma(Pi.X2) i, so sigma Z i = sigma X.1 i
        rw [hZ_split, ← hright i hi2, ← hX_split]; exact hXY_i
      · -- Window: i ∈ {g₁.rank - 1, g₁.rank, g₁.rank + 1}
        have hi_range : i = g₁.rank - 1 ∨ i = g₁.rank ∨ i = g₁.rank + 1 := by omega
        by_cases heven : Even g₁.rank
        · -- g₁.rank is even
          -- for i = g₁.rank: c₁ - c_i ≤ d₀ - d_{i-1}
          have hc1_ci_rank : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 ≤
            (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
            Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
          -- for i = g₁.rank: d₀ - d_{i-1} ≤ b₀ - b_{i-1}
          have hd0_di_rank : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
            (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
            have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
              sigma_zero_snd_eq X Y hXY.le
            have hbm1_le_dm1 : (Sigma.sigma X.1 (g₁.rank - 1)).2 ≤
                (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
              (le_iff_dominates.mp hXY.le (g₁.rank - 1)).2
            linarith
          -- b₀ - b_{j-1} = a₁ - a_j for all 1 ≤ j ≤ g₁.rank
          have hb0_bi : ∀ j, 1 ≤ j → j ≤ g₁.rank →
              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (j - 1)).2 =
              (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 j).1 :=
            fun j hj1 hj2 => x_actual_negative_prefix_equalities
              (fun g' _ hg'_pos =>
                hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
              hj1 hj2
          -- for i = g₁.rank: b₀ - b_{i-1} = a₁ - a_i
          have hb0_bi_rank := hb0_bi g₁.rank (by omega) (le_refl _)
          -- for i = g₁.rank - 1: c₁ - c_i ≤ d₀ - d_{i-1}
          have hc1_ci_rank1 : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 ≤
            (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
            Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
          -- for i = g₁.rank - 1: d₀ - d_{i-1} ≤ b₀ - b_{i-1}
          have hd0_di_rank1 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 ≤
            (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 := by
            have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
              sigma_zero_snd_eq X Y hXY.le
            have hbm2_le_dm2 : (Sigma.sigma X.1 (g₁.rank - 2)).2 ≤
                (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
              (le_iff_dominates.mp hXY.le (g₁.rank - 2)).2
            linarith
          -- for i = g₁.rank - 1: b₀ - b_{i-1} = a₁ - a_i
          have hb0_bi_rank1 := hb0_bi (g₁.rank - 1) (by omega) (by omega)
          simp only [show g₁.rank - 1 - 1 = g₁.rank - 2 from by omega] at hb0_bi_rank1
          -- a_{g₁.rank} < c_{g₁.rank}
          have ha_lt_c_rank : (Sigma.sigma X.1 g₁.rank).1 <
              (Sigma.sigma Y.1 g₁.rank).1 := by
            have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
              sigma_zero_fst_eq X Y hXY.le
            linarith [hc1_ci_rank, hd0_di_rank, hb0_bi_rank, hstrict]
          -- a_{g₁.rank - 1} < c_{g₁.rank - 1}
          have ha_lt_c_rank1 : (Sigma.sigma X.1 (g₁.rank - 1)).1 <
              (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
            have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
              sigma_zero_fst_eq X Y hXY.le
            linarith [hc1_ci_rank1, hd0_di_rank1, hb0_bi_rank1, hstrict]
          -- for i = g₁.rank - 1: d₂ - d_{i+1} ≤ c₁ - c_i
          have hd2_c1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
              (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
            by_cases hrank2 : g₁.rank = 2
            · simp only [hrank2, sub_self, le_refl]
            · have h : g₁.rank - 1 ≥ 2 := by omega
              have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
              rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
          -- for i = g₁.rank - 1: d₂ - d_{i+1} ≤ d₀ - d_{i-1}
          have hd2_di1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
            hd2_c1_rank1.trans hc1_ci_rank1
          -- g₁.type = .Negative since rank is even and hε₁ rules out .Positive
          have hg₁_type : g₁.type = .Negative := by
            have hne_pos : g₁.type ≠ .Positive := by
              intro h; apply hε₁
              have h_odd : ¬ Even ((g₁.rank : ℤ) - 1) := by
                obtain ⟨r, hr⟩ := heven; intro ⟨k, hk⟩; omega
              simp only [GeneType.negOnePow_smul, GeneType.neg_negative, if_neg h_odd, h]
            cases ht : g₁.type with
            | Positive => exact absurd ht hne_pos
            | Negative => rfl
            | NonPolarized => exact absurd ht hε
          -- all min-rank genes are Negative (else a pos-neg pair of equal rank exists)
          have no_neg_gene_rank_g : ∀ g' ∈ X.1.val.support,
              g'.rank = g₁.rank → g'.type = .Negative := by
            intro g' hg'_supp hg'_rank
            have hg'_ne_np : g'.type ≠ .NonPolarized :=
              IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
            have hg'_ne_pos : g'.type ≠ .Positive := by
              intro hg'_pos
              apply hXpn
              exact ⟨g', g₁, hg'_rank, hg'_pos, hg₁_type,
                     Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp), hXg₁pos⟩
            cases ht' : g'.type with
            | Positive => exact absurd ht' hg'_ne_pos
            | Negative => rfl
            | NonPolarized => exact absurd ht' hg'_ne_np
          have grank_bounds : g₁.rank ≥ 2 := by omega
          -- for i = g₁.rank - 1: b₀ - b_{i-1} = b₂ - b_{i+1}
          have hb0_b2_rank1 : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
              (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 g₁.rank).2 := by
            have h := Sigma.b0_eq_b2_negative g₁.rank grank_bounds hg₁min
              no_neg_gene_rank_g
              (show g₁.rank - 2 ≤ g₁.rank - 1 from by omega)
            simp only [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h
            exact h
          -- for i = g₁.rank: b₀ - b_{i-1} = b₂ - b_{i+1}
          have hb0_b2_rank : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 =
              (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 (g₁.rank + 1)).2 := by
            have h := Sigma.b0_eq_b2_negative g₁.rank grank_bounds hg₁min
              no_neg_gene_rank_g
              (show g₁.rank - 1 ≤ g₁.rank - 1 from le_refl _)
            simp only [show g₁.rank - 1 + 2 = g₁.rank + 1 from by omega] at h
            exact h
          -- for i = g₁.rank: d₂ - d_{i+1} ≤ c₁ - c_i
          have hd2_c1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank + 1)).2 ≤
              (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 :=
            Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 hg₁_ge2
          -- for i = g₁.rank: d₂ - d_{i+1} ≤ d₀ - d_{i-1}
          have hd2_di1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank + 1)).2 ≤
              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
            hd2_c1_rank.trans hc1_ci_rank
          -- b_{g₁.rank} < d_{g₁.rank}
          have hb_lt_d_rank : (Sigma.sigma X.1 g₁.rank).2 <
              (Sigma.sigma Y.1 g₁.rank).2 := by
            linarith [hd2_di1_rank1, hd0_di_rank1, hb0_b2_rank1, hd2_gt_b2]
          -- b_{g₁.rank + 1} < d_{g₁.rank + 1}
          have hb_lt_d_rank1 : (Sigma.sigma X.1 (g₁.rank + 1)).2 <
              (Sigma.sigma Y.1 (g₁.rank + 1)).2 := by
            linarith [hd2_di1_rank, hd0_di_rank, hb0_b2_rank, hd2_gt_b2]
          -- sigma Z i - sigma X.1 i equals the window difference from sigma_type2_same_rank
          have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
              if i = g₁.rank then (1, 1)
              else if i = g₁.rank - 1 then (1, 0)
              else (0, 1) := by
            -- Rewrite both sides using the Pi.Y2/Pi.X2 + rest decomposition;
            -- the rest terms are equal so they cancel
            rw [hZ_split, hX_split, add_sub_add_right_eq_sub]
            -- Derive index bounds from hi_range to apply hwindow
            have hibounds : g₁.rank - 1 ≤ i ∧ i ≤ g₁.rank + 1 := by
              rcases hi_range with rfl | rfl | rfl <;> omega
            -- Apply the window difference formula from sigma_type2_same_rank
            rw [hwindow i hibounds.1 hibounds.2]
            -- g₁.type = .Negative: rank is even so ↑g₁.rank - 1 is odd,
            -- and hε₁ (type ≠ negOnePow(rank-1)•Negative) then gives type ≠ Positive
            have htype_neg : g₁.type ≠ .Positive := by
              intro h
              apply hε₁
              have h_odd : ¬ Even ((g₁.rank : ℤ) - 1) := by
                simp [heven]
              simp only [GeneType.negOnePow_smul, GeneType.neg_negative,
                          if_neg h_odd, h]
            simp [if_neg htype_neg]
          rcases hi_range with hi | hi | hi
          · -- i = g₁.rank - 1
            subst hi
            have hZX_diff' : Sigma.sigma Z.val (g₁.rank - 1) -
                            Sigma.sigma X.1.val (g₁.rank - 1) = (1, 0) := by
              simpa [show g₁.rank - 1 ≠ g₁.rank from by omega] using hZX_diff
            have hZX_diff' : Sigma.sigma Z.val (g₁.rank - 1) =
                            Sigma.sigma X.1.val (g₁.rank - 1) + (1, 0) := by
              have h := hZX_diff'; rw [← h]; ring
            rw [hZX_diff']
            constructor
            · -- .1: (sigma X).1 + 1 ≤ (sigma Y).1 by ha_lt_c_rank1 and integrality
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val (g₁.rank - 1) X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val (g₁.rank - 1) Y.1.2
              rw [hnX, hnY] at ha_lt_c_rank1 ⊢
              simp only [Prod.fst_add] at ha_lt_c_rank1 ⊢
              exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank1)
            · -- .2: (sigma X).2 + 0 ≤ (sigma Y).2 from hXY_i
              simp only [Prod.snd_add]
              linarith [hXY_i.2]
          · -- i = g₁.rank
            subst hi
            have hZX_diff' : Sigma.sigma Z.val g₁.rank -
                             Sigma.sigma X.1.val g₁.rank = (1, 1) := by
              simpa using hZX_diff
            have hZX_diff' : Sigma.sigma Z.val g₁.rank =
                             Sigma.sigma X.1.val g₁.rank + (1, 1) := by
              have h := hZX_diff'; rw [← h]; ring
            rw [hZX_diff']
            constructor
            · -- .1: (sigma X).1 + 1 ≤ (sigma Y).1 by ha_lt_c_rank and integrality
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val g₁.rank X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val g₁.rank Y.1.2
              rw [hnX, hnY] at ha_lt_c_rank ⊢
              simp only [Prod.fst_add] at ha_lt_c_rank ⊢
              exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank)
            · -- .2: (sigma X).2 + 1 ≤ (sigma Y).2 by hb_lt_d_rank and integrality
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val g₁.rank X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val g₁.rank Y.1.2
              rw [hnX, hnY] at hb_lt_d_rank ⊢
              simp only [Prod.snd_add] at hb_lt_d_rank ⊢
              exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank)
          · -- i = g₁.rank + 1
            subst hi
            have hZX_diff' : Sigma.sigma Z.val (g₁.rank + 1) -
                             Sigma.sigma X.1.val (g₁.rank + 1) = (0, 1) := by
              simpa [show g₁.rank + 1 ≠ g₁.rank from by omega,
                     show g₁.rank + 1 ≠ g₁.rank - 1 from by omega] using hZX_diff
            have hZX_diff' : Sigma.sigma Z.val (g₁.rank + 1) =
                             Sigma.sigma X.1.val (g₁.rank + 1) + (0, 1) := by
              have h := hZX_diff'; rw [← h]; ring
            rw [hZX_diff']
            constructor
            · -- .1: (sigma X).1 + 0 ≤ (sigma Y).1 from hXY_i
              simp only [Prod.fst_add]
              linarith [hXY_i.1]
            · -- .2: (sigma X).2 + 1 ≤ (sigma Y).2 by hb_lt_d_rank1 and integrality
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val (g₁.rank + 1) X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val (g₁.rank + 1) Y.1.2
              rw [hnX, hnY] at hb_lt_d_rank1 ⊢
              simp only [Prod.snd_add] at hb_lt_d_rank1 ⊢
              exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank1)
        · -- g₁.rank is odd
          have all_rel :
              (Sigma.sigma X.1 g₁.rank).1       < (Sigma.sigma Y.1 g₁.rank).1       ∧
              (Sigma.sigma X.1 (g₁.rank + 1)).1 < (Sigma.sigma Y.1 (g₁.rank + 1)).1 ∧
              (Sigma.sigma X.1 g₁.rank).2       < (Sigma.sigma Y.1 g₁.rank).2       ∧
              (Sigma.sigma X.1 (g₁.rank - 1)).2 < (Sigma.sigma Y.1 (g₁.rank - 1)).2 := by
            -- Step 1: auxiliary inequalities for the .1 component
            -- for i = g₁.rank: c₁ - c_{rank} ≤ d₀ - d_{rank-1}
            have hc1_ci_rank : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
              Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
            -- for i = g₁.rank: d₀ - d_{rank-1} ≤ b₀ - b_{rank-1}
            have hd0_di_rank : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
              have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                sigma_zero_snd_eq X Y hXY.le
              have hbm1_le_dm1 : (Sigma.sigma X.1 (g₁.rank - 1)).2 ≤
                  (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                (le_iff_dominates.mp hXY.le (g₁.rank - 1)).2
              linarith
            -- b₀ - b_{j-1} = a₁ - a_j for all 1 ≤ j ≤ g₁.rank + 1
            have hb0_bi : ∀ j, 1 ≤ j → j ≤ g₁.rank + 1 →
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (j - 1)).2 =
                (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 j).1 := by
              intro j hj1 hj2
              by_cases hj : j = 1
              · subst hj; simp
              · have hodd : Odd g₁.rank := Nat.not_even_iff_odd.mp heven
                have hg₁_type : g₁.type = .Positive := by
                  have h_even : Even ((g₁.rank : ℤ) - 1) := by simp [hodd]
                  have hne_neg : g₁.type ≠ .Negative := by
                    intro h; apply hε₁
                    simp only [GeneType.negOnePow_smul, if_pos h_even, h]
                  cases ht : g₁.type with
                  | Positive => rfl
                  | Negative => exact absurd ht hne_neg
                  | NonPolarized => exact absurd ht hε
                have no_neg_gene_rank_g : ∀g' ∈ X.1.val.support,
                    g'.rank = g₁.rank → g'.type = .Positive := by
                  intro g' hg'_supp hg'_rank
                  have hg'_ne_np : g'.type ≠ .NonPolarized :=
                    IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
                  have hg'_ne_neg : g'.type ≠ .Negative := by
                    intro hg'_neg
                    apply hXpn
                    exact ⟨g₁, g', hg'_rank.symm, hg₁_type, hg'_neg, hXg₁pos,
                           Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp)⟩
                  cases ht' : g'.type with
                  | Positive => rfl
                  | Negative => exact absurd ht' hg'_ne_neg
                  | NonPolarized => exact absurd ht' hg'_ne_np
                have h := Sigma.b0_bi_eq_a1_ai1 X.1.val X.1.2 (j - 1)
                    (fun g hg_supp hrank_le => by
                      have hg_rank_ge := hg₁min g hg_supp
                      have hg_rank_eq : g.rank = g₁.rank := by omega
                      exact no_neg_gene_rank_g g hg_supp hg_rank_eq)
                rwa [Nat.sub_add_cancel hj1] at h
            -- for j = g₁.rank: b₀ - b_{rank-1} = a₁ - a_{rank}
            have hb0_bi_rank := hb0_bi g₁.rank (by omega) (by omega)
            -- a_{g₁.rank} < c_{g₁.rank}
            have ha_lt_c_rank : (Sigma.sigma X.1 g₁.rank).1 <
                (Sigma.sigma Y.1 g₁.rank).1 := by
              have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                sigma_zero_fst_eq X Y hXY.le
              linarith [hc1_ci_rank, hd0_di_rank, hb0_bi_rank, hstrict]
            -- for i = g₁.rank + 1: c₁ - c_{rank+1} ≤ d₀ - d_{rank}
            have hc1_ci_rank1 : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank + 1)).1 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 g₁.rank).2 :=
              Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
            -- for i = g₁.rank + 1: d₀ - d_{rank} ≤ b₀ - b_{rank}
            have hd0_di_rank1 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 g₁.rank).2 := by
              have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                sigma_zero_snd_eq X Y hXY.le
              have hb_le_d : (Sigma.sigma X.1 g₁.rank).2 ≤
                  (Sigma.sigma Y.1 g₁.rank).2 :=
                (le_iff_dominates.mp hXY.le g₁.rank).2
              linarith
            -- for j = g₁.rank + 1: b₀ - b_{rank} = a₁ - a_{rank+1}
            have hb0_bi_rank1 := hb0_bi (g₁.rank + 1) (by omega) (le_refl _)
            simp only [show g₁.rank + 1 - 1 = g₁.rank from by omega] at hb0_bi_rank1
            -- a_{g₁.rank + 1} < c_{g₁.rank + 1}
            have ha_lt_c_rank1 : (Sigma.sigma X.1 (g₁.rank + 1)).1 <
                (Sigma.sigma Y.1 (g₁.rank + 1)).1 := by
              have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                sigma_zero_fst_eq X Y hXY.le
              linarith [hc1_ci_rank1, hd0_di_rank1, hb0_bi_rank1, hstrict]
            -- Step 2: auxiliary inequalities for the .2 component
            -- d₂ - d_{rank} ≤ c₁ - c_{rank-1}  (from b2_bi_2_le_a1_ai at rank-1)
            have hd2_c1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
              have h : g₁.rank - 1 ≥ 2 := by
                rcases Nat.even_or_odd g₁.rank with hev | ⟨k, hk⟩
                · exact absurd hev heven
                · omega
              have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
              rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
            -- d₂ - d_{rank-1} ≤ c₁ - c_{rank-2}  (from b2_bi_2_le_a1_ai at rank-2)
            have hd2_c1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 2)).1 := by
              by_cases hrank3 : g₁.rank = 3
              · simp [hrank3]
              · have h : g₁.rank - 2 ≥ 2 := by
                  rcases Nat.even_or_odd g₁.rank with hev | ⟨k, hk⟩
                  · exact absurd hev heven
                  · omega
                have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
                rwa [show g₁.rank - 2 + 1 = g₁.rank - 1 from by omega] at this
            -- chain to d₀ - d_{rank-2}
            have hd2_di1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
              hd2_c1_rank.trans (Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega))
            -- chain to d₀ - d_{rank-3}
            have hd2_di1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 3)).2 :=
              hd2_c1_rank1.trans (Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by
                rcases Nat.even_or_odd g₁.rank with hev | ⟨k, hk⟩
                · exact absurd hev heven
                · omega))
            -- b₀ - b_{rank-2} = b₂ - b_{rank}
            have hb0_b2_rank : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
                (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 g₁.rank).2 := by
              have h := Sigma.b0_eq_b2_positive g₁.rank hg₁min
                (show g₁.rank - 2 ≤ g₁.rank - 2 from by omega)
              simp only [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h
              exact h
            -- b₀ - b_{rank-3} = b₂ - b_{rank-1}
            have hb0_b2_rank1 : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 3)).2 =
                (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
              have h := Sigma.b0_eq_b2_positive g₁.rank hg₁min
                (show g₁.rank - 3 ≤ g₁.rank - 2 from by omega)
              simp only [show g₁.rank - 3 + 2 = g₁.rank - 1 from by
                rcases Nat.even_or_odd g₁.rank with hev | ⟨k, hk⟩
                · exact absurd hev heven
                · omega] at h
              exact h
            -- b_{rank} < d_{rank}
            have hb_lt_d_rank : (Sigma.sigma X.1 g₁.rank).2 <
                (Sigma.sigma Y.1 g₁.rank).2 := by
              have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                sigma_zero_snd_eq X Y hXY.le
              have hb_le_d : (Sigma.sigma X.1 (g₁.rank - 2)).2 ≤
                  (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                (le_iff_dominates.mp hXY.le (g₁.rank - 2)).2
              linarith [hd2_di1_rank, hb0_b2_rank, hd2_gt_b2]
            -- b_{rank-1} < d_{rank-1}
            have hb_lt_d_rank1 : (Sigma.sigma X.1 (g₁.rank - 1)).2 <
                (Sigma.sigma Y.1 (g₁.rank - 1)).2 := by
              have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                sigma_zero_snd_eq X Y hXY.le
              have hb_le_d : (Sigma.sigma X.1 (g₁.rank - 3)).2 ≤
                  (Sigma.sigma Y.1 (g₁.rank - 3)).2 :=
                (le_iff_dominates.mp hXY.le (g₁.rank - 3)).2
              linarith [hd2_di1_rank1, hb0_b2_rank1, hd2_gt_b2]
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
            have htype_pos : g₁.type = .Positive := by
              have h_even : Even ((g₁.rank : ℤ) - 1) := by
                have : Odd g₁.rank := by simp_all
                simp [this]
              have hne_neg : g₁.type ≠ .Negative := by
                intro h
                apply hε₁
                simp only [GeneType.negOnePow_smul, if_pos h_even, h]
              cases htype : g₁.type with
              | Positive => rfl
              | Negative => exact absurd htype hne_neg
              | NonPolarized => exact absurd htype hε
            simp [htype_pos]
          rcases hi_range with hi | hi | hi
          · -- i = g₁.rank - 1, diff = (0, 1)
            subst hi
            have hZX_diff' : Sigma.sigma Z.val (g₁.rank - 1) -
                             Sigma.sigma X.1.val (g₁.rank - 1) = (0, 1) := by
              simpa [show g₁.rank - 1 ≠ g₁.rank from by omega] using hZX_diff
            have hZX_diff' : Sigma.sigma Z.val (g₁.rank - 1) =
                             Sigma.sigma X.1.val (g₁.rank - 1) + (0, 1) := by
              have h := hZX_diff'; rw [← h]; ring
            rw [hZX_diff']
            constructor
            · -- .1: (sigma X).1 + 0 ≤ (sigma Y).1 from hXY_i
              simp only [Prod.fst_add]
              linarith [hXY_i.1]
            · -- .2: (sigma X).2 + 1 ≤ (sigma Y).2 by hb_lt_d_rank1 and integrality
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val (g₁.rank - 1) X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val (g₁.rank - 1) Y.1.2
              rw [hnX, hnY] at hb_lt_d_rank1 ⊢
              simp only [Prod.snd_add] at hb_lt_d_rank1 ⊢
              exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank1)
          · -- i = g₁.rank, diff = (1, 1)
            subst hi
            have hZX_diff' : Sigma.sigma Z.val g₁.rank -
                             Sigma.sigma X.1.val g₁.rank = (1, 1) := by
              simpa using hZX_diff
            have hZX_diff' : Sigma.sigma Z.val g₁.rank =
                             Sigma.sigma X.1.val g₁.rank + (1, 1) := by
              have h := hZX_diff'; rw [← h]; ring
            rw [hZX_diff']
            constructor
            · -- .1: (sigma X).1 + 1 ≤ (sigma Y).1 by ha_lt_c_rank and integrality
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val g₁.rank X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val g₁.rank Y.1.2
              rw [hnX, hnY] at ha_lt_c_rank ⊢
              simp only [Prod.fst_add] at ha_lt_c_rank ⊢
              exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank)
            · -- .2: (sigma X).2 + 1 ≤ (sigma Y).2 by hb_lt_d_rank and integrality
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val g₁.rank X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val g₁.rank Y.1.2
              rw [hnX, hnY] at hb_lt_d_rank ⊢
              simp only [Prod.snd_add] at hb_lt_d_rank ⊢
              exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank)
          · -- i = g₁.rank + 1, diff = (1, 0)
            subst hi
            have hZX_diff' : Sigma.sigma Z.val (g₁.rank + 1) -
                             Sigma.sigma X.1.val (g₁.rank + 1) = (1, 0) := by
              simpa [show g₁.rank + 1 ≠ g₁.rank from by omega,
                     show g₁.rank + 1 ≠ g₁.rank - 1 from by omega] using hZX_diff
            have hZX_diff' : Sigma.sigma Z.val (g₁.rank + 1) =
                             Sigma.sigma X.1.val (g₁.rank + 1) + (1, 0) := by
              have h := hZX_diff'
              rw [← h]; ring
            rw [hZX_diff']
            constructor
            · -- .1: (sigma X).1 + 1 ≤ (sigma Y).1 by ha_lt_c_rank1 and integrality
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val (g₁.rank + 1) X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val (g₁.rank + 1) Y.1.2
              rw [hnX, hnY] at ha_lt_c_rank1 ⊢
              simp only [Prod.fst_add] at ha_lt_c_rank1 ⊢
              exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank1)
            · -- .2: (sigma X).2 + 0 ≤ (sigma Y).2 from hXY_i
              simp only [Prod.snd_add]
              linarith [hXY_i.2]
