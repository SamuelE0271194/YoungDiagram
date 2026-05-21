import YoungDiagram.Theorem6.Prelim

open Variety hiding prime prime_def
open Chromosome

set_option linter.flexible false in
lemma exists_mutation_le_case4a
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
    (hε₂ : g₂.type = -g₁.type) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  -- Case 4a: g₂.type = -g₁.type (opposite type families)
  -- Mutation: Pi.Primitive.type1 with ε = g₁.type, m = g₁.rank, k = g₂.rank
  -- Source (Pi.X1): Gene.ofRank m ε + Gene.ofRank k (-ε) = single g₁ 1 + single g₂ 1
  -- Target (Pi.Y1): Gene.ofRank (m-1) (-ε) + Gene.ofRank (k+1) ε
  let ε := g₁.type
  have hε : ε ≠ .NonPolarized :=
    IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
  have hle : g₁.rank ≤ g₂.rank := le_of_lt hg₂rank
  -- ofRank g₁.rank ε = single g₁ 1
  have hg₁_ofRank : Gene.ofRank g₁.rank ε = Finsupp.single g₁ 1 :=
    Gene.ofRank_eq_gene
  -- ofRank g₂.rank (-ε) = single g₂ 1  (since g₂.type = -ε by hε₂)
  have hg₂_ofRank : Gene.ofRank g₂.rank (-ε) = Finsupp.single g₂ 1 := by
    have h := @Gene.ofRank_eq_gene g₂; rw [hε₂] at h; exact h
  -- The type1 source chromosome equals single g₁ 1 + single g₂ 1
  have hsrc_val : (Pi.X1 hε hle g₁.rank_pos : Chromosome) =
      Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
    simp only [Pi.X1_eq]; rw [hg₁_ofRank, hg₂_ofRank]
  -- src ≤ X.1.val pointwise
  have hsrc_le : ∀ g : Gene,
      (Pi.X1 hε hle g₁.rank_pos : Chromosome) g ≤ X.1.val g := by
    have hne : g₁ ≠ g₂ := fun h => absurd hg₂rank (h ▸ lt_irrefl _)
    intro gen
    rw [hsrc_val, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    rcases eq_or_ne gen g₁ with rfl | hng₁
    · -- gen = g₁: 1 + 0 ≤ X.1.val g₁ = 1
      simp [Ne.symm hne, hg₁_one]
    · rcases eq_or_ne gen g₂ with rfl | hng₂
      · -- gen = g₂: 0 + 1 ≤ X.1.val g₂
        simp only [Ne.symm hng₁]
        exact hg₂pos
      · -- gen ∉ {g₁, g₂}: 0 ≤ X.1.val gen
        simp [Ne.symm hng₁, Ne.symm hng₂]
  -- rest = X.1.val − src, still in Pi
  let rest : Pi :=
    ⟨X.1.val - (Pi.X1 hε hle g₁.rank_pos : Chromosome),
      Variety.sub_mem_Pi _ X.1.2⟩
  -- X.1 decomposes as src + rest
  have hdecomp : X.1 = Pi.X1 hε hle g₁.rank_pos + rest :=
    Subtype.val_injective
      (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
  -- Z is the type1 mutation result
  let Z : Pi := Pi.Y1 hε hle g₁.rank_pos + rest
  -- Construct the Pi-step
  have hstep : Pi.Step X.1 Z :=
    hdecomp.symm ▸ Pi.Step.mk
      (Pi.X1 hε hle g₁.rank_pos)
      (Pi.Y1 hε hle g₁.rank_pos)
      rest
      (Pi.Primitive.type1 ε hε hle g₁.rank_pos)
  exact ⟨Z, hstep, by
    change Z.val ≤ Y.1.val
    rw [le_iff_dominates]
    intro i
    change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
    have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
      le_iff_dominates.mp hXY.le i
    have hZ_split : Sigma.sigma Z.val i =
        Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos).val i + Sigma.sigma rest.val i := by
      change Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos + rest : Variety.Pi).val i = _
      simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
    have hX_split : Sigma.sigma X.1.val i =
        Sigma.sigma (Pi.X1 hε hle g₁.rank_pos).val i + Sigma.sigma rest.val i := by
      have hval : X.1.val = (Pi.X1 hε hle g₁.rank_pos).val + rest.val := by
        have h := congrArg Subtype.val hdecomp
        simp only [AddSubmonoid.coe_add] at h; exact h
      simp only [hval, Sigma.sigma, iterate_map_add, map_add]
    -- All conditions on the relationship between X and Y
    have hXY_sigma :
        (∀ j, g₁.rank ≤ j → j ≤ g₂.rank →
          Sigma.sigma X.1.val j + (Gene.ofRank 1 ε).signature ≤
          Sigma.sigma Y.1.val j) ∧
        (∀ j, ¬(g₁.rank ≤ j ∧ j ≤ g₂.rank) →
          Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos).val j =
          Sigma.sigma (Pi.X1 hε hle g₁.rank_pos).val j) := by
      have h_outside_range : ∀ j, ¬(g₁.rank ≤ j ∧ j ≤ g₂.rank) →
          Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos).val j =
          Sigma.sigma (Pi.X1 hε hle g₁.rank_pos).val j := by
          intro j hj
          rcases not_and_or.mp hj with h | h
          · -- j < g₁.rank: signature equality by mutation_type1_signature_eq
            simp only [Sigma.sigma, Pi.Y1_eq, Pi.X1_eq, iterate_map_add,
                       prime_iterate_ofRank]
            rw [show g₁.rank - 1 - j = g₁.rank - j - 1 from by omega,
                show g₂.rank + 1 - j = g₂.rank - j + 1 from by omega]
            exact (mutation_type1_signature_eq hε (by omega) (by omega)).symm
          · -- j > g₂.rank: both sigma values are 0
            simp only [Sigma.sigma, Pi.Y1_eq, Pi.X1_eq, iterate_map_add,
                       prime_iterate_ofRank,
                       show g₁.rank - j = 0 from by omega,
                       show g₂.rank - j = 0 from by omega,
                       show g₁.rank - 1 - j = 0 from by omega,
                       show g₂.rank + 1 - j = 0 from by omega,
                       Gene.ofRank_zero, map_zero, add_zero]
      by_cases heven : Even g₁.rank
      · -- g₁.rank is even
        have hε_neg : ε = .Negative :=
          gene_type_eq_negative_of_even_of_ne_negOnePow_negative heven hε hε₁
        -- b_{rank} < d_{rank}
        have hb_lt_d_rank : (Sigma.sigma X.1 g₁.rank).2 <
            (Sigma.sigma Y.1 g₁.rank).2 := by
          have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            linarith [sigma_zero_fst_eq X Y hXY.le]
          have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
            (le_iff_dominates.mp hXY.le 1).2
          have hb12_eq : (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 =
            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            -- g₁.type is in the Positive family (not Negative by hε₁,
             --not NonPolarized by polarization)
            -- Gene.ofRankAlt g₁.rank Positive = single g₁ 1
            have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Positive =
                 Finsupp.single g₁ 1 := by
              exact ofRankAlt_eq_single_of_type_eq_altType <| by
                simpa [Sigma.altType] using
                  gene_type_eq_negOnePow_positive_of_ne_negOnePow_negative hε hε₁
            -- Apply x_side_equalities at j = 1 (odd),
              -- using g₁ as the minimal Positive-family gene
            have h := x_side_equalities
              (fun g' _ hg'_pos => hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
              (show 1 < g₁.rank from hg₁_ge2)
            simp only [show ¬Even 1 from by norm_num, ↓reduceIte] at h
            exact h
          have hd12_le : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 ≤
              (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
            have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (2 - 1) Y.1.2
            simp only [show ¬Even (2 - 1 : ℕ) from by norm_num, if_false] at h
            exact h
          have hb12_gt_d12 : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 <
            (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 := by
            linarith [hb12_eq, hstrict, hd12_le]
          have hd2_gt_b2 : (Sigma.sigma X.1 2).2 < (Sigma.sigma Y.1 2).2 := by
            linarith [hb1_le_d1, hb12_gt_d12]
          have no_neg_gene_rank_g : ∀ g' ∈ X.1.val.support,
              g'.rank = g₁.rank → g'.type = .Negative := by
            intro g' hg'_supp hg'_rank
            have hg'_ne_np := IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
            have hg'_ne_pos : g'.type ≠ .Positive := fun hg'_pos => hXpn
              ⟨g', g₁, hg'_rank, hg'_pos, hε_neg,
               Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp), hXg₁pos⟩
            cases ht' : g'.type with
            | Positive => exact absurd ht' hg'_ne_pos
            | Negative => rfl
            | NonPolarized => exact absurd ht' hg'_ne_np
          have hc1_ci_rank1 : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 ≤
              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
            Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
          have hb0_b2_rank1 : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
              (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 g₁.rank).2 := by
            have h := Sigma.b0_eq_b2_negative g₁.rank hg₁_ge2 hg₁min
              no_neg_gene_rank_g (show g₁.rank - 2 ≤ g₁.rank - 1 from by omega)
            simp only [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h; exact h
          have hd0_di_rank1 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 ≤
              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 :=
            theorem6_snd_gap_le_of_dominates X Y hXY.le
          have hd2_c1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
              (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
            by_cases hrank2 : g₁.rank = 2
            · simp only [hrank2, sub_self, le_refl]
            · have h : g₁.rank - 1 ≥ 2 := by omega
              have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
              rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
          have hd2_di1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
            hd2_c1_rank1.trans hc1_ci_rank1
          linarith [hd2_di1_rank1, hd0_di_rank1, hb0_b2_rank1, hd2_gt_b2]
        have hdi_sub_le_bi_sub : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank - 1 →
            (Sigma.sigma Y.1 j).2 - (Sigma.sigma Y.1 (j + 1)).2 ≤
            (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 := by
          intro j hj1 hj2
          by_cases hjeven : Even j
          · -- j is even
            have hdj_le_d0 : (Sigma.sigma Y.1 j).2 - (Sigma.sigma Y.1 (j + 1)).2 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 1).2 := by
              have key : ∀ n : ℕ,
                  (Sigma.sigma Y.1.val (n + n)).2 -
                  (Sigma.sigma Y.1.val (n + n + 1)).2 ≤
                  (Sigma.sigma Y.1.val 0).2 - (Sigma.sigma Y.1.val 1).2 := by
                intro n
                induction n with
                | zero => simp
                | succ n ih =>
                  have h1 : (Sigma.drop Y.1.val (n + n + 2)).2 ≤
                      (Sigma.drop Y.1.val (n + n + 1)).1 := by
                    have h := Sigma.cond_15_7_drop Y.1.val (n + n + 1) Y.1.2
                    rw [if_neg (fun heven =>
                      (Nat.even_add_one.mp heven) ⟨n, rfl⟩)] at h; exact h
                  have h2 : (Sigma.drop Y.1.val (n + n + 1)).1 ≤
                      (Sigma.drop Y.1.val (n + n)).2 := by
                    have h := Sigma.cond_15_7_drop Y.1.val (n + n) Y.1.2
                    rw [if_pos ⟨n, rfl⟩] at h; exact h
                  simp only [Sigma.drop_snd, Sigma.drop_fst] at h1 h2
                  rw [show n + 1 + (n + 1) = n + n + 2 from by omega]; linarith
              obtain ⟨m, hm⟩ := hjeven
              rw [hm]; exact key m
            have hd0_le_b0 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 1).2 ≤
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 := by
              have hb0_eq_d0 := sigma_zero_snd_eq X Y hXY.le
              have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
                (le_iff_dominates.mp hXY.le 1).2
              linarith
            have hb0_eq_bj : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 := by
              have hLHS : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    0 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative),
                  (X.1.val g : ℚ) := by
                have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
                have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
                simp only [Function.iterate_zero, id] at h1 h2
                exact h1.trans h2
              have hRHS : (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 =
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
                    g.type = Sigma.altType g.rank GeneType.Negative) := by
                ext g
                simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                constructor
                · rintro ⟨hg_supp, _, hg_type⟩
                  refine ⟨hg_supp, ?_, hg_type⟩
                  have hmin := hg₁min g (Finsupp.mem_support_iff.mpr hg_supp)
                  rcases eq_or_lt_of_le hmin with h_eq | h_lt
                  · have halttype :
                        Sigma.altType g.rank GeneType.Negative =
                        GeneType.Positive := by
                      rw [show g.rank = g₁.rank from h_eq.symm,
                          Sigma.altType_even g₁.rank heven,
                          GeneType.neg_negative]
                    rw [halttype] at hg_type
                    exact absurd hXpn (not_not.mpr
                      ⟨g, g₁, h_eq.symm, hg_type, hε_neg,
                       Nat.pos_of_ne_zero hg_supp, hXg₁pos⟩)
                  · exact by
                      have := hg₂min g (Nat.pos_of_ne_zero hg_supp) h_lt
                      omega
                · rintro ⟨hg_supp, hg_rank, hg_type⟩
                  exact ⟨hg_supp, g.rank_pos, hg_type⟩
              rw [hLHS, hRHS, hfilter_eq]
            linarith
          · -- j is odd
            have hdj_le_c01 : (Sigma.sigma Y.1 j).2 - (Sigma.sigma Y.1 (j + 1)).2 ≤
                (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
              simpa [hjeven] using Sigma.cond_15_6_compare_k_to_0 Y.1.val j Y.1.2
            have hc01_le_a01_sub1 : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 ≤
                (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 := by
              have ha0_eq_c0 := sigma_zero_fst_eq X Y hXY.le
              have ha : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                  (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                linarith [sigma_zero_fst_eq X Y hXY.le]
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val 1 X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val 1 Y.1.2
              have hX1 : (Sigma.sigma X.1 1).1 = ↑nX.1 := congr_arg Prod.fst hnX
              have hY1 : (Sigma.sigma Y.1 1).1 = ↑nY.1 := congr_arg Prod.fst hnY
              have hlt : (↑nX.1 : ℚ) < ↑nY.1 := by linarith
              have hlt_nat : nX.1 < nY.1 := by exact_mod_cast hlt
              have hle : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 := by
                exact_mod_cast (by omega : nX.1 + 1 ≤ nY.1)
              linarith
            have ha01_sub1_eq_bm : (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 =
                (Sigma.sigma X.1 (g₁.rank - 1)).2 - (Sigma.sigma X.1 g₁.rank).2 - 1 := by
              have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
                rw [Sigma.altType_even g₁.rank heven, GeneType.neg_positive]; exact hε_neg
              have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Positive =
                  Finsupp.single g₁ 1 := by
                rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]
                congr 1; exact Gene.ext rfl hg₁_altType.symm
              have h := x_side_equalities
                (fun g' _ hg' => hg₁min g' (Finsupp.mem_support_iff.mpr hg'.ne'))
                (show g₁.rank - 1 < g₁.rank from by omega)
              rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
              have hodd : ¬Even (g₁.rank - 1) := by
                obtain ⟨r, hr⟩ := heven; intro ⟨s, hs⟩; omega
              simp only [hodd, if_false] at h
              linarith
            have hbm_sub1_eq_am : (Sigma.sigma X.1 (g₁.rank - 1)).2 -
                (Sigma.sigma X.1 g₁.rank).2 - 1 =
                (Sigma.sigma X.1 g₁.rank).1 - (Sigma.sigma X.1 (g₁.rank + 1)).1 := by
              -- Step 1: rewrite LHS drop via sigma_snd_diff +
              -- prime_iterate_sum_neg_eq
              have hLHS : (Sigma.sigma X.1 (g₁.rank - 1)).2 -
                  (Sigma.sigma X.1 g₁.rank).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    g₁.rank - 1 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive),
                  (X.1.val g : ℚ) := by
                have h := Sigma.sigma_snd_diff X.1.val (g₁.rank - 1) X.1.2
                rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
                rw [h, Sigma.prime_iterate_sum_neg_eq X.1.val (g₁.rank - 1)
                        (show ¬Even (g₁.rank - 1) from by
                          obtain ⟨r, hr⟩ := heven
                          intro ⟨s, hs⟩; omega)]
                rfl
              -- Step 2: rewrite RHS drop via sigma_fst_diff + prime_iterate_sum_pos_eq
              have hRHS : (Sigma.sigma X.1 g₁.rank).1 -
                  (Sigma.sigma X.1 (g₁.rank + 1)).1 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    g₁.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive),
                  (X.1.val g : ℚ) := by
                rw [Sigma.sigma_fst_diff X.1.val g₁.rank X.1.2,
                    Sigma.prime_iterate_sum_pos_eq X.1.val g₁.rank heven]
                rfl
              -- g₁ satisfies the LHS filter:
              --  altType g₁.rank Positive = Negative = g₁.type
              have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
                rw [Sigma.altType_even g₁.rank heven, GeneType.neg_positive]
                exact hε_neg
              -- Split: LHS filter = {g₁} ∪ RHS filter (g₁ not in RHS filter)
              have hfilter_split :
                  X.1.val.support.filter (fun g =>
                    g₁.rank - 1 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive) =
                  {g₁} ∪ X.1.val.support.filter (fun g =>
                    g₁.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive) := by
                ext g
                simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
                           Finsupp.mem_support_iff]
                constructor
                · rintro ⟨hsupp, hrank, htype⟩
                  by_cases heq : g = g₁
                  · left; exact heq
                  · right
                    refine ⟨hsupp, ?_, htype⟩
                    rcases Nat.lt_or_eq_of_le
                      (show g₁.rank ≤ g.rank from by omega) with h | h
                    · exact h
                    · exfalso; apply heq
                      exact Gene.ext h.symm
                        (by rw [← h, ← hg₁_altType] at htype; exact htype)
                · rintro (rfl | ⟨hsupp, hrank, htype⟩)
                  · exact ⟨by rw [hg₁_one]; exact one_ne_zero, by omega, hg₁_altType⟩
                  · exact ⟨hsupp, by omega, htype⟩
              have hdisjoint : Disjoint {g₁} (X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧ g.type =
                  Sigma.altType g.rank GeneType.Positive)) := by
                simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_filter]
                rintro g rfl ⟨_, hlt, _⟩
                exact absurd hlt (lt_irrefl _)
              rw [hLHS, hfilter_split, Finset.sum_union hdisjoint, Finset.sum_singleton,
                  show (X.1.val g₁ : ℚ) = 1 from by exact_mod_cast hg₁_one, hRHS]
              ring
            have ham_eq_bj : (Sigma.sigma X.1 g₁.rank).1 -
                (Sigma.sigma X.1 (g₁.rank + 1)).1 =
                (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 := by
              have hLHS : (Sigma.sigma X.1 g₁.rank).1 -
                  (Sigma.sigma X.1 (g₁.rank + 1)).1 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    g₁.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive),
                  (X.1.val g : ℚ) := by
                rw [Sigma.sigma_fst_diff X.1.val g₁.rank X.1.2,
                    Sigma.prime_iterate_sum_pos_eq X.1.val g₁.rank heven]
                rfl
              have hRHS : (Sigma.sigma X.1 j).2 -
                  (Sigma.sigma X.1 (j + 1)).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    j < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive),
                  (X.1.val g : ℚ) := by
                rw [Sigma.sigma_snd_diff X.1.val j X.1.2,
                    Sigma.prime_iterate_sum_neg_eq X.1.val j hjeven]
                rfl
              have hfilter_eq :
                  X.1.val.support.filter (fun g =>
                    g₁.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive) =
                  X.1.val.support.filter (fun g =>
                    j < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive) := by
                ext g
                simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                constructor
                · rintro ⟨hg_supp, hg_rank, hg_type⟩
                  exact ⟨hg_supp,
                    by have := hg₂min g
                          (Nat.pos_of_ne_zero hg_supp)
                          hg_rank; omega,
                    hg_type⟩
                · rintro ⟨hg_supp, hg_rank, hg_type⟩
                  exact ⟨hg_supp, by omega, hg_type⟩
              rw [hLHS, hRHS, hfilter_eq]
            linarith
        have hbj_lt_dj : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank →
            (Sigma.sigma X.1 j).2 < (Sigma.sigma Y.1 j).2 := by
          intro j hj1 hj2
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj1
          induction d with
          | zero => simpa using hb_lt_d_rank
          | succ d ih =>
            have ihd := ih (by omega) (by omega)
            have hstep := hdi_sub_le_bi_sub (g₁.rank + d) (by omega) (by omega)
            change (Sigma.sigma X.1 (g₁.rank + d + 1)).2 <
                 (Sigma.sigma Y.1 (g₁.rank + d + 1)).2
            simp at hstep
            linarith
        refine ⟨fun j hj1 hj2 => ?_, h_outside_range⟩
        have hbj := hbj_lt_dj j hj1 hj2
        rw [show (Gene.ofRank 1 ε).signature = (0, 1) from by
          rw [hε_neg]
          simp [Gene.signature, Gene.ofRank, show ¬ Even 1 from by decide]]
        constructor
        · have h1 := (le_iff_dominates.mp hXY.le j).1
          simp only [Prod.fst_add, add_zero]
          simpa [Sigma.sigma] using h1
        · simpa using theorem6_sigma_snd_add_one_le_of_lt X.1.2 Y.1.2 j hbj
      · -- g₁.rank is odd
        have hodd : Odd g₁.rank := Nat.not_even_iff_odd.mp heven
        have hε_pos : ε = .Positive :=
          gene_type_eq_positive_of_odd_of_ne_negOnePow_negative hodd hε hε₁
        -- a_{rank} < c_{rank}
        have ha_lt_c_rank : (Sigma.sigma X.1 g₁.rank).1 <
            (Sigma.sigma Y.1 g₁.rank).1 := by
          have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            linarith [sigma_zero_fst_eq X Y hXY.le]
          have hc1_ci_rank : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 ≤
              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
            Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
          have hd0_di_rank : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 :=
            theorem6_snd_gap_le_of_dominates X Y hXY.le
          have hb0_bi_rank : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 =
              (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 g₁.rank).1 :=
            x_actual_negative_prefix_equalities
              (fun g' _ hg'_pos => hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
              (by omega) (le_refl _)
          linarith [sigma_zero_fst_eq X Y hXY.le, hc1_ci_rank, hd0_di_rank,
            hb0_bi_rank, hstrict]
        have hci_sub_le_ai_sub : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank - 1 →
            (Sigma.sigma Y.1 j).1 - (Sigma.sigma Y.1 (j + 1)).1 ≤
            (Sigma.sigma X.1 j).1 - (Sigma.sigma X.1 (j + 1)).1 := by
          intro j hj1 hj2
          by_cases hjeven : Even j
          · -- j is even
            have hcj_le_c01 :
                (Sigma.sigma Y.1 j).1 - (Sigma.sigma Y.1 (j + 1)).1 ≤
                (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
              simpa [hjeven] using Sigma.cond_15_6_compare_k_to_0 Y.1.val j Y.1.2
            have hc01_le_a01_sub1 :
                (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 ≤
                (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 := by
              have ha0_eq_c0 := sigma_zero_fst_eq X Y hXY.le
              have ha : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                  (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                linarith [sigma_zero_fst_eq X Y hXY.le]
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val 1 X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val 1 Y.1.2
              have hX1 : (Sigma.sigma X.1 1).1 = ↑nX.1 := congr_arg Prod.fst hnX
              have hY1 : (Sigma.sigma Y.1 1).1 = ↑nY.1 := congr_arg Prod.fst hnY
              have hlt : (↑nX.1 : ℚ) < ↑nY.1 := by linarith
              have hlt_nat : nX.1 < nY.1 := by exact_mod_cast hlt
              have hle : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 := by
                exact_mod_cast (by omega : nX.1 + 1 ≤ nY.1)
              linarith
            have ha01_sub1_eq_am_sub1 :
                (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 =
                (Sigma.sigma X.1 (g₁.rank - 1)).1 - (Sigma.sigma X.1 g₁.rank).1 - 1 := by
              have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
                rw [Sigma.altType_odd g₁.rank heven]; exact hε_pos
              have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Positive =
                  Finsupp.single g₁ 1 := by
                rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]
                congr 1; exact Gene.ext rfl hg₁_altType.symm
              have h := x_side_equalities
                (fun g' _ hg' => hg₁min g' (Finsupp.mem_support_iff.mpr hg'.ne'))
                (show g₁.rank - 1 < g₁.rank from by omega)
              rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
              have heven_sub1 : Even (g₁.rank - 1) := by
                obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp heven
                exact ⟨r, by omega⟩
              simp only [if_pos heven_sub1] at h
              linarith
            have ham_sub1_eq_bm :
                (Sigma.sigma X.1 (g₁.rank - 1)).1 - (Sigma.sigma X.1 g₁.rank).1 - 1 =
                (Sigma.sigma X.1 g₁.rank).2 - (Sigma.sigma X.1 (g₁.rank + 1)).2 := by
              have hLHS : (Sigma.sigma X.1 (g₁.rank - 1)).1 -
                  (Sigma.sigma X.1 g₁.rank).1 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    g₁.rank - 1 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive),
                  (X.1.val g : ℚ) := by
                have h := Sigma.sigma_fst_diff X.1.val (g₁.rank - 1) X.1.2
                rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
                rw [h, Sigma.prime_iterate_sum_pos_eq X.1.val (g₁.rank - 1)
                        (show Even (g₁.rank - 1) from by
                          obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp heven
                          exact ⟨r, by omega⟩)]
                rfl
              have hRHS : (Sigma.sigma X.1 g₁.rank).2 -
                  (Sigma.sigma X.1 (g₁.rank + 1)).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    g₁.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive),
                  (X.1.val g : ℚ) := by
                rw [Sigma.sigma_snd_diff X.1.val g₁.rank X.1.2,
                    Sigma.prime_iterate_sum_neg_eq X.1.val g₁.rank heven]
                rfl
              have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
                rw [Sigma.altType_odd g₁.rank heven]; exact hε_pos
              have hfilter_split :
                  X.1.val.support.filter (fun g =>
                    g₁.rank - 1 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive) =
                  {g₁} ∪ X.1.val.support.filter (fun g =>
                    g₁.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive) := by
                ext g
                simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
                           Finsupp.mem_support_iff]
                constructor
                · rintro ⟨hsupp, hrank, htype⟩
                  by_cases heq : g = g₁
                  · left; exact heq
                  · right
                    refine ⟨hsupp, ?_, htype⟩
                    rcases Nat.lt_or_eq_of_le
                      (show g₁.rank ≤ g.rank from by omega) with h | h
                    · exact h
                    · exfalso; apply heq
                      exact Gene.ext h.symm
                        (by rw [← h, ← hg₁_altType] at htype; exact htype)
                · rintro (rfl | ⟨hsupp, hrank, htype⟩)
                  · exact ⟨by rw [hg₁_one]; exact one_ne_zero, by omega, hg₁_altType⟩
                  · exact ⟨hsupp, by omega, htype⟩
              have hdisjoint : Disjoint {g₁} (X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧ g.type =
                  Sigma.altType g.rank GeneType.Positive)) := by
                simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_filter]
                rintro g rfl ⟨_, hlt, _⟩
                exact absurd hlt (lt_irrefl _)
              rw [hLHS, hfilter_split, Finset.sum_union hdisjoint, Finset.sum_singleton,
                  show (X.1.val g₁ : ℚ) = 1 from by exact_mod_cast hg₁_one, hRHS]
              ring
            have hbm_eq_aj :
                (Sigma.sigma X.1 g₁.rank).2 - (Sigma.sigma X.1 (g₁.rank + 1)).2 =
                (Sigma.sigma X.1 j).1 - (Sigma.sigma X.1 (j + 1)).1 := by
              have hLHS : (Sigma.sigma X.1 g₁.rank).2 -
                  (Sigma.sigma X.1 (g₁.rank + 1)).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    g₁.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive),
                  (X.1.val g : ℚ) := by
                rw [Sigma.sigma_snd_diff X.1.val g₁.rank X.1.2,
                    Sigma.prime_iterate_sum_neg_eq X.1.val g₁.rank heven]
                rfl
              have hRHS : (Sigma.sigma X.1 j).1 -
                  (Sigma.sigma X.1 (j + 1)).1 =
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
                    g.type = Sigma.altType g.rank GeneType.Positive) := by
                ext g
                simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                constructor
                · rintro ⟨hg_supp, hg_rank, hg_type⟩
                  exact ⟨hg_supp,
                    by have := hg₂min g
                          (Nat.pos_of_ne_zero hg_supp)
                          hg_rank; omega,
                    hg_type⟩
                · rintro ⟨hg_supp, hg_rank, hg_type⟩
                  exact ⟨hg_supp, by omega, hg_type⟩
              rw [hLHS, hRHS, hfilter_eq]
            linarith
          · -- j is odd
            have hcj_le_c12 :
                (Sigma.sigma Y.1 j).1 - (Sigma.sigma Y.1 (j + 1)).1 ≤
                (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 2).1 := by
              have key : ∀ n : ℕ,
                  (Sigma.sigma Y.1.val (n + n + 1)).1 -
                  (Sigma.sigma Y.1.val (n + n + 2)).1 ≤
                  (Sigma.sigma Y.1.val 1).1 - (Sigma.sigma Y.1.val 2).1 := by
                intro n
                induction n with
                | zero => simp
                | succ n ih =>
                  have h1 : (Sigma.drop Y.1.val (n + n + 3)).1 ≤
                      (Sigma.drop Y.1.val (n + n + 2)).2 := by
                    have h := Sigma.cond_15_7_drop Y.1.val (n + n + 2) Y.1.2
                    rw [if_pos ⟨n + 1, by omega⟩] at h; exact h
                  have h2 : (Sigma.drop Y.1.val (n + n + 2)).2 ≤
                      (Sigma.drop Y.1.val (n + n + 1)).1 := by
                    have h := Sigma.cond_15_7_drop Y.1.val (n + n + 1) Y.1.2
                    rw [if_neg (fun heven =>
                      (Nat.even_add_one.mp heven) ⟨n, rfl⟩)] at h; exact h
                  simp only [Sigma.drop_fst, Sigma.drop_snd] at h1 h2
                  rw [show n + 1 + (n + 1) + 1 = n + n + 3 from by omega,
                      show n + 1 + (n + 1) + 2 = n + n + 4 from by omega]
                  linarith
              obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hjeven
              rw [show j = m + m + 1 from by omega]
              exact key m
            have hc12_le_d01 :
                (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 2).1 ≤
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 1).2 := by
              simpa using Sigma.cond_15_7 Y.1.val 0 Y.1.2
            have hd01_le_b01 :
                (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 1).2 ≤
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 := by
              have hb0_eq_d0 := sigma_zero_snd_eq X Y hXY.le
              have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
                (le_iff_dominates.mp hXY.le 1).2
              linarith
            have hb01_eq_aj :
                (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                (Sigma.sigma X.1 j).1 - (Sigma.sigma X.1 (j + 1)).1 := by
              have hLHS : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    0 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative),
                  (X.1.val g : ℚ) := by
                have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
                have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
                simp only [Function.iterate_zero, id] at h1 h2
                exact h1.trans h2
              have hRHS : (Sigma.sigma X.1 j).1 - (Sigma.sigma X.1 (j + 1)).1 =
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
                    g.type = Sigma.altType g.rank GeneType.Negative) := by
                ext g
                simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                constructor
                · rintro ⟨hg_supp, _, hg_type⟩
                  refine ⟨hg_supp, ?_, hg_type⟩
                  have hmin := hg₁min g (Finsupp.mem_support_iff.mpr hg_supp)
                  rcases eq_or_lt_of_le hmin with h_eq | h_lt
                  · have halttype :
                        Sigma.altType g.rank GeneType.Negative =
                        GeneType.Negative := by
                      rw [show g.rank = g₁.rank from h_eq.symm,
                          Sigma.altType_odd g₁.rank heven]
                    rw [halttype] at hg_type
                    exact absurd hXpn (not_not.mpr
                      ⟨g₁, g, h_eq, hε_pos, hg_type,
                       hXg₁pos, Nat.pos_of_ne_zero hg_supp⟩)
                  · exact by
                      have := hg₂min g (Nat.pos_of_ne_zero hg_supp) h_lt
                      omega
                · rintro ⟨hg_supp, hg_rank, hg_type⟩
                  exact ⟨hg_supp, g.rank_pos, hg_type⟩
              rw [hLHS, hRHS, hfilter_eq]
            linarith
        have haj_lt_cj : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank →
            (Sigma.sigma X.1 j).1 < (Sigma.sigma Y.1 j).1 := by
          intro j hj1 hj2
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj1
          induction d with
          | zero => simpa using ha_lt_c_rank
          | succ d ih =>
            have ihd := ih (by omega) (by omega)
            have hstep := hci_sub_le_ai_sub (g₁.rank + d) (by omega) (by omega)
            change (Sigma.sigma X.1 (g₁.rank + d + 1)).1 <
                 (Sigma.sigma Y.1 (g₁.rank + d + 1)).1
            simp at hstep
            linarith
        refine ⟨fun j hj1 hj2 => ?_, h_outside_range⟩
        have haj := haj_lt_cj j hj1 hj2
        rw [show (Gene.ofRank 1 ε).signature = (1, 0) from by
          rw [hε_pos]
          simp [Gene.signature, Gene.ofRank, show ¬ Even 1 from by decide]]
        constructor
        · simpa using theorem6_sigma_fst_add_one_le_of_lt X.1.2 Y.1.2 j haj
        · have h2 := (le_iff_dominates.mp hXY.le j).2
          simp only [Prod.snd_add, add_zero]
          simpa [Sigma.sigma] using h2
    by_cases hin : g₁.rank ≤ i ∧ i ≤ g₂.rank
    · obtain ⟨hi1, hi2⟩ := hin
      -- Inside [g₁.rank, g₂.rank]: sigma(Y1)(i) - sigma(X1)(i) = sig(ofRank 1 ε)
      have hdiff : Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos).val i -
          Sigma.sigma (Pi.X1 hε hle g₁.rank_pos).val i =
          (Gene.ofRank 1 ε).signature := by
        simp only [Sigma.sigma, Pi.Y1_eq, Pi.X1_eq, iterate_map_add,
          prime_iterate_ofRank,
          show g₁.rank - i = 0 from Nat.sub_eq_zero_of_le hi1,
          show g₁.rank - 1 - i = 0 from Nat.sub_eq_zero_of_le (by omega),
          Gene.ofRank_zero, zero_add]
        rw [signature_ofRank_general (show 1 ≤ g₂.rank + 1 - i from by omega) hε,
          show g₂.rank + 1 - i - 1 = g₂.rank - i from by omega]
        ring
      -- sigma(Z)(i) = sigma(X)(i) + sig(ofRank 1 ε)
      have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
          (Gene.ofRank 1 ε).signature := by
        rw [hZ_split, hX_split, add_sub_add_right_eq_sub]; exact hdiff
      have hZX_eq : Sigma.sigma Z.val i =
          Sigma.sigma X.1.val i + (Gene.ofRank 1 ε).signature :=
        theorem6_sigma_eq_add_of_sub_eq hZX_diff
      rw [hZX_eq]
      exact hXY_sigma.1 i hi1 hi2
    · -- Outside [g₁.rank, g₂.rank]: sigma(Z)(i) = sigma(X)(i) ≤ sigma(Y)(i)
      rw [hZ_split, hXY_sigma.2 i hin, ← hX_split]; exact hXY_i⟩
