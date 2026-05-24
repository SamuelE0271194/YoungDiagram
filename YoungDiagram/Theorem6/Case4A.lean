import YoungDiagram.Theorem6.Prelim

open Variety hiding prime prime_def
open Chromosome

private lemma support_filter_tail_eq {X : Chromosome} {g₁ g₂ : Gene} {j : ℕ} {τ : GeneType}
    (hg₂min : ∀ g', 0 < X g' → g₁.rank < g'.rank → g₂.rank ≤ g'.rank)
    (hj1 : g₁.rank ≤ j) (hj2 : j ≤ g₂.rank - 1) :
    X.support.filter (fun g => g₁.rank < g.rank ∧ g.type = Sigma.altType g.rank τ) =
      X.support.filter (fun g => j < g.rank ∧ g.type = Sigma.altType g.rank τ) := by
  ext g
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  refine ⟨fun ⟨hs, hr, ht⟩ => ⟨hs, ?_, ht⟩, fun ⟨hs, hr, ht⟩ => ⟨hs, by omega, ht⟩⟩
  have := hg₂min g (Nat.pos_of_ne_zero hs) hr; omega

private lemma support_filter_rank_pred_altType_split {X : Chromosome} {g₁ : Gene} {τ : GeneType}
    (hg₁_one : X g₁ = 1) (hg₁_altType : g₁.type = Sigma.altType g₁.rank τ) :
    X.support.filter (fun g => g₁.rank - 1 < g.rank ∧ g.type = Sigma.altType g.rank τ) =
      {g₁} ∪ X.support.filter (fun g => g₁.rank < g.rank ∧
        g.type = Sigma.altType g.rank τ) := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
    Finsupp.mem_support_iff]
  refine ⟨fun ⟨hsupp, hrank, htype⟩ => ?_, ?_⟩
  · by_cases heq : g = g₁
    · exact Or.inl heq
    · refine Or.inr ⟨hsupp, ?_, htype⟩
      rcases Nat.lt_or_eq_of_le (show g₁.rank ≤ g.rank by omega) with h | h
      · exact h
      · exact absurd (Gene.ext h.symm (by rw [← h, ← hg₁_altType] at htype; exact htype)) heq
  · rintro (rfl | ⟨hsupp, hrank, htype⟩)
    · exact ⟨by rw [hg₁_one]; exact one_ne_zero, by have := g.rank_pos; omega, hg₁_altType⟩
    · exact ⟨hsupp, by have := g₁.rank_pos; omega, htype⟩

lemma support_filter_negative_eq_tail_of_even {X : Chromosome} {g₁ g₂ : Gene} {j : ℕ}
    (hXpn : ¬∃ g h, g.rank = h.rank ∧ g.type = GeneType.Positive ∧
      h.type = GeneType.Negative ∧ 0 < X g ∧ 0 < X h)
    (hXg₁pos : 0 < X g₁) (hg₁min : ∀ g ∈ X.support, g₁.rank ≤ g.rank)
    (hg₂min : ∀ g', 0 < X g' → g₁.rank < g'.rank → g₂.rank ≤ g'.rank)
    (heven : Even g₁.rank) (hε_neg : g₁.type = .Negative)
    (hj2 : j ≤ g₂.rank - 1) :
    X.support.filter (fun g => 0 < g.rank ∧
      g.type = Sigma.altType g.rank GeneType.Negative) =
    X.support.filter (fun g => j < g.rank ∧
      g.type = Sigma.altType g.rank GeneType.Negative) := by
  ext g
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  refine ⟨fun ⟨hs, _, ht⟩ => ⟨hs, ?_, ht⟩, fun ⟨hs, _, ht⟩ => ⟨hs, g.rank_pos, ht⟩⟩
  rcases eq_or_lt_of_le (hg₁min g (Finsupp.mem_support_iff.mpr hs)) with h_eq | h_lt
  · have halttype : Sigma.altType g.rank GeneType.Negative = GeneType.Positive := by
      rw [show g.rank = g₁.rank from h_eq.symm, Sigma.altType_even g₁.rank heven,
        GeneType.neg_negative]
    rw [halttype] at ht
    exact absurd hXpn (not_not.mpr
      ⟨g, g₁, h_eq.symm, ht, hε_neg, Nat.pos_of_ne_zero hs, hXg₁pos⟩)
  · have := hg₂min g (Nat.pos_of_ne_zero hs) h_lt; omega

lemma support_filter_negative_eq_tail_of_odd {X : Chromosome} {g₁ g₂ : Gene} {j : ℕ}
    (hXpn : ¬∃ g h, g.rank = h.rank ∧ g.type = GeneType.Positive ∧
      h.type = GeneType.Negative ∧ 0 < X g ∧ 0 < X h)
    (hXg₁pos : 0 < X g₁) (hg₁min : ∀ g ∈ X.support, g₁.rank ≤ g.rank)
    (hg₂min : ∀ g', 0 < X g' → g₁.rank < g'.rank → g₂.rank ≤ g'.rank)
    (hodd : ¬ Even g₁.rank) (hε_pos : g₁.type = .Positive)
    (hj2 : j ≤ g₂.rank - 1) :
    X.support.filter (fun g => 0 < g.rank ∧
      g.type = Sigma.altType g.rank GeneType.Negative) =
    X.support.filter (fun g => j < g.rank ∧
      g.type = Sigma.altType g.rank GeneType.Negative) := by
  ext g
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  refine ⟨fun ⟨hs, _, ht⟩ => ⟨hs, ?_, ht⟩, fun ⟨hs, _, ht⟩ => ⟨hs, g.rank_pos, ht⟩⟩
  rcases eq_or_lt_of_le (hg₁min g (Finsupp.mem_support_iff.mpr hs)) with h_eq | h_lt
  · have halttype : Sigma.altType g.rank GeneType.Negative = GeneType.Negative := by
      rw [show g.rank = g₁.rank from h_eq.symm, Sigma.altType_odd g₁.rank hodd]
    rw [halttype] at ht
    exact absurd hXpn (not_not.mpr
      ⟨g₁, g, h_eq, hε_pos, ht, hXg₁pos, Nat.pos_of_ne_zero hs⟩)
  · have := hg₂min g (Nat.pos_of_ne_zero hs) h_lt; omega

private lemma type1_sigma_outside_range_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {g₁ g₂ : Gene} (hle : g₁.rank ≤ g₂.rank) (hpos : 0 < g₁.rank) :
    ∀ j, ¬(g₁.rank ≤ j ∧ j ≤ g₂.rank) →
      Sigma.sigma (Pi.Y1 hε hle hpos).val j =
      Sigma.sigma (Pi.X1 hε hle hpos).val j := by
  intro j hj
  rcases not_and_or.mp hj with h | h
  · simp only [Sigma.sigma, Pi.Y1_eq, Pi.X1_eq, iterate_map_add, prime_iterate_ofRank]
    rw [show g₁.rank - 1 - j = g₁.rank - j - 1 from by omega,
      show g₂.rank + 1 - j = g₂.rank - j + 1 from by omega]
    exact (mutation_type1_signature_eq hε (by omega) (by omega)).symm
  · simp only [Sigma.sigma, Pi.Y1_eq, Pi.X1_eq, iterate_map_add, prime_iterate_ofRank,
      show g₁.rank - j = 0 from by omega, show g₂.rank - j = 0 from by omega,
      show g₁.rank - 1 - j = 0 from by omega, show g₂.rank + 1 - j = 0 from by omega,
      Gene.ofRank_zero, map_zero, add_zero]

private lemma type1_sigma_inside_range_sub_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {g₁ g₂ : Gene} {i : ℕ} (hle : g₁.rank ≤ g₂.rank) (hpos : 0 < g₁.rank)
    (hi1 : g₁.rank ≤ i) (hi2 : i ≤ g₂.rank) :
    Sigma.sigma (Pi.Y1 hε hle hpos).val i -
      Sigma.sigma (Pi.X1 hε hle hpos).val i =
      (Gene.ofRank 1 ε).signature := by
  simp only [Sigma.sigma, Pi.Y1_eq, Pi.X1_eq, iterate_map_add, prime_iterate_ofRank,
    show g₁.rank - i = 0 from Nat.sub_eq_zero_of_le hi1,
    show g₁.rank - 1 - i = 0 from Nat.sub_eq_zero_of_le (by omega),
    Gene.ofRank_zero, zero_add]
  rw [signature_ofRank_general (show 1 ≤ g₂.rank + 1 - i from by omega) hε,
    show g₂.rank + 1 - i - 1 = g₂.rank - i from by omega]
  ring

private lemma fst_zero_gap_le_sub_one_of_fst_one_lt {n : ℕ} (X Y : nPi n)
    (hXY : X.1 ≤ Y.1) (ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1) :
    (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 ≤
      (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 := by
  obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val 1 X.1.2
  obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val 1 Y.1.2
  have hX1 : (Sigma.sigma X.1 1).1 = ↑nX.1 := congr_arg Prod.fst hnX
  have hY1 : (Sigma.sigma Y.1 1).1 = ↑nY.1 := congr_arg Prod.fst hnY
  have hlt : (↑nX.1 : ℚ) < ↑nY.1 := hX1 ▸ hY1 ▸ ha
  have hle : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 :=
    mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hlt)
  linarith [sigma_zero_fst_eq X Y hXY]

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
  let ε := g₁.type
  have hε : ε ≠ .NonPolarized :=
    IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
  have hle : g₁.rank ≤ g₂.rank := le_of_lt hg₂rank
  have hg₁_ofRank : Gene.ofRank g₁.rank ε = Finsupp.single g₁ 1 :=
    Gene.ofRank_eq_gene
  have hg₂_ofRank : Gene.ofRank g₂.rank (-ε) = Finsupp.single g₂ 1 := by
    have h := @Gene.ofRank_eq_gene g₂; rw [hε₂] at h; exact h
  have hsrc_val : (Pi.X1 hε hle g₁.rank_pos : Chromosome) =
      Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
    simp only [Pi.X1_eq]; rw [hg₁_ofRank, hg₂_ofRank]
  have hsrc_le : ∀ g : Gene,
      (Pi.X1 hε hle g₁.rank_pos : Chromosome) g ≤ X.1.val g := by
    have hne : g₁ ≠ g₂ := fun h => absurd hg₂rank (h ▸ lt_irrefl _)
    intro gen
    rw [hsrc_val, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    rcases eq_or_ne gen g₁ with rfl | hng₁
    · simp [Ne.symm hne, hg₁_one]
    · rcases eq_or_ne gen g₂ with rfl | hng₂
      · simpa [Ne.symm hng₁] using hg₂pos
      · simp [Ne.symm hng₁, Ne.symm hng₂]
  let rest : Pi :=
    ⟨X.1.val - (Pi.X1 hε hle g₁.rank_pos : Chromosome),
      Variety.sub_mem_Pi _ X.1.2⟩
  have hdecomp : X.1 = Pi.X1 hε hle g₁.rank_pos + rest :=
    Subtype.val_injective
      (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
  let Z : Pi := Pi.Y1 hε hle g₁.rank_pos + rest
  have hstep : Pi.Step X.1 Z :=
    hdecomp.symm ▸ Pi.Step.mk
      (Pi.X1 hε hle g₁.rank_pos)
      (Pi.Y1 hε hle g₁.rank_pos)
      rest
      (Pi.Primitive.type1 ε hε hle g₁.rank_pos)
  have hZ_le : Z.val ≤ Y.1.val := by
    rw [le_iff_dominates]
    intro i
    change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
    have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
      le_iff_dominates.mp hXY.le i
    have hZ_split : Sigma.sigma Z.val i =
        Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos).val i + Sigma.sigma rest.val i := by
      show Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos + rest : Variety.Pi).val i = _
      simp [Sigma.sigma, iterate_map_add, map_add]
    have hX_split : Sigma.sigma X.1.val i =
        Sigma.sigma (Pi.X1 hε hle g₁.rank_pos).val i + Sigma.sigma rest.val i := by
      have hval : X.1.val = (Pi.X1 hε hle g₁.rank_pos).val + rest.val := by
        have h := congrArg Subtype.val hdecomp
        simpa [AddSubmonoid.coe_add] using h
      simp [hval, Sigma.sigma, iterate_map_add, map_add]
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
        exact type1_sigma_outside_range_eq hε hle g₁.rank_pos
      by_cases heven : Even g₁.rank
      · have hε_neg : ε = .Negative :=
          gene_type_eq_negative_of_even_of_ne_negOnePow_negative heven hε hε₁
        have hb_lt_d_rank : (Sigma.sigma X.1 g₁.rank).2 <
            (Sigma.sigma Y.1 g₁.rank).2 := by
          have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            linarith [sigma_zero_fst_eq X Y hXY.le]
          have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
            (le_iff_dominates.mp hXY.le 1).2
          have hb12_eq : (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 =
            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Positive =
                 Finsupp.single g₁ 1 := by
              exact ofRankAlt_eq_single_of_type_eq_altType <| by
                simpa [Sigma.altType] using
                  gene_type_eq_negOnePow_positive_of_ne_negOnePow_negative hε hε₁
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
          have hd2_gt_b2 : (Sigma.sigma X.1 2).2 < (Sigma.sigma Y.1 2).2 := by
            linarith [hb12_eq, hstrict, hd12_le, hb1_le_d1]
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
            · simp [hrank2]
            · have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 (show g₁.rank - 1 ≥ 2 by omega)
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
          · have hdj_le_d0 : (Sigma.sigma Y.1 j).2 - (Sigma.sigma Y.1 (j + 1)).2 ≤
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
              linarith [sigma_zero_snd_eq X Y hXY.le, (le_iff_dominates.mp hXY.le 1).2]
            have hb0_eq_bj : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 := by
              have hLHS : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    0 < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative),
                  (X.1.val g : ℚ) := by
                have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
                have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
                simpa using h1.trans h2
              have hRHS : (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    j < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Negative),
                  (X.1.val g : ℚ) := by
                have h1 := Sigma.sigma_snd_diff X.1.val j X.1.2
                have h2 := Sigma.prime_iterate_sum_eq X.1.val j GeneType.Negative
                simp only [show Int.negOnePow (j : ℤ) = 1 from
                  Int.negOnePow_even _ (by exact_mod_cast hjeven), one_smul] at h2
                exact h1.trans h2
              rw [hLHS, hRHS, support_filter_negative_eq_tail_of_even hXpn hXg₁pos hg₁min
                hg₂min heven hε_neg hj2]
            linarith
          · have hdj_le_c01 : (Sigma.sigma Y.1 j).2 - (Sigma.sigma Y.1 (j + 1)).2 ≤
                (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
              simpa [hjeven] using Sigma.cond_15_6_compare_k_to_0 Y.1.val j Y.1.2
            have hc01_le_a01_sub1 : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 ≤
                (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 := by
              exact fst_zero_gap_le_sub_one_of_fst_one_lt X Y hXY.le ha
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
              have hRHS : (Sigma.sigma X.1 g₁.rank).1 -
                  (Sigma.sigma X.1 (g₁.rank + 1)).1 =
                  ∑ g ∈ X.1.val.support.filter (fun g =>
                    g₁.rank < g.rank ∧
                    g.type = Sigma.altType g.rank GeneType.Positive),
                  (X.1.val g : ℚ) := by
                rw [Sigma.sigma_fst_diff X.1.val g₁.rank X.1.2,
                    Sigma.prime_iterate_sum_pos_eq X.1.val g₁.rank heven]
                rfl
              have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
                rw [Sigma.altType_even g₁.rank heven, GeneType.neg_positive]; exact hε_neg
              have hdisjoint : Disjoint {g₁} (X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧ g.type =
                  Sigma.altType g.rank GeneType.Positive)) := by
                simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_filter]
                rintro g rfl ⟨_, hlt, _⟩
                exact absurd hlt (lt_irrefl _)
              rw [hLHS, support_filter_rank_pred_altType_split hg₁_one hg₁_altType,
                  Finset.sum_union hdisjoint, Finset.sum_singleton,
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
              rw [hLHS, hRHS, support_filter_tail_eq hg₂min hj1 hj2]
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
            simp at hstep; linarith
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
      · have hodd : Odd g₁.rank := Nat.not_even_iff_odd.mp heven
        have hε_pos : ε = .Positive :=
          gene_type_eq_positive_of_odd_of_ne_negOnePow_negative hodd hε hε₁
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
          · have hcj_le_c01 :
                (Sigma.sigma Y.1 j).1 - (Sigma.sigma Y.1 (j + 1)).1 ≤
                (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
              simpa [hjeven] using Sigma.cond_15_6_compare_k_to_0 Y.1.val j Y.1.2
            have hc01_le_a01_sub1 :
                (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 ≤
                (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 := by
              exact fst_zero_gap_le_sub_one_of_fst_one_lt X Y hXY.le ha
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
              have hdisjoint : Disjoint {g₁} (X.1.val.support.filter (fun g =>
                  g₁.rank < g.rank ∧ g.type =
                  Sigma.altType g.rank GeneType.Positive)) := by
                simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_filter]
                rintro g rfl ⟨_, hlt, _⟩
                exact absurd hlt (lt_irrefl _)
              rw [hLHS, support_filter_rank_pred_altType_split hg₁_one hg₁_altType,
                  Finset.sum_union hdisjoint, Finset.sum_singleton,
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
              rw [hLHS, hRHS, support_filter_tail_eq hg₂min hj1 hj2]
            linarith
          · have hcj_le_c12 :
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
              linarith [sigma_zero_snd_eq X Y hXY.le, (le_iff_dominates.mp hXY.le 1).2]
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
                simpa using h1.trans h2
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
              rw [hLHS, hRHS, support_filter_negative_eq_tail_of_odd hXpn hXg₁pos hg₁min
                hg₂min heven hε_pos hj2]
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
            simp at hstep; linarith
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
      have hdiff := type1_sigma_inside_range_sub_eq hε hle g₁.rank_pos hi1 hi2
      have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
          (Gene.ofRank 1 ε).signature := by
        rw [hZ_split, hX_split, add_sub_add_right_eq_sub]; exact hdiff
      rw [theorem6_sigma_eq_add_of_sub_eq hZX_diff]
      exact hXY_sigma.1 i hi1 hi2
    · rw [hZ_split, hXY_sigma.2 i hin, ← hX_split]; exact hXY_i
  exact ⟨Z, hstep, hZ_le⟩
