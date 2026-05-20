import YoungDiagram.Theorem6.Prelim

open Variety hiding prime prime_def
open Chromosome

lemma exists_mutation_le_case2
    {n : ℕ} (X Y : nPi n) (hXY : X.1 < Y.1)
    {g₁ : Gene}
    (ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1)
    (hε₁ : ¬ g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Negative)
    (hXg₁ : X.1.val g₁ ≠ 0)
    (hXg₁pos : 0 < X.1.val g₁)
    (hg₁_one : g₁.rank = 1) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hb₀_eq_d₀ : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
    sigma_zero_snd_eq X Y hXY.le
  have hb₀_gt_a₁ : (Sigma.sigma X.1 1).1 < (Sigma.sigma X.1 0).2 := by
    have hd₀_ge_c₁ : (Sigma.sigma Y.1 1).1 ≤ (Sigma.sigma Y.1 0).2 := by
      have h := Sigma.cond_15_5 Y.1.val 0
      rw [if_pos (by norm_num : Even (0 : ℕ))] at h; exact h
    linarith [hb₀_eq_d₀]
  have hg₂_neg : ∃ g₂ : Gene,
      g₂.type = .Negative ∧
      0 < X.1.val g₂ ∧
      ∀ g' : Gene, g'.type = .Negative → 0 < X.1.val g' → g₂.rank ≤ g'.rank := by
    have hSne : (X.1.val.support.filter (fun g => g.type = .Negative)).Nonempty := by
      obtain ⟨g, hgtype, hgpos⟩ := Sigma.neg_gene_of_b0_gt_a1 X.1.val X.1.2 hb₀_gt_a₁
      exact ⟨g, Finset.mem_filter.mpr
        ⟨Finsupp.mem_support_iff.mpr hgpos.ne', hgtype⟩⟩
    obtain ⟨g₂, hg₂S, hg₂min⟩ := Finset.exists_min_image _ Gene.rank hSne
    rw [Finset.mem_filter] at hg₂S
    exact ⟨g₂, hg₂S.2,
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂S.1),
      fun g' hg'_neg hg'_pos => hg₂min g'
        (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hg'_pos.ne', hg'_neg⟩)⟩
  obtain ⟨g₂, hg₂_type, hg₂_pos, hg₂_min⟩ := hg₂_neg
  -- g₁ has type Positive (not Negative from hε₁, not NonPolarized from polarization).
  have hg₁_type : g₁.type = .Positive := by
    have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁
      (Finsupp.mem_support_iff.mpr hXg₁)
    cases ht : g₁.type with
    | Positive => rfl
    | NonPolarized => exact absurd ht hpol
    | Negative =>
      exfalso; apply hε₁
      rw [ht, hg₁_one]; simp
  -- g₁ ≠ g₂ (Positive vs Negative types are distinct).
  have hg₁g₂_ne : g₁ ≠ g₂ := fun heq => by
    rw [← heq, hg₁_type] at hg₂_type; exact absurd hg₂_type (by decide)
  -- Hypotheses for Pi.Primitive.type1 (ε = Positive, m = 1, n = g₂.rank).
  have hε_pos : GeneType.Positive ≠ .NonPolarized := by decide
  have hle_ranks : 1 ≤ g₂.rank := g₂.rank_pos
  -- ofRank 1 .Positive = single g₁ 1 (using g₁.rank = 1, g₁.type = .Positive).
  have hg₁_ofRank : Gene.ofRank 1 GeneType.Positive = Finsupp.single g₁ 1 := by
    have h := @Gene.ofRank_eq_gene g₁; rw [hg₁_one, hg₁_type] at h; exact h
  -- ofRank g₂.rank .Negative = single g₂ 1 (using g₂.type = .Negative).
  have hg₂_ofRank : Gene.ofRank g₂.rank GeneType.Negative = Finsupp.single g₂ 1 := by
    have h := @Gene.ofRank_eq_gene g₂; rw [hg₂_type] at h; exact h
  -- The type1 source chromosome equals single g₁ 1 + single g₂ 1.
  have hsrc_val : (Pi.X1 hε_pos hle_ranks (le_refl 1) : Chromosome) =
      Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
    simp only [Pi.X1_eq, GeneType.neg_positive]; rw [hg₁_ofRank, hg₂_ofRank]
  -- src ≤ X.1.val pointwise.
  have hsrc_le : ∀ g : Gene,
      (Pi.X1 hε_pos hle_ranks (le_refl 1) : Chromosome) g ≤ X.1.val g := by
    intro g
    rw [hsrc_val, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    rcases eq_or_ne g g₁ with rfl | hne₁
    · simp only [↓reduceIte, if_neg (Ne.symm hg₁g₂_ne)]; exact hXg₁pos
    · rcases eq_or_ne g g₂ with rfl | hne₂
      · simp only [if_neg (Ne.symm hne₁), ↓reduceIte, zero_add]; exact hg₂_pos
      · simp only [if_neg (Ne.symm hne₁), if_neg (Ne.symm hne₂), add_zero, Nat.zero_le]
  -- rest = X.1 − src, still in Pi.
  let rest : Pi :=
    ⟨X.1.val - (Pi.X1 hε_pos hle_ranks (le_refl 1) : Chromosome),
      Variety.sub_mem_Pi _ X.1.2⟩
  -- X.1 decomposes as src + rest.
  have hdecomp : X.1 = Pi.X1 hε_pos hle_ranks (le_refl 1) + rest :=
    Subtype.val_injective
      (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
  -- Z is the type1 mutation result: ofRank (g₂.rank+1) .Positive + rest.
  let Z : Pi := Pi.Y1 hε_pos hle_ranks (le_refl 1) + rest
  -- Construct the Pi-step.
  have hstep : Pi.Step X.1 Z :=
    hdecomp.symm ▸ Pi.Step.mk
      (Pi.X1 hε_pos hle_ranks (le_refl 1))
      (Pi.Y1 hε_pos hle_ranks (le_refl 1))
      rest
      (Pi.Primitive.type1 GeneType.Positive hε_pos hle_ranks (le_refl 1))
  have hsigma_diff_XZ : ∀ i : ℕ, 1 ≤ i → i ≤ g₂.rank →
      (Sigma.sigma Z.val i) - (Sigma.sigma X.val i) = (1, 0) := by
    intro i i_lb i_ub
    simp [Z, hdecomp, Sigma.sigma_linearity, Pi.Y1_eq, Pi.X1_eq]
    simp [Sigma.sigma]
    simp [prime_iterate_ofRank]
    have : 1 - i = 0 := by omega
    simp [this]
    simp [signature_ofRank_positive (by omega : 1 ≤ g₂.rank + 1 - i),
        show g₂.rank + 1 - i - 1 = g₂.rank - i from by omega]
  have hsigma_diff_XY : ∀ i : ℕ, 1 ≤ i → i ≤ g₂.rank →
      (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.val i).1 := by
    intro i i_lb i_ub
    exact caseA2_strict_fst X Y hXY hg₂_min hb₀_eq_d₀ ha i_lb i_ub
  exact ⟨Z, hstep, by
    change Z.val ≤ Y.1.val
    rw [le_iff_dominates]
    intro i
    change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
    have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
      le_iff_dominates.mp hXY.le i
    by_cases hin : 1 ≤ i ∧ i ≤ g₂.rank
    · obtain ⟨hi1, hi2⟩ := hin
      have hdiff := hsigma_diff_XZ i hi1 hi2
      have hlt := hsigma_diff_XY i hi1 hi2
      -- Extract component equations: Z.1 = X.1 + 1 and Z.2 = X.2
      have hfst : (Sigma.sigma Z.val i).1 = (Sigma.sigma X.1.val i).1 + 1 := by
        have h : (Sigma.sigma Z.val i).1 - (Sigma.sigma X.1.val i).1 = 1 :=
          calc (Sigma.sigma Z.val i).1 - (Sigma.sigma X.1.val i).1
              = (Sigma.sigma Z.val i - Sigma.sigma X.val i).1 := rfl
            _ = ((1 : ℚ), (0 : ℚ)).1 := congr_arg Prod.fst hdiff
            _ = 1 := rfl
        linarith
      have hsnd : (Sigma.sigma Z.val i).2 = (Sigma.sigma X.1.val i).2 := by
        have h : (Sigma.sigma Z.val i).2 - (Sigma.sigma X.1.val i).2 = 0 :=
          calc (Sigma.sigma Z.val i).2 - (Sigma.sigma X.1.val i).2
              = (Sigma.sigma Z.val i - Sigma.sigma X.val i).2 := rfl
            _ = ((1 : ℚ), (0 : ℚ)).2 := congr_arg Prod.snd hdiff
            _ = 0 := rfl
        linarith
      constructor
      · -- (Z).1 = (X).1 + 1 ≤ (Y).1: (X).1 < (Y).1 strict, integrality absorbs the +1
        rw [hfst]
        suffices h : (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.1.val i).1 by
          obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val i X.1.2
          obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val i Y.1.2
          rw [hnX, hnY] at h ⊢
          simp only at h ⊢
          exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp h)
        exact hlt
      · -- (Z).2 = (X).2 ≤ (Y).2: no increment in second component
        linarith [hsnd, hXY_i.2]
    · push Not at hin
      -- Outside [1, g₂.rank]: type1 mutation does not alter sigma at i
      have hZ_eq : Sigma.sigma Z.val i = Sigma.sigma X.1.val i := by
        -- Split Z = Y1 + rest and X.1 = X1 + rest, reducing to sigma Y1 i = sigma X1 i
        have hZ_split : Sigma.sigma Z.val i =
            Sigma.sigma (Pi.Y1 hε_pos hle_ranks (le_refl 1)).val i +
            Sigma.sigma rest.val i := by
          change Sigma.sigma (Pi.Y1 hε_pos hle_ranks (le_refl 1) + rest : Variety.Pi).val i =
           _
          simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
        have hX_split : Sigma.sigma X.1.val i =
            Sigma.sigma (Pi.X1 hε_pos hle_ranks (le_refl 1)).val i +
            Sigma.sigma rest.val i := by
          have hval : X.1.val = (Pi.X1 hε_pos hle_ranks (le_refl 1)).val + rest.val := by
            have h := congrArg Subtype.val hdecomp
            simp only [AddSubmonoid.coe_add] at h; exact h
          simp only [hval, Sigma.sigma, iterate_map_add, map_add]
        suffices h : Sigma.sigma (Pi.Y1 hε_pos hle_ranks (le_refl 1)).val i =
                     Sigma.sigma (Pi.X1 hε_pos hle_ranks (le_refl 1)).val i by
          rw [hZ_split, hX_split, h]
        -- push_neg gives hin : 1 ≤ i → g₂.rank < i; case split on whether 1 ≤ i
        by_cases hi1 : 1 ≤ i
        · -- i ≥ 1, so i > g₂.rank from hin
          have hi_gt : g₂.rank < i := hin hi1
          -- prime^[i] kills all genes in X1 (ranks 1, g₂.rank) and Y1 (rank g₂.rank+1)
          have hX1_zero : Sigma.sigma (Pi.X1 hε_pos hle_ranks (le_refl 1)).val i = 0 := by
            simp only [Sigma.sigma, Pi.X1_eq, GeneType.neg_positive, iterate_map_add,
                       prime_iterate_ofRank,
                       show 1 - i = 0 from by omega,
                       show g₂.rank - i = 0 from by omega,
                       Gene.ofRank_zero, map_zero, add_zero]
          have hY1_zero : Sigma.sigma (Pi.Y1 hε_pos hle_ranks (le_refl 1)).val i = 0 := by
            simp only [Sigma.sigma, Pi.Y1_eq, GeneType.neg_positive, prime_iterate_ofRank,
                       show (1 : ℕ) - 1 = 0 from rfl, Gene.ofRank_zero,
                       show g₂.rank + 1 - i = 0 from by omega,
                       map_zero, zero_add]
          rw [hY1_zero, hX1_zero]
        · -- i = 0: mutation_type1_signature_eq gives equal signatures at level 0
          have hi : i = 0 := by omega
          subst hi
          simp only [Sigma.sigma, Function.iterate_zero, id, Pi.Y1_eq, Pi.X1_eq]
          exact (mutation_type1_signature_eq hε_pos hle_ranks (le_refl 1)).symm
      rw [hZ_eq]
      exact hXY_i⟩
