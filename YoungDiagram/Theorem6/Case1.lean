import YoungDiagram.Theorem6.Prelim

open Variety hiding prime prime_def
open Chromosome

lemma exists_mutation_le_case1 (m : ℕ)
    (X Y : nPi (m + 2)) (hXY : X.1 < Y.1)
    {g₁ : Gene}
    (ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1)
    (hε₁ : g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Negative)
    (hXg₁ : X.1.val g₁ ≠ 0)
    (hXg₁pos : 0 < X.1.val g₁)
    (hg₁min : ∀ g ∈ X.1.val.support, g₁.rank ≤ g.rank) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg₂_exists : ∃ g₂ : Gene, (g₂.type = Int.negOnePow (g₂.rank - 1) • GeneType.Positive) ∧
   0 < X.1.val g₂ := by
    by_contra hno_g₂
    push Not at hno_g₂
    -- No rank-matching Positive gene in X ⇒ priming once does not decrease a.
    have ha₁_eq_a₀ : (Sigma.sigma X.1 1).1 = (Sigma.sigma X.1 0).1 := by
      simp only [Sigma.sigma, Function.iterate_one, Function.iterate_zero, id]
      rw [signature_prime_fst, signature_fst]
      apply Finsupp.sum_congr
      intro g hg
      congr 1
      have hg_in_X : 0 < X.1.val g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
      have hg_pol : g.type ≠ .NonPolarized :=
        IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g hg
      have hg_neg : g.type = Int.negOnePow (g.rank - 1) • GeneType.Negative :=
        gene_type_eq_negOnePow_negative_of_ne_negOnePow_positive hg_pol
          (fun heq => by have := hno_g₂ g heq; omega)
      have hofRankAlt : Gene.ofRankAlt g.rank GeneType.Negative = Finsupp.single g 1 := by
        rw [Gene.ofRankAlt_eq_gene g.rank_pos]; congr 1; exact Gene.ext rfl hg_neg.symm
      have hkey := signature_prime_ofRankAlt_negative g.rank_pos
      rw [hofRankAlt, prime_single, one_smul, ← primeGene_def] at hkey
      have hfst : (signature (Finsupp.single g 1)).1 = (signature (primeGene g)).1 := by
        have := congr_arg Prod.fst hkey
        simp at this; linarith
      have hsingle : (signature (Finsupp.single g 1)).1 = g.signature.1 := by
        rw [signature_fst, Finsupp.sum_single_index (by simp), Nat.cast_one, one_smul]
      linarith
    have ha₀_eq_c₀ : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 := by
      simp only [Sigma.sigma, Function.iterate_zero, id]
      have hsig_le := (le_iff_dominates.mp hXY.le) 0
      simp only [Function.iterate_zero, id] at hsig_le
      have hXsum := @signature_sum_eq_rank X.1.val
      have hYsum := @signature_sum_eq_rank Y.1.val
      have hXrank : (X.1.val.rank : ℚ) = m + 2 := by exact_mod_cast X.2
      have hYrank : (Y.1.val.rank : ℚ) = m + 2 := by exact_mod_cast Y.2
      obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
      linarith
    have hc₁_le_c₀ : (Sigma.sigma Y.1 1).1 ≤ (Sigma.sigma Y.1 0).1 :=
      (Prod.le_def.mp (Sigma.antitone Y.1 (Nat.zero_le 1))).1
    linarith
  -- Choose g₂ of minimal rank among all g₊-genes in X (Step 2: "choose k minimal").
  have hg₂ : ∃ g₂ : Gene,
      Gene.ofRankAlt g₂.rank GeneType.Positive = Finsupp.single g₂ 1 ∧
      0 < X.1.val g₂ ∧
      ∀ g' : Gene, Gene.ofRankAlt g'.rank GeneType.Positive = Finsupp.single g' 1 →
        0 < X.1.val g' → g₂.rank ≤ g'.rank := by
    have hSne : (X.1.val.support.filter
        (fun g => g.type = Int.negOnePow (g.rank - 1) • GeneType.Positive)).Nonempty := by
      obtain ⟨g, hgtype, hgpos⟩ := hg₂_exists
      exact ⟨g, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hgpos.ne', hgtype⟩⟩
    obtain ⟨g₂, hg₂S, hg₂min⟩ := Finset.exists_min_image _ Gene.rank hSne
    rw [Finset.mem_filter] at hg₂S
    refine ⟨g₂,
      by rw [Gene.ofRankAlt_eq_gene g₂.rank_pos]; congr 1; exact Gene.ext rfl hg₂S.2.symm,
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂S.1),
      fun g' hg'_eq hg'pos => hg₂min g' (Finset.mem_filter.mpr
        ⟨Finsupp.mem_support_iff.mpr hg'pos.ne', by
          have h := (Gene.ofRankAlt_eq_gene g'.rank_pos).symm.trans hg'_eq
          exact (congr_arg Gene.type
            ((Finsupp.single_left_inj one_ne_zero).mp h)).symm⟩)⟩
  obtain ⟨g₂, hg₂type, hg₂pos, hg₂min⟩ := hg₂
  -- The type-3 mutation g₋(g₁.rank) + g₊(g₂.rank) → g₊(g₁.rank−1) + g₋(g₂.rank+1).
  have hε_neg : GeneType.Negative ≠ .NonPolarized := by decide
  have hle_ranks : g₁.rank ≤ g₂.rank :=
    hg₁min g₂ (Finsupp.mem_support_iff.mpr hg₂pos.ne')
  have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Negative = Finsupp.single g₁ 1 := by
    rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]; congr 1; exact Gene.ext rfl hε₁.symm
  have hg₂_type_eq : g₂.type = Int.negOnePow (g₂.rank - 1) • GeneType.Positive :=
    (congr_arg Gene.type ((Finsupp.single_left_inj one_ne_zero).mp
      ((Gene.ofRankAlt_eq_gene g₂.rank_pos).symm.trans hg₂type))).symm
  -- g₁ ≠ g₂ since their types are incompatible (Negative-family vs Positive-family).
  have hg₁g₂_ne : g₁ ≠ g₂ := fun heq => by
    rw [← heq, hε₁] at hg₂_type_eq
    simp only [GeneType.negOnePow_smul, GeneType.neg_negative, GeneType.neg_positive]
      at hg₂_type_eq
    split_ifs at hg₂_type_eq
  have hsrc_val : (Pi.X3 hε_neg hle_ranks g₁.rank_pos : Chromosome) =
      Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
    simp only [Pi.X3_eq, GeneType.neg_negative]; rw [hg₁_ofRankAlt, hg₂type]
  have hsrc_le : ∀ g : Gene,
      (Pi.X3 hε_neg hle_ranks g₁.rank_pos : Chromosome) g ≤ X.1.val g := by
    intro g
    rw [hsrc_val, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    rcases eq_or_ne g g₁ with rfl | hne₁
    · simp only [↓reduceIte, if_neg (Ne.symm hg₁g₂_ne)]; exact hXg₁pos
    · rcases eq_or_ne g g₂ with rfl | hne₂
      · simp only [if_neg (Ne.symm hne₁), ↓reduceIte, zero_add]; exact hg₂pos
      · simp only [if_neg (Ne.symm hne₁), if_neg (Ne.symm hne₂), add_zero, Nat.zero_le]
  let rest : Pi :=
    ⟨X.1.val - (Pi.X3 hε_neg hle_ranks g₁.rank_pos : Chromosome),
      Variety.sub_mem_Pi _ X.1.2⟩
  have hdecomp : X.1 = Pi.X3 hε_neg hle_ranks g₁.rank_pos + rest :=
    Subtype.val_injective
      (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
  let Z : Pi := Pi.Y3 hε_neg hle_ranks g₁.rank_pos + rest
  have hstep : Pi.Step X.1 Z :=
    hdecomp.symm ▸ Pi.Step.mk
      (Pi.X3 hε_neg hle_ranks g₁.rank_pos)
      (Pi.Y3 hε_neg hle_ranks g₁.rank_pos)
      rest
      (Pi.Primitive.type3 GeneType.Negative hε_neg hle_ranks g₁.rank_pos)
  -- Step 4: σ(Z) = σ(X) + alternating increment on [g₁.rank, g₂.rank], zero elsewhere.
  -- The type-3 mutation with ε = Negative adds (1,0) at odd columns and (0,1) at even
  -- columns within [g₁.rank, g₂.rank], and is the identity outside this range.
  have hstep4 : ∀ i : ℕ,
      Sigma.sigma Z.val i =
      Sigma.sigma X.1.val i +
      if g₁.rank ≤ i ∧ i ≤ g₂.rank then
        if Even i then (0, 1) else (1, 0)
      else (0, 0) := by
    intro i
    have sigma_add : ∀ (A B : Chromosome),
        Sigma.sigma (A + B) i = Sigma.sigma A i + Sigma.sigma B i :=
      fun A B => by simp only [Sigma.sigma, iterate_map_add, map_add]
    have hZ_split : Sigma.sigma Z.val i =
        Sigma.sigma (Pi.Y3 hε_neg hle_ranks g₁.rank_pos).val i +
        Sigma.sigma rest.val i := by
      change Sigma.sigma (Pi.Y3 hε_neg hle_ranks g₁.rank_pos + rest : Variety.Pi).val i = _
      simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
    have hX_split : Sigma.sigma X.1.val i =
        Sigma.sigma (Pi.X3 hε_neg hle_ranks g₁.rank_pos).val i +
        Sigma.sigma rest.val i := by
      have hval : X.1.val = (Pi.X3 hε_neg hle_ranks g₁.rank_pos).val + rest.val := by
        have h := congrArg Subtype.val hdecomp
        simpa [AddSubmonoid.coe_add] using h
      rw [hval, sigma_add]
    rw [hZ_split, hX_split, Sigma.mutation_type3_sigma_eq hε_neg hle_ranks g₁.rank_pos i]
    simp only [GeneType.neg_negative, signature_ofRank_one_negative,
      signature_ofRank_one_positive]
    abel
  refine ⟨Z, hstep, ?_⟩
  -- Case split on the parity of k = g₂.rank.
  rcases Nat.even_or_odd g₂.rank with ⟨j, hk_even⟩ | ⟨j, hk_odd⟩
  · -- k even: g₂.rank = 2 * j
    have hXchain : ∀ i : ℕ, i < g₂.rank →
        (if Even i then (Sigma.sigma X.1 i).1 - (Sigma.sigma X.1 (i + 1)).1
         else (Sigma.sigma X.1 i).2 - (Sigma.sigma X.1 (i + 1)).2) =
        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 :=
          fun i hi => x_side_equalities hg₂min hi
    have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
      have ha₀ := sigma_zero_fst_eq X Y hXY.le
      linarith
    change Z.val ≤ Y.1.val
    rw [le_iff_dominates]
    intro i
    change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
    have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
      le_iff_dominates.mp hXY.le i
    rw [hstep4 i]
    split_ifs with hin heven
    · -- In range, even i: σ(Z)(i) = σ(X)(i) + (0, 1), increment at .2 component.
      suffices h : (Sigma.sigma X.1.val i).2 < (Sigma.sigma Y.1.val i).2 by
        constructor
        · calc (Sigma.sigma X.1.val i + ((0, 1) : ℚ × ℚ)).1
              = (Sigma.sigma X.1.val i).1 + 0 := rfl
            _ ≤ (Sigma.sigma Y.1.val i).1 := by linarith [hXY_i.1]
        · obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.1.2 (k := i))
          obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.1.2 (k := i))
          simp only [Sigma.sigma] at h ⊢
          simp only [Prod.snd_add]
          rw [hnX, hnY] at h ⊢
          simp only at h ⊢
          have hnXY : nX.2 < nY.2 := Nat.cast_lt.mp h
          exact_mod_cast Nat.add_one_le_iff.mpr hnXY
      -- No hi_lt needed: i ≤ g₂.rank and 1 ≤ i give i-1 < g₂.rank directly.
      have hi_pos : 1 ≤ i := Nat.le_trans g₁.rank_pos hin.1
      have hpred_odd : ¬Even (i - 1) := by
        simp only [Nat.even_iff] at *; omega
      have hX_eq : (Sigma.sigma X.1 (i - 1)).2 - (Sigma.sigma X.1 i).2 =
          (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
        have h := hXchain (i - 1) (by omega)
        simp only [if_neg hpred_odd] at h
        rwa [Nat.sub_add_cancel hi_pos] at h
      have hY_le : (Sigma.sigma Y.1.val (i - 1)).2 - (Sigma.sigma Y.1.val i).2 ≤
          (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
        have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (i - 1) Y.1.2
        simp only [if_neg hpred_odd] at h
        rwa [Nat.sub_add_cancel hi_pos] at h
      have hXY_pred : (Sigma.sigma X.1.val (i - 1)).2 ≤ (Sigma.sigma Y.1.val (i - 1)).2 :=
        (le_iff_dominates.mp hXY.le (i - 1)).2
      linarith [hX_eq, hY_le, hstrict, hXY_pred]
    · -- In range, odd i: σ(Z)(i) = σ(X)(i) + (1, 0), increment at .1 component.
      suffices h : (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.1.val i).1 by
        constructor
        · obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.1.2 (k := i))
          obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.1.2 (k := i))
          simp only [Sigma.sigma] at h ⊢
          simp only [Prod.fst_add]
          rw [hnX, hnY] at h ⊢
          simp only at h ⊢
          have hnXY : nX.1 < nY.1 := Nat.cast_lt.mp h
          exact_mod_cast Nat.add_one_le_iff.mpr hnXY
        · calc (Sigma.sigma X.1.val i + ((1, 0) : ℚ × ℚ)).2
              = (Sigma.sigma X.1.val i).2 + 0 := rfl
            _ ≤ (Sigma.sigma Y.1.val i).2 := by linarith [hXY_i.2]
      have hi_pos : 1 ≤ i := Nat.le_trans g₁.rank_pos hin.1
      have hpred_even : Even (i - 1) := by
        simp only [Nat.even_iff] at *; omega
      have hX_eq : (Sigma.sigma X.1 (i - 1)).1 - (Sigma.sigma X.1 i).1 =
          (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
        have h := hXchain (i - 1) (by omega)
        simp only [if_pos hpred_even] at h
        rwa [Nat.sub_add_cancel hi_pos] at h
      have hY_le : (Sigma.sigma Y.1.val (i - 1)).1 - (Sigma.sigma Y.1.val i).1 ≤
          (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
        have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (i - 1) Y.1.2
        simp only [if_pos hpred_even] at h
        rwa [Nat.sub_add_cancel hi_pos] at h
      have hXY_pred : (Sigma.sigma X.1.val (i - 1)).1 ≤ (Sigma.sigma Y.1.val (i - 1)).1 :=
        (le_iff_dominates.mp hXY.le (i - 1)).1
      linarith [hX_eq, hY_le, hstrict, hXY_pred]
    · -- Outside mutation range: σ(Z)(i) = σ(X)(i) + (0,0) = σ(X)(i) ≤ σ(Y)(i).
      have h00 : ((0, 0) : ℚ × ℚ) = 0 := rfl
      rw [h00, add_zero]
      exact hXY_i
  · -- k odd: g₂.rank = 2 * j + 1
    -- Step 5: chain of inequalities.
    -- 5a (X-side equalities, proved): for all i < g₂.rank, the alternating sigma-difference
    -- of X equals P = (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1.
    have hXchain : ∀ i : ℕ, i < g₂.rank →
        (if Even i then (Sigma.sigma X.1 i).1 - (Sigma.sigma X.1 (i + 1)).1
         else (Sigma.sigma X.1 i).2 - (Sigma.sigma X.1 (i + 1)).2) =
        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 :=
          fun i hi => x_side_equalities hg₂min hi
    -- 5b (Y-side weak chain): alternating sigma-differences of Y are non-increasing
    -- This is sigma.cond_15_6_compare_k_to_0
    -- 5c (strict inequality): a₀ = c₀ and a₁ < c₁ give c₀ - c₁ < P.
    have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
      have ha₀ := sigma_zero_fst_eq X Y hXY.le
      linarith
    -- Step 6: telescoping to conclude Z ≤ Y.1.
    -- The mutation adds alternating (1,0)/(0,1) increments to σ(X) on [g₁.rank, g₂.rank].
    -- At each such column the strict inequality from step 5 (combined with X ≤ Y elsewhere)
    -- absorbs the increment.
    change Z.val ≤ Y.1.val
    rw [le_iff_dominates]
    intro i
    -- Unfold sigma so that hstep4 can rewrite the goal.
    change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
    -- Weak X ≤ Y at column i, componentwise (with explicit Sigma.sigma type).
    have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
      le_iff_dominates.mp hXY.le i
    -- Rewrite σ(Z)(i) using the mutation increment formula.
    rw [hstep4 i]
    -- split_ifs handles the three branches: in-range even, in-range odd, out-of-range.
    split_ifs with hin heven
    · -- In range, even i: σ(Z)(i) = σ(X)(i) + (0, 1), increment at .2 component.
      -- Suffices: (σ(X)(i)).2 < (σ(Y)(i)).2; integrality gives (σ(X)(i)).2 + 1 ≤ (σ(Y)(i)).2.
      suffices h : (Sigma.sigma X.1.val i).2 < (Sigma.sigma Y.1.val i).2 by
        constructor
        · -- (σ(X)(i) + (0,1)).1 = (σ(X)(i)).1 + 0 ≤ (σ(Y)(i)).1
          calc (Sigma.sigma X.1.val i + ((0, 1) : ℚ × ℚ)).1
              = (Sigma.sigma X.1.val i).1 + 0 := rfl
            _ ≤ (Sigma.sigma Y.1.val i).1 := by linarith [hXY_i.1]
        · -- (σ(X)(i)).2 + 1 ≤ (σ(Y)(i)).2: sigma values of Pi-chromosomes are integers,
          -- so strict inequality implies gap ≥ 1.
          obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.1.2 (k := i))
          obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.1.2 (k := i))
          simp only [Sigma.sigma] at h ⊢
          simp only [Prod.snd_add]
          rw [hnX, hnY] at h ⊢
          simp only at h ⊢
          have hnXY : nX.2 < nY.2 := Nat.cast_lt.mp h
          exact_mod_cast Nat.add_one_le_iff.mpr hnXY
      -- Step 1: predecessor i-1 exists (i ≥ 1) and is odd (i is even and i ≠ g₂.rank)
      have hi_pos : 1 ≤ i := Nat.le_trans g₁.rank_pos hin.1
      have hi_lt : i < g₂.rank := by
        rcases Nat.lt_or_eq_of_le hin.2 with h | h
        · exact h
        · exact absurd heven (h ▸ hk_odd ▸ Nat.not_even_two_mul_add_one j)
      have hpred_odd : ¬Even (i - 1) := by
        simp only [Nat.even_iff] at *
        omega
      -- Step 2: X's .2-component difference at i-1 equals P
      have hX_eq : (Sigma.sigma X.1 (i - 1)).2 - (Sigma.sigma X.1 i).2 =
          (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
        have h := hXchain (i - 1) (by omega)
        simp only [if_neg hpred_odd] at h
        rwa [Nat.sub_add_cancel hi_pos] at h
      -- Step 3: Y's .2-component difference at i-1 is ≤ c₀ − c₁
      have hY_le : (Sigma.sigma Y.1.val (i - 1)).2 - (Sigma.sigma Y.1.val i).2 ≤
          (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
        have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (i - 1) Y.1.2
        simp only [if_neg hpred_odd] at h
        rwa [Nat.sub_add_cancel hi_pos] at h
      -- Step 4: Y dominates X at column i-1 in the .2 component
      have hXY_pred : (Sigma.sigma X.1.val (i - 1)).2 ≤ (Sigma.sigma Y.1.val (i - 1)).2 :=
        (le_iff_dominates.mp hXY.le (i - 1)).2
      -- Step 5: chain c₀-c₁ < P = σX(i-1).2 - σX(i).2 with σX(i-1).2 ≤ σY(i-1).2
      linarith [hX_eq, hY_le, hstrict, hXY_pred]
    · -- In range, odd i: σ(Z)(i) = σ(X)(i) + (1, 0), increment at .1 component.
      -- Suffices: (σ(X)(i)).1 < (σ(Y)(i)).1; integrality gives (σ(X)(i)).1 + 1 ≤ (σ(Y)(i)).1.
      suffices h : (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.1.val i).1 by
        constructor
        · -- (σ(X)(i)).1 + 1 ≤ (σ(Y)(i)).1: follows from h by integrality.
          obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val i X.1.2
          obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val i Y.1.2
          rw [hnX, hnY] at h ⊢
          simp only [Prod.fst_add] at h ⊢
          exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp h)
        · -- (σ(X)(i) + (1,0)).2 = (σ(X)(i)).2 + 0 ≤ (σ(Y)(i)).2
          calc (Sigma.sigma X.1.val i + ((1, 0) : ℚ × ℚ)).2
              = (Sigma.sigma X.1.val i).2 + 0 := rfl
            _ ≤ (Sigma.sigma Y.1.val i).2 := by linarith [hXY_i.2]
      -- Step 1: predecessor i-1 exists (i ≥ 1) and is even (i is odd)
      have hi_pos : 1 ≤ i := Nat.le_trans g₁.rank_pos hin.1
      have hpred_even : Even (i - 1) := by
        simp only [Nat.even_iff] at *
        omega
      -- Step 2: X's .1-component difference at i-1 equals P
      have hX_eq : (Sigma.sigma X.1 (i - 1)).1 - (Sigma.sigma X.1 i).1 =
          (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
        have h := hXchain (i - 1) (by omega)
        simp only [if_pos hpred_even] at h
        rwa [Nat.sub_add_cancel hi_pos] at h
      -- Step 3: Y's .1-component difference at i-1 is ≤ c₀ − c₁
      have hY_le : (Sigma.sigma Y.1.val (i - 1)).1 - (Sigma.sigma Y.1.val i).1 ≤
          (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
        have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (i - 1) Y.1.2
        simp only [if_pos hpred_even] at h
        rwa [Nat.sub_add_cancel hi_pos] at h
      -- Step 4: Y dominates X at column i-1 in the .1 component
      have hXY_pred : (Sigma.sigma X.1.val (i - 1)).1 ≤ (Sigma.sigma Y.1.val (i - 1)).1 :=
        (le_iff_dominates.mp hXY.le (i - 1)).1
      -- Step 5: chain c₀-c₁ < P = σX(i-1).1 - σX(i).1 with σX(i-1).1 ≤ σY(i-1).1
      linarith [hX_eq, hY_le, hstrict, hXY_pred]
    · -- Outside mutation range: σ(Z)(i) = σ(X)(i) + (0,0) = σ(X)(i) ≤ σ(Y)(i).
      have h00 : ((0, 0) : ℚ × ℚ) = 0 := rfl
      rw [h00, add_zero]
      exact hXY_i
