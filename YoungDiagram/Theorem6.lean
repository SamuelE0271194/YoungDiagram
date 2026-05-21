import YoungDiagram.Theorem6.Case1
import YoungDiagram.Theorem6.Case2
import YoungDiagram.Theorem6.Case3
import YoungDiagram.Theorem6.Case4A

open Variety hiding prime prime_def
open Chromosome

set_option maxHeartbeats 0

/-! ## (15.10): X has no positive-negative gene pair of equal rank -/
/-- Dispatcher for Cases 1–4 of §15.10.  The completed subcases live in
`YoungDiagram.Theorem6.Case1`, `.Case2`, `.Case3`, and `.Case4A`. -/
private lemma exists_mutation_le_fifteen_ten (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X.1 k = Sigma.sigma Y.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  -- From hsigeq: for k ≥ 1 with Y^(k) ≠ 0, sigma X k ≠ sigma Y k.
  -- Combined with X < Y: (a_k, b_k) ≤ (c_k, d_k), so a_k < c_k or b_k < d_k.
  -- Split: either some k has a_k < c_k, or for all such k a_k = c_k (so b_k < d_k).
  -- From hsigeq: for k ≥ 1 with Y^(k) ≠ 0, sigma X k ≠ sigma Y k.
  -- Split on Case A (a₁ < c₁) vs Case B (a₁ = c₁, so b₁ < d₁).
  by_cases ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1
  · -- Case A: a₁ < c₁ (paper §15.10, Cases 1–4).
    -- Let g₁ = g_{ε₁}(m) be the gene of minimal rank m in X (paper §15, p.30).
    have hXne : X.1.val ≠ 0 := by
      intro h; have := X.2; rw [h, rank_def, Finsupp.sum_zero_index] at this; omega
    obtain ⟨g₁, hXg₁, hg₁min⟩ := Finset.exists_min_image X.1.val.support Gene.rank
      (Finsupp.support_nonempty_iff.mpr hXne)
    rw [Finsupp.mem_support_iff] at hXg₁
    have hXg₁pos : 0 < X.1.val g₁ := Nat.pos_of_ne_zero hXg₁

    by_cases hε₁ : g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Negative
    · -- Case 1: ε₁ = − (i.e. g₁ = Gene.ofRankAlt g₁.rank .Negative as a Gene term).
      exact exists_mutation_le_case1 m X Y hXY ha hε₁ hXg₁ hXg₁pos hg₁min
    · -- Cases 2-4
      by_cases hg₁_one : g₁.rank = 1
      · -- g₁.rank = 1 (case 2)
        exact exists_mutation_le_case2 X Y hXY ha hε₁ hXg₁ hXg₁pos hg₁_one
      · -- g₁.rank ≥ 2 (Case 3-4)
        have hg₁_ge2 : 2 ≤ g₁.rank := by
          have := g₁.rank_pos; omega
        by_cases h2g₁ : 2 ≤ X.1.val g₁
        · exact exists_mutation_le_case3 X Y hXY hXpn ha hε₁ hXg₁ hXg₁pos hg₁min hg₁_ge2 h2g₁
        · -- Case 4: g₁ appears with multiplicity 1 in X
          have hg₁_one : X.1.val g₁ = 1 := by omega
          have hprime_rank_ne_zero : prime^[g₁.rank] X.1.val ≠ 0 := by
            -- If prime^[g₁.rank] X = 0, we show X = single g₁ 1 and derive a contradiction.
            have hX_eq_g₁ : prime^[g₁.rank] X.1.val = 0 → X.1.val = Finsupp.single g₁ 1 := by
              intro hzero
              -- All genes in X have rank ≤ g₁.rank (prime_iterate_eq_zero_rank_le)
              have hrank_le : ∀ g ∈ X.1.val.support, g.rank ≤ g₁.rank :=
                fun g hg => prime_iterate_eq_zero_rank_le.2 hzero g hg
              -- Combined with hg₁min (minimal rank ≥ g₁.rank): rank = g₁.rank exactly
              have hrank_eq : ∀ g ∈ X.1.val.support, g.rank = g₁.rank :=
                fun g hg => le_antisymm (hrank_le g hg) (hg₁min g hg)
              -- All genes have type = g₁.type (else hXpn gives a pos-neg pair of equal rank)
              have htype_eq : ∀ g ∈ X.1.val.support, g.type = g₁.type := by
                intro g hg
                have hg_pol : g.type ≠ .NonPolarized :=
                  IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g hg
                have hg₁_pol : g₁.type ≠ .NonPolarized :=
                  IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
                by_contra hne
                apply hXpn
                cases ht : g.type with
                | NonPolarized => exact absurd ht hg_pol
                | Positive =>
                  have hg₁_neg : g₁.type = .Negative := by
                    cases ht₁ : g₁.type with
                    | NonPolarized => exact absurd ht₁ hg₁_pol
                    | Positive => exact False.elim (hne (ht.trans ht₁.symm))
                    | Negative => rfl
                  exact ⟨g, g₁, hrank_eq g hg, ht, hg₁_neg,
                    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg), hXg₁pos⟩
                | Negative =>
                  have hg₁_pos : g₁.type = .Positive := by
                    cases ht₁ : g₁.type with
                    | NonPolarized => exact absurd ht₁ hg₁_pol
                    | Negative => exact False.elim (hne (ht.trans ht₁.symm))
                    | Positive => rfl
                  exact ⟨g₁, g, (hrank_eq g hg).symm, hg₁_pos, ht,
                    hXg₁pos, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)⟩
              -- Every gene in the support equals g₁ (same rank and type)
              have hall_g₁ : ∀ g ∈ X.1.val.support, g = g₁ :=
                fun g hg => Gene.ext (hrank_eq g hg) (htype_eq g hg)
              -- X.1.val = single g₁ 1 since support ⊆ {g₁} and X.1.val g₁ = 1
              ext g
              rcases eq_or_ne g g₁ with rfl | hne
              · simp [hg₁_one]
              · have hg_zero : X.1.val g = 0 := by
                  by_contra h
                  exact hne (hall_g₁ g (Finsupp.mem_support_iff.mpr h))
                simp [hg_zero, hne]
            intro hzero
            have hX_rank_eq : X.1.val.rank = g₁.rank := by
              rw [hX_eq_g₁ hzero, rank_single, one_smul]
            have hYX_rank : Y.1.val.rank = X.1.val.rank := by
              simp only [Y.2, X.2]
            have hY_maxrank : Y.1.val.maxRank = X.1.val.maxRank := by
              have hX_maxrank : X.1.val.maxRank = g₁.rank := by
                rw [hX_eq_g₁ hzero, ← Gene.ofRank_eq_gene, maxRank_ofRank]
              rw [hX_maxrank]
              apply Nat.le_antisymm
              · -- Upper: Y.maxRank ≤ Y.rank = X.rank = g₁.rank
                calc Y.1.val.maxRank
                    ≤ Y.1.val.rank := maxRank_le_rank _
                  _ = X.1.val.rank := hYX_rank
                  _ = g₁.rank      := hX_rank_eq
              · -- Lower: if Y.maxRank < g₁.rank then prime^[g₁.rank-1] Y = 0,
                --   but X ≤ Y forces sigma(X, g₁.rank-1) ≤ 0, contradicting
                --   prime^[g₁.rank-1] X = ofRank 1 g₁.type ≠ 0
                by_contra hlt
                push Not at hlt
                have hY_zero : prime^[g₁.rank - 1] Y.1.val = 0 :=
                  prime_iterate_zero_of_maxRank_le (by omega)
                have hX_ne : prime^[g₁.rank - 1] X.1.val ≠ 0 := by
                  rw [hX_eq_g₁ hzero, ← Gene.ofRank_eq_gene, prime_iterate_ofRank,
                      show g₁.rank - (g₁.rank - 1) = 1 from by omega]
                  simp [Gene.ofRank_is_gene]
                have hle := (le_iff_dominates.mp hXY.le) (g₁.rank - 1)
                simp only [hY_zero, map_zero] at hle
                obtain ⟨n, hn⟩ := Sigma.sigma_isNat X.1.val (g₁.rank - 1) X.1.2
                have hzero_sig : signature (prime^[g₁.rank - 1] X.1.val) = 0 := by
                  simp only [Sigma.sigma] at hn
                  rw [hn] at hle ⊢
                  obtain ⟨h1, h2⟩ := Prod.le_def.mp hle
                  simp at h1 h2
                  have : ((0, 0) : ℚ × ℚ) = 0 := rfl
                  simp [h1, h2]
                exact hX_ne (signature_eq_zero hzero_sig)
            -- Re-establish X.maxRank = g₁.rank (local to hY_maxrank's proof, so re-derive)
            have hX_maxrank : X.1.val.maxRank = g₁.rank := by
              rw [hX_eq_g₁ hzero, ← Gene.ofRank_eq_gene, maxRank_ofRank]
            -- Y.maxRank = g₁.rank
            have hY_maxrank_val : Y.1.val.maxRank = g₁.rank := hY_maxrank.trans hX_maxrank
            -- Y.rank = Y.maxRank (both equal g₁.rank)
            have hY_rank_maxrank : Y.1.val.rank = Y.1.val.maxRank :=
              (hYX_rank.trans hX_rank_eq).trans hY_maxrank_val.symm
            -- Y = single g₂ 1 for some g₂ with g₂.rank = g₁.rank
            obtain ⟨g₂, hg₂_maxrank, hY_eq⟩ := rank_eq_maxRank_single hY_rank_maxrank
              (by rw [hY_maxrank_val]; linarith)
            have hg₂_rank : g₂.rank = g₁.rank := hg₂_maxrank.trans hY_maxrank_val
            -- g₁ and g₂ are polarized (both chromosomes are in Pi)
            have hg₁_pol : g₁.type ≠ .NonPolarized :=
              IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
            have hg₂_in_supp : g₂ ∈ Y.1.val.support := by rw [hY_eq]; simp
            have hg₂_pol : g₂.type ≠ .NonPolarized :=
              IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2) g₂ hg₂_in_supp
            rcases eq_or_ne g₁ g₂ with rfl | hne
            · -- g₁ = g₂ ⟹ X.1.val = Y.1.val ⟹ X.1 = Y.1, contradicting X.1 < Y.1
              exact absurd
                (Subtype.val_injective ((hX_eq_g₁ hzero).trans hY_eq.symm))
                (ne_of_lt hXY)
            · -- g₁ ≠ g₂ but g₁.rank = g₂.rank ⟹ g₁.type ≠ g₂.type
              have htype_ne : g₁.type ≠ g₂.type := fun heq =>
                hne (Gene.ext hg₂_rank.symm heq)
              -- sigma inequality at k = g₁.rank - 1
              have hle : signature (prime^[g₁.rank - 1] X.1.val) ≤
                         signature (prime^[g₁.rank - 1] Y.1.val) :=
                (le_iff_dominates.mp hXY.le) (g₁.rank - 1)
              rw [hX_eq_g₁ hzero, ← Gene.ofRank_eq_gene, prime_iterate_ofRank,
                  show g₁.rank - (g₁.rank - 1) = 1 from by omega] at hle
              rw [hY_eq, ← Gene.ofRank_eq_gene, prime_iterate_ofRank,
                  show g₂.rank - (g₁.rank - 1) = 1 from by rw [hg₂_rank]; omega] at hle
              -- hle : signature(ofRank 1 g₁.type) ≤ signature(ofRank 1 g₂.type)
              -- Both types are polarized and differ ⟹ one is Positive, other Negative
              -- ⟹ (1,0) ≤ (0,1) or (0,1) ≤ (1,0), both impossible
              cases ht₁ : g₁.type with
              | NonPolarized => exact hg₁_pol ht₁
              | Positive =>
                cases ht₂ : g₂.type with
                | NonPolarized => exact hg₂_pol ht₂
                | Positive => exact htype_ne (ht₁.trans ht₂.symm)
                | Negative =>
                  simp only [ht₁, ht₂, signature_ofRank_one_positive,
                    signature_ofRank_one_negative] at hle
                  linarith [(Prod.le_def.mp hle).1]
              | Negative =>
                cases ht₂ : g₂.type with
                | NonPolarized => exact hg₂_pol ht₂
                | Positive =>
                  simp only [ht₁, ht₂, signature_ofRank_one_positive,
                    signature_ofRank_one_negative] at hle
                  linarith [(Prod.le_def.mp hle).2]
                | Negative => exact htype_ne (ht₁.trans ht₂.symm)
          have hg₂ : ∃ g₂ : Gene,
              0 < X.1.val g₂ ∧
              g₁.rank < g₂.rank ∧
              ∀ g' : Gene, 0 < X.1.val g' → g₁.rank < g'.rank → g₂.rank ≤ g'.rank := by
            -- The filter set S = { g ∈ X.1.val.support | g₁.rank < g.rank } is nonempty.
            -- Since prime^[g₁.rank] X.1.val ≠ 0, pick any g' in its support.
            -- By prime_iterate_coeff, (prime^[g₁.rank] X.1.val),
            --    g' = X.1.val ⟨g'.rank + g₁.rank, ...⟩ > 0,
            -- so ⟨g'.rank + g₁.rank, g'.type, _⟩ ∈ X.1.val.support with rank > g₁.rank.
            have hSne : (X.1.val.support.filter (fun g => g₁.rank < g.rank)).Nonempty := by
              -- Extract a gene g' from the nonempty support of prime^[g₁.rank] X.1.val
              obtain ⟨g', hg'⟩ := Finsupp.support_nonempty_iff.mpr hprime_rank_ne_zero
              -- Lift g' to a gene h of rank g'.rank + g₁.rank in X.1.val
              let h : Gene := ⟨g'.rank + g₁.rank, g'.type, Nat.le_add_right_of_le g'.rank_pos⟩
              refine ⟨h, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
              · -- h ∈ X.1.val.support: prime_iterate_coeff links (prime^[g₁.rank] X.1.val) g'
                --   = X.1.val h ≠ 0
                rw [Finsupp.mem_support_iff]
                have hne := Finsupp.mem_support_iff.mp hg'
                rwa [prime_iterate_coeff] at hne
              · -- g₁.rank < h.rank = g'.rank + g₁.rank, since g'.rank ≥ 1
                change g₁.rank < g'.rank + g₁.rank
                have := g'.rank_pos; omega
            -- Apply Finset.exists_min_image on S w.r.t. Gene.rank to get the minimal element g₂.
            obtain ⟨g₂, hg₂S, hg₂min⟩ := Finset.exists_min_image _ Gene.rank hSne
            rw [Finset.mem_filter] at hg₂S
            exact ⟨g₂, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂S.1),
              hg₂S.2,
              fun g' hg'pos hg'rank => hg₂min g'
                (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hg'pos.ne', hg'rank⟩)⟩
          obtain ⟨g₂, hg₂pos, hg₂rank, hg₂min⟩ := hg₂
          by_cases hε₂ : g₂.type = -g₁.type
          · exact exists_mutation_le_case4a X Y hXY hXpn ha hε₁ hXg₁ hXg₁pos
              hg₁min hg₁_ge2 hg₁_one hg₂pos hg₂rank hg₂min hε₂
          · -- Case 4b: g₂.type ≠ -g₁.type (same type family)
            by_cases hparity : Even (g₂.rank - g₁.rank)
            · -- (g₂.rank - g₁.rank) is even
              -- Mutation: Pi.Primitive.type2 with ε = g₁.type, m = g₁.rank, n = g₂.rank
              -- Source (Pi.X2): Gene.ofRank m ε + Gene.ofRank n ε = single g₁ 1 + single g₂ 1
              -- Target (Pi.Y2): Gene.ofRank (m-2) ε + Gene.ofRank (n+2) ε
              let ε := g₁.type
              have hε : ε ≠ .NonPolarized :=
                IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
              have hle : g₁.rank ≤ g₂.rank := le_of_lt hg₂rank
              -- g₂.type = g₁.type = ε (since g₂.type ≠ -g₁.type and g₂ is polarized)
              have hg₂_type : g₂.type = g₁.type := by
                have hpol₁ : g₁.type ≠ .NonPolarized := hε
                have hpol₂ : g₂.type ≠ .NonPolarized :=
                  IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₂
                    (Finsupp.mem_support_iff.mpr hg₂pos.ne')
                match ht₁ : g₁.type, hpol₁ with
                | .Positive, _ =>
                  cases ht₂ : g₂.type
                  · tauto
                  · rw [ht₂, ht₁] at hε₂
                  · rw [ht₂, ht₁, GeneType.neg_positive] at hε₂; tauto
                | .Negative, _ =>
                  cases ht₂ : g₂.type
                  · tauto
                  · rw [ht₂, ht₁, GeneType.neg_negative] at hε₂; tauto
                  · rw [ht₂, ht₁] at hε₂
              -- Gene.ofRank g₁.rank ε = single g₁ 1
              have hg₁_ofRank : Gene.ofRank g₁.rank ε = Finsupp.single g₁ 1 :=
                Gene.ofRank_eq_gene
              -- Gene.ofRank g₂.rank ε = single g₂ 1
              have hg₂_ofRank : Gene.ofRank g₂.rank ε = Finsupp.single g₂ 1 := by
                have h := @Gene.ofRank_eq_gene g₂; rw [hg₂_type] at h; exact h
              -- The type2 source chromosome equals single g₁ 1 + single g₂ 1
              have hsrc_val : (Pi.X2 hε hle hg₁_ge2 : Chromosome) =
                  Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
                simp only [Pi.X2_eq]; rw [hg₁_ofRank, hg₂_ofRank]
              -- src ≤ X.1.val pointwise
              have hne : g₁ ≠ g₂ := fun h => absurd hg₂rank (h ▸ lt_irrefl _)
              have hsrc_le : ∀ g : Gene,
                  (Pi.X2 hε hle hg₁_ge2 : Chromosome) g ≤ X.1.val g := by
                intro gen
                rw [hsrc_val, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                rcases eq_or_ne gen g₁ with rfl | hng₁
                · simp [Ne.symm hne, hg₁_one]
                · rcases eq_or_ne gen g₂ with rfl | hng₂
                  · simp only [Ne.symm hng₁]; exact hg₂pos
                  · simp [Ne.symm hng₁, Ne.symm hng₂]
              -- rest = X.1 − src, still in Pi
              let rest : Pi :=
                ⟨X.1.val - (Pi.X2 hε hle hg₁_ge2 : Chromosome),
                  Variety.sub_mem_Pi _ X.1.2⟩
              -- X.1 decomposes as Pi.X2 + rest
              have hdecomp : X.1 = Pi.X2 hε hle hg₁_ge2 + rest :=
                Subtype.val_injective
                  (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
              -- Z is the type2 mutation result: Pi.Y2 + rest
              let Z : Pi := Pi.Y2 hε hle hg₁_ge2 + rest
              -- Construct the Pi-step
              have hstep : Pi.Step X.1 Z :=
                hdecomp.symm ▸ Pi.Step.mk
                  (Pi.X2 hε hle hg₁_ge2)
                  (Pi.Y2 hε hle hg₁_ge2)
                  rest
                  (Pi.Primitive.type2 ε hε hle hg₁_ge2)
              refine ⟨Z, hstep, ?_⟩
              change Z.val ≤ Y.1.val
              rw [le_iff_dominates]
              intro i
              change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
              have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
                le_iff_dominates.mp hXY.le i
              have hZ_split : Sigma.sigma Z.val i =
                  Sigma.sigma (Pi.Y2 hε hle hg₁_ge2).val i +
                  Sigma.sigma rest.val i := by
                change Sigma.sigma (Pi.Y2 hε hle hg₁_ge2 + rest : Variety.Pi).val i = _
                simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
              have hX_split : Sigma.sigma X.1.val i =
                  Sigma.sigma (Pi.X2 hε hle hg₁_ge2).val i +
                  Sigma.sigma rest.val i := by
                have hval : X.1.val = (Pi.X2 hε hle hg₁_ge2).val + rest.val := by
                  have h := congrArg Subtype.val hdecomp
                  simp only [AddSubmonoid.coe_add] at h; exact h
                simp only [hval, Sigma.sigma, iterate_map_add, map_add]
              -- Key condition: the type2 sigma increment ≤ sigma(Y) - sigma(X)
              have hXY_sigma : ∀ j,
                  Sigma.sigma (Pi.Y2 hε hle hg₁_ge2).val j +
                  Sigma.sigma X.1.val j ≤
                  Sigma.sigma (Pi.X2 hε hle hg₁_ge2).val j +
                  Sigma.sigma Y.1.val j := by
                intro j
                have hXYj : Sigma.sigma X.1.val j ≤ Sigma.sigma Y.1.val j :=
                  le_iff_dominates.mp hXY.le j
                obtain ⟨hcase1, hcase2, hcase3⟩ :=
                  Sigma.sigma_type2_mn_rank ε hε hg₂rank hg₁_ge2
                by_cases hjl : j ≤ g₁.rank - 2
                · rw [← hcase1 j hjl]
                  sorry
                · by_cases hjr : g₂.rank + 2 ≤ j
                  · rw [← hcase2 j hjr]
                    sorry
                  · push Not at hjl hjr
                    sorry
              rw [hZ_split]
              have h1 := (hXY_sigma i).1
              have h2 := (hXY_sigma i).2
              rw [hX_split] at h1 h2
              simp only [Prod.fst_add, Prod.snd_add] at h1 h2
              refine ⟨?_, ?_⟩
              · simp only [Prod.fst_add]; linarith
              · simp only [Prod.snd_add]; linarith
            · -- (g₂.rank - g₁.rank) is odd
              sorry
  · -- Case B: a₁ = c₁ for all relevant k, so b₁ < d₁ (from hsigeq and dominance).
    sorry

/-! ## Main theorem -/

/--
Proposition after (15.7) [Djoković 1982, p. 29]:
Let X, Y ∈ Π(n) with X < Y.  Then there exists a Π-mutation X → Z such that Z ≤ Y.
-/
theorem exists_mutation_le (n : ℕ) (X Y : nPi n)
    (hXY : X.1 < Y.1) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  revert X Y hXY
  refine Nat.strongRecOn n ?_
  intro n ih X Y hXY
  cases n with
  | zero =>
    exfalso
    have hX0 : X.1.val = 0 := rank_zero X.2
    have hY0 : Y.1.val = 0 := rank_zero Y.2
    exact absurd (Subtype.ext (hX0.trans hY0.symm)) (ne_of_lt hXY)
  | succ n =>
    cases n with
    | zero =>
      exfalso
      have hsig_le : signature X.1.val ≤ signature Y.1.val :=
        (le_iff_dominates.mp hXY.le) 0
      have hXsum : (signature X.1.val).1 + (signature X.1.val).2 = 1 := by
        rcases rank_one_pi_sig X.1.2 X.2 with h | h <;> simp [h]
      have hYsum : (signature Y.1.val).1 + (signature Y.1.val).2 = 1 := by
        rcases rank_one_pi_sig Y.1.2 Y.2 with h | h <;> simp [h]
      have hsig_eq : signature X.1.val = signature Y.1.val := by
        obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
        exact Prod.ext (le_antisymm h1_le (by linarith [h2_le]))
                       (le_antisymm h2_le (by linarith [h1_le]))
      exact absurd (Subtype.ext (Pi_rank_one_eq_of_sig_eq X.1.2 Y.1.2 X.2 Y.2 hsig_eq))
                   (ne_of_lt hXY)
    | succ m =>
      have ha₀_eq_c₀ := sigma_zero_fst_eq X Y hXY.le
      by_cases hcommon : ∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g
      · exact exists_mutation_le_shared_gene m ih X Y hXY hcommon
      · by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
            Sigma.sigma X.1 k = Sigma.sigma Y.1 k
        · exact exists_mutation_le_disjoint_sigma_eq m ih X.1 Y hXY hcommon hsigeq
        · by_cases hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
              g.type = .Positive ∧ h.type = .Negative ∧
              0 < X.1.val g ∧ 0 < X.1.val h
          · exact exists_mutation_le_disjoint_pair X.1 Y.1 hXY hcommon hsigeq hXpn
          · exact exists_mutation_le_fifteen_ten m ih X Y hXY hcommon hsigeq hXpn
