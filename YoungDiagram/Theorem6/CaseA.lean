import YoungDiagram.Theorem6.Case1
import YoungDiagram.Theorem6.Case2
import YoungDiagram.Theorem6.Case3
import YoungDiagram.Theorem6.Case4A

open Variety hiding prime prime_def
open Chromosome

/-!
Case A of §15.10.

The remaining `sorry`s in this file are inherited from the unfinished Case 4b
subcases of the original dispatcher, not from the final Case B branch. The final
Case B branch is proved in `Theorem6.lean` by applying sign-duality to this lemma.
-/

set_option maxHeartbeats 0 in
-- Case A contains several large linear-arithmetic window checks inherited from §15.10.
lemma exists_mutation_le_fifteen_ten_caseA (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X.1 k = Sigma.sigma Y.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
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
                exact ⟨by simp only [Prod.fst_add]; linarith [hXYj.1],
                        by simp only [Prod.snd_add]; linarith [hXYj.2]⟩
              · by_cases hjr : g₂.rank + 2 ≤ j
                · rw [← hcase2 j hjr]
                  exact ⟨by simp only [Prod.fst_add]; linarith [hXYj.1],
                          by simp only [Prod.snd_add]; linarith [hXYj.2]⟩
                · -- Middle window: g₁.rank - 1 ≤ j ≤ g₂.rank + 1
                  push Not at hjl hjr
                  -- hcase3 gives the exact delta D = sigma Y2 j - sigma X2 j
                  have hjl' : g₁.rank - 1 ≤ j := by omega
                  have hjr' : j ≤ g₂.rank + 1 := by omega
                  have hdelta := hcase3 j hjl' hjr'
                  by_cases h_g1_rank_even : Even g₁.rank
                  · -- g₁.rank even → negOnePow(g₁.rank - 1) = -1 → (-1)•Negative = Positive
                    -- so hε₁ : ε ≠ Positive, and hε : ε ≠ NonPolarized, hence ε = Negative
                    have hε_neg : ε = GeneType.Negative := by
                      have hnodd : ¬Even ((g₁.rank : ℤ) - 1) := by
                        obtain ⟨k, hk⟩ := h_g1_rank_even
                        intro ⟨m, hm⟩
                        omega
                      simp only [GeneType.negOnePow_smul, if_neg hnodd,
                                 GeneType.neg_negative] at hε₁
                      match h : ε with
                      | .Positive    => exact absurd h hε₁
                      | .Negative    => rfl
                      | .NonPolarized =>
                        have : ε ≠ .NonPolarized := by assumption
                        exact absurd h this
                    have haj_lt_cj : ∀ j, g₁.rank - 1 ≤ j → j ≤ g₂.rank →
                        (Sigma.sigma X.1.val j).1 < (Sigma.sigma Y.1.val j).1 := by
                      -- Base inequalities at rank m = g₁.rank
                      have ham1_lt_cm1 :
                          (Sigma.sigma X.1.val (g₁.rank - 1)).1 <
                          (Sigma.sigma Y.1.val (g₁.rank - 1)).1 := by
                        have hc1_ci_rank1 :
                            (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 ≤
                            (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                          Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                        have hd0_di_rank1 :
                            (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 ≤
                            (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 := by
                          have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                            sigma_zero_snd_eq X Y hXY.le
                          have hbm2_le_dm2 :
                              (Sigma.sigma X.1 (g₁.rank - 2)).2 ≤
                              (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                            (le_iff_dominates.mp hXY.le (g₁.rank - 2)).2
                          linarith
                        have hb0_bi_rank1 :
                            (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
                            (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 (g₁.rank - 1)).1 := by
                          have h : (Sigma.sigma X.1 0).2 -
                              (Sigma.sigma X.1 (g₁.rank - 1 - 1)).2 =
                              (Sigma.sigma X.1 1).1 -
                              (Sigma.sigma X.1 (g₁.rank - 1)).1 :=
                            x_actual_negative_prefix_equalities
                              (fun g' _ hg'_pos =>
                                hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                              (by omega) (by omega)
                          simpa [show g₁.rank - 1 - 1 = g₁.rank - 2 from by omega] using h
                        have hstrict :
                            (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                          have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                            sigma_zero_fst_eq X Y hXY.le
                          linarith
                        have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                          sigma_zero_fst_eq X Y hXY.le
                        linarith [hc1_ci_rank1, hd0_di_rank1, hb0_bi_rank1, hstrict]
                      have ham_lt_cm :
                          (Sigma.sigma X.1.val g₁.rank).1 <
                          (Sigma.sigma Y.1.val g₁.rank).1 := by
                        have hc1_ci_rank :
                            (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 ≤
                            (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                          Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                        have hd0_di_rank :
                            (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                            (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
                          have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                            sigma_zero_snd_eq X Y hXY.le
                          have hbm1_le_dm1 :
                              (Sigma.sigma X.1 (g₁.rank - 1)).2 ≤
                              (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                            (le_iff_dominates.mp hXY.le (g₁.rank - 1)).2
                          linarith
                        have hb0_bi_rank :
                            (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 =
                            (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 g₁.rank).1 :=
                          x_actual_negative_prefix_equalities
                            (fun g' _ hg'_pos =>
                              hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                            (by omega) (le_refl g₁.rank)
                        have hstrict :
                            (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                          have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                            sigma_zero_fst_eq X Y hXY.le
                          linarith
                        have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                          sigma_zero_fst_eq X Y hXY.le
                        linarith [hc1_ci_rank, hd0_di_rank, hb0_bi_rank, hstrict]
                      have hfst_diff_le : ∀ i, g₁.rank ≤ i → i ≤ g₂.rank - 1 →
                          (Sigma.sigma Y.1.val i).1 - (Sigma.sigma Y.1.val (i + 1)).1 ≤
                          (Sigma.sigma X.1.val i).1 - (Sigma.sigma X.1.val (i + 1)).1 := by
                        intro i hi1 hi2
                        by_cases hi_even : Even i
                        · have hci_le_c0 :
                              (Sigma.sigma Y.1.val i).1 - (Sigma.sigma Y.1.val (i + 1)).1 ≤
                              (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
                            have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val i Y.1.2
                            simp only [if_pos hi_even] at h
                            exact h
                          have hc0_le_a0 :
                              (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 ≤
                              (Sigma.sigma X.1.val 0).1 - (Sigma.sigma X.1.val 1).1 - 1 := by
                            obtain ⟨nX1, hnX1⟩ := Sigma.sigma_isNat X.1.val 1 X.1.2
                            obtain ⟨nY1, hnY1⟩ := Sigma.sigma_isNat Y.1.val 1 Y.1.2
                            have ha0_eq : (Sigma.sigma X.1.val 0).1 = (Sigma.sigma Y.1.val 0).1 :=
                              sigma_zero_fst_eq X Y hXY.le
                            have hX1 : (Sigma.sigma X.1.val 1).1 = ↑nX1.1 :=
                              congr_arg Prod.fst hnX1
                            have hY1 : (Sigma.sigma Y.1.val 1).1 = ↑nY1.1 :=
                              congr_arg Prod.fst hnY1
                            have hlt1 : (nX1.1 : ℚ) + 1 ≤ nY1.1 := by
                              have h : (Sigma.sigma X.1.val 1).1 < (Sigma.sigma Y.1.val 1).1 := ha
                              rw [hX1, hY1] at h
                              exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp h)
                            rw [← ha0_eq, hX1, hY1]
                            linarith
                          have ha0_eq_am :
                              (Sigma.sigma X.1.val 0).1 - (Sigma.sigma X.1.val 1).1 - 1 =
                              (Sigma.sigma X.1.val g₁.rank).1 -
                                (Sigma.sigma X.1.val (g₁.rank + 1)).1 := by
                            have hLHS : (Sigma.sigma X.1.val 0).1 - (Sigma.sigma X.1.val 1).1 =
                                ∑ g ∈ X.1.val.support.filter (fun g =>
                                  0 < g.rank ∧
                                  g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                                (X.1.val g : ℚ) := by
                              rw [Sigma.sigma_fst_diff X.1.val 0 X.1.2,
                                  Sigma.prime_iterate_sum_pos_eq X.1.val 0 ⟨0, rfl⟩]
                            have hRHS : (Sigma.sigma X.1.val g₁.rank).1 -
                                (Sigma.sigma X.1.val (g₁.rank + 1)).1 =
                                ∑ g ∈ X.1.val.support.filter (fun g =>
                                  g₁.rank < g.rank ∧
                                  g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                                (X.1.val g : ℚ) := by
                              rw [Sigma.sigma_fst_diff X.1.val g₁.rank X.1.2,
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
                              rw [h1]; exact hε_neg
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
                                · left; exact heq
                                · right
                                  refine ⟨hsupp, ?_, htype⟩
                                  have hge := hg₁min g (Finsupp.mem_support_iff.mpr hsupp)
                                  rcases Nat.lt_or_eq_of_le hge with h | h
                                  · exact h
                                  · exfalso; apply heq
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
                              (Sigma.sigma X.1.val g₁.rank).1 -
                                (Sigma.sigma X.1.val (g₁.rank + 1)).1 =
                              (Sigma.sigma X.1.val i).1 -
                                (Sigma.sigma X.1.val (i + 1)).1 := by
                            have hLHS : (Sigma.sigma X.1.val g₁.rank).1 -
                                (Sigma.sigma X.1.val (g₁.rank + 1)).1 =
                                ∑ g ∈ X.1.val.support.filter (fun g =>
                                  g₁.rank < g.rank ∧
                                  g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                                (X.1.val g : ℚ) := by
                              rw [Sigma.sigma_fst_diff X.1.val g₁.rank X.1.2,
                                  Sigma.prime_iterate_sum_pos_eq X.1.val g₁.rank h_g1_rank_even]
                            have hRHS : (Sigma.sigma X.1.val i).1 -
                                (Sigma.sigma X.1.val (i + 1)).1 =
                                ∑ g ∈ X.1.val.support.filter (fun g =>
                                  i < g.rank ∧
                                  g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
                                (X.1.val g : ℚ) := by
                              rw [Sigma.sigma_fst_diff X.1.val i X.1.2,
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
                              (Sigma.sigma Y.1.val i).1 - (Sigma.sigma Y.1.val (i + 1)).1 ≤
                              (Sigma.sigma Y.1.val 1).1 - (Sigma.sigma Y.1.val 2).1 := by
                            have hi_pos : 1 ≤ i := by omega
                            have hi_pred_even : Even (i - 1) := by
                              simp only [Nat.even_iff] at *; omega
                            have sigma_shift : ∀ k, Sigma.sigma Y.1.val.prime k =
                                Sigma.sigma Y.1.val (k + 1) := fun k => by
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
                              (Sigma.sigma Y.1.val 1).1 - (Sigma.sigma Y.1.val 2).1 ≤
                              (Sigma.sigma Y.1.val 0).2 - (Sigma.sigma Y.1.val 1).2 :=
                            Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                          have hd0_le_b0 :
                              (Sigma.sigma Y.1.val 0).2 - (Sigma.sigma Y.1.val 1).2 ≤
                              (Sigma.sigma X.1.val 0).2 - (Sigma.sigma X.1.val 1).2 := by
                            have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                              sigma_zero_snd_eq X Y hXY.le
                            have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
                              (le_iff_dominates.mp hXY.le 1).2
                            linarith
                          have hb0_eq_ai :
                              (Sigma.sigma X.1.val 0).2 -
                                (Sigma.sigma X.1.val 1).2 =
                              (Sigma.sigma X.1.val i).1 -
                                (Sigma.sigma X.1.val (i + 1)).1 := by
                              have hLHS : (Sigma.sigma X.1.val 0).2 -
                                  (Sigma.sigma X.1.val 1).2 =
                                  ∑ g ∈ X.1.val.support.filter (fun g =>
                                    0 < g.rank ∧
                                    g.type = Sigma.altType g.rank GeneType.Negative),
                                  (X.1.val g : ℚ) := by
                                have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
                                have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
                                simp only [Function.iterate_zero, id] at h1 h2
                                exact h1.trans h2
                              have hRHS : (Sigma.sigma X.1.val i).1 -
                                  (Sigma.sigma X.1.val (i + 1)).1 =
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
                        | zero => intro _; simpa using ham_lt_cm
                        | succ k ihk =>
                          intro hjr
                          have hprev := ihk (by omega) (by omega) (by omega) (by omega)
                          have hdiff := hfst_diff_le (g₁.rank + k) (by omega) (by omega)
                          obtain ⟨nX_k, hnX_k⟩ :=
                            Sigma.sigma_isNat X.1.val (g₁.rank + k) X.1.2
                          obtain ⟨nY_k, hnY_k⟩ :=
                            Sigma.sigma_isNat Y.1.val (g₁.rank + k) Y.1.2
                          obtain ⟨nX_s, hnX_s⟩ :=
                            Sigma.sigma_isNat X.1.val (g₁.rank + k + 1) X.1.2
                          obtain ⟨nY_s, hnY_s⟩ :=
                            Sigma.sigma_isNat Y.1.val (g₁.rank + k + 1) Y.1.2
                          rw [hnX_k, hnY_k] at hprev hdiff
                          rw [hnX_s, hnY_s] at hdiff
                          have hks : g₁.rank + Nat.succ k = g₁.rank + k + 1 := by omega
                          rw [hks, hnX_s, hnY_s]
                          have h1 : (↑nX_k.1 : ℚ) + 1 ≤ ↑nY_k.1 := by
                            exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp hprev)
                          linarith
                    have hbj_lt_dj : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank + 1 →
                        (Sigma.sigma X.1.val j).2 < (Sigma.sigma Y.1.val j).2 := by
                      have hbm_lt_dm :
                          (Sigma.sigma X.1.val g₁.rank).2 <
                          (Sigma.sigma Y.1.val g₁.rank).2 := by
                          have hstrict :
                              (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                            linarith [sigma_zero_fst_eq X Y hXY.le]
                          have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
                            (le_iff_dominates.mp hXY.le 1).2
                          have hb12_eq :
                              (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 =
                              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                            have h := x_side_equalities
                              (fun g' _ hg'_pos =>
                                hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                              (show 1 < g₁.rank from hg₁_ge2)
                            simp only [show ¬Even 1 from by norm_num, ↓reduceIte] at h
                            exact h
                          have hd12_le :
                              (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 ≤
                              (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
                            have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (2 - 1) Y.1.2
                            simp only [show ¬Even (2 - 1 : ℕ) from by norm_num, if_false] at h
                            exact h
                          have hd2_gt_b2 : (Sigma.sigma X.1 2).2 < (Sigma.sigma Y.1 2).2 := by
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
                              (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 ≤
                              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                            Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                          have hb0_b2_rank1 :
                              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
                              (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 g₁.rank).2 := by
                            have h := Sigma.b0_eq_b2_negative g₁.rank hg₁_ge2 hg₁min
                              no_neg_gene_rank_g
                              (show g₁.rank - 2 ≤ g₁.rank - 1 from by omega)
                            simp only [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h
                            exact h
                          have hd0_di_rank1 :
                              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 ≤
                              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 :=
                            theorem6_snd_gap_le_of_dominates X Y hXY.le
                          have hd2_c1_rank1 :
                              (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                              (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
                            by_cases hrank2 : g₁.rank = 2
                            · simp only [hrank2, sub_self, le_refl]
                            · have h : g₁.rank - 1 ≥ 2 := by omega
                              have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
                              rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
                          have hd2_di1_rank1 :
                              (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                            hd2_c1_rank1.trans hc1_ci_rank1
                          linarith [hd2_di1_rank1, hd0_di_rank1, hb0_b2_rank1, hd2_gt_b2]
                      have hbm1_lt_dm1 : g₁.rank > 2 →
                          (Sigma.sigma X.1.val (g₁.rank - 1)).2 <
                          (Sigma.sigma Y.1.val (g₁.rank - 1)).2 := by
                          intro hgt
                          have hge4 : g₁.rank ≥ 4 := by
                            obtain ⟨k, hk⟩ := h_g1_rank_even; omega
                          have hstrict :
                              (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                            linarith [sigma_zero_fst_eq X Y hXY.le]
                          have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
                            (le_iff_dominates.mp hXY.le 1).2
                          have hb12_eq :
                              (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 =
                              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                            have h := x_side_equalities
                              (fun g' _ hg'_pos =>
                                hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                              (show 1 < g₁.rank from hg₁_ge2)
                            simp only [show ¬Even 1 from by norm_num, ↓reduceIte] at h
                            exact h
                          have hd12_le :
                              (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 ≤
                              (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
                            have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (2 - 1) Y.1.2
                            simp only [show ¬Even (2 - 1 : ℕ) from by norm_num, if_false] at h
                            exact h
                          have hd2_gt_b2 : (Sigma.sigma X.1 2).2 < (Sigma.sigma Y.1 2).2 := by
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
                              (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                              (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 2)).1 := by
                            have h := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2
                              (show g₁.rank - 2 ≥ 2 from by omega)
                            rwa [show g₁.rank - 2 + 1 = g₁.rank - 1 from by omega] at h
                          have hc1_ci_rank_m1 :
                              (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 2)).1 ≤
                              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 3)).2 := by
                            have h := Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2
                              (show g₁.rank - 2 ≥ 1 from by omega)
                            simp only [show g₁.rank - 2 - 1 = g₁.rank - 3 from by omega] at h
                            exact h
                          have hd0_di_rank_m1 :
                              (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 3)).2 ≤
                              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 3)).2 :=
                            theorem6_snd_gap_le_of_dominates X Y hXY.le
                          have hb0_b2_rank_m1 :
                              (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 3)).2 =
                              (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
                            have h := Sigma.b0_eq_b2_negative g₁.rank hg₁_ge2 hg₁min
                              no_neg_gene_rank_g
                              (show g₁.rank - 3 ≤ g₁.rank - 1 from by omega)
                            simp only [show g₁.rank - 3 + 2 = g₁.rank - 1 from by omega] at h
                            exact h
                          linarith [hd2_c1_rank_m1, hc1_ci_rank_m1,
                                    hd0_di_rank_m1, hb0_b2_rank_m1, hd2_gt_b2]
                      have hdi_sub_le_bi_sub : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank →
                            (Sigma.sigma Y.1.val j).2 - (Sigma.sigma Y.1.val (j + 1)).2 ≤
                            (Sigma.sigma X.1.val j).2 - (Sigma.sigma X.1.val (j + 1)).2 := by
                          sorry
                      intro j hj1 hj2
                      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj1
                      induction d with
                      | zero => simpa using hbm_lt_dm
                      | succ d ih =>
                        have ihd := ih (by omega) (by omega)
                        have hstep :=
                          hdi_sub_le_bi_sub (g₁.rank + d) (by omega) (by omega)
                        obtain ⟨nX_d, hnX_d⟩ :=
                          Sigma.sigma_isNat X.1.val (g₁.rank + d) X.1.2
                        obtain ⟨nY_d, hnY_d⟩ :=
                          Sigma.sigma_isNat Y.1.val (g₁.rank + d) Y.1.2
                        obtain ⟨nX_s, hnX_s⟩ :=
                          Sigma.sigma_isNat X.1.val (g₁.rank + d + 1) X.1.2
                        obtain ⟨nY_s, hnY_s⟩ :=
                          Sigma.sigma_isNat Y.1.val (g₁.rank + d + 1) Y.1.2
                        rw [hnX_d, hnY_d] at ihd hstep
                        rw [hnX_s, hnY_s] at hstep
                        have hks : g₁.rank + Nat.succ d = g₁.rank + d + 1 := by omega
                        rw [hks, hnX_s, hnY_s]
                        have h1 : (↑nX_d.2 : ℚ) + 1 ≤ ↑nY_d.2 := by
                          exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp ihd)
                        linarith
                    have hε_ne_pos : ε ≠ .Positive := hε_neg ▸ by decide
                    simp only [if_neg hε_ne_pos] at hdelta
                    -- hdelta : sigma Y2 j - sigma X2 j =
                    --   if (j > g₁.rank-1) ∧ (j < g₂.rank+1) then (1,1)
                    --   else if j = g₁.rank-1 then (1,0) else (0,1)
                    obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val j X.1.2
                    obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val j Y.1.2
                    rw [hnX, hnY] at hXYj
                    rcases (show j = g₁.rank - 1 ∨
                                 (g₁.rank ≤ j ∧ j ≤ g₂.rank) ∨
                                 j = g₂.rank + 1 from by omega)
                        with hjbd | ⟨hjl2, hjr2⟩ | hjbd2
                    · -- Left boundary: j = g₁.rank - 1, delta = (1, 0)
                      rw [if_neg (by omega : ¬((j > g₁.rank - 1) ∧ (j < g₂.rank + 1))),
                          if_pos hjbd] at hdelta
                      have haj := haj_lt_cj j (by omega) (by omega)
                      rw [hnX, hnY] at haj
                      have hd1 : (Sigma.sigma (Pi.Y2 hε hle hg₁_ge2).val j).1 -
                                 (Sigma.sigma (Pi.X2 hε hle hg₁_ge2).val j).1 = 1 :=
                        congr_arg Prod.fst hdelta
                      have hd2 : (Sigma.sigma (Pi.Y2 hε hle hg₁_ge2).val j).2 -
                                 (Sigma.sigma (Pi.X2 hε hle hg₁_ge2).val j).2 = 0 :=
                        congr_arg Prod.snd hdelta
                      have ha1 : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 :=
                        by exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp haj)
                      exact ⟨by simp only [Prod.fst_add, hnX, hnY]; linarith,
                             by simp only [Prod.snd_add, hnX, hnY]; linarith [hXYj.2]⟩
                    · -- Interior: g₁.rank ≤ j ≤ g₂.rank, delta = (1, 1)
                      rw [if_pos (show (j > g₁.rank - 1) ∧ (j < g₂.rank + 1)
                                  from ⟨by omega, by omega⟩)] at hdelta
                      have haj := haj_lt_cj j (by omega) hjr2
                      have hbj := hbj_lt_dj j hjl2 (by omega)
                      rw [hnX, hnY] at haj hbj
                      have hd1 : (Sigma.sigma (Pi.Y2 hε hle hg₁_ge2).val j).1 -
                                 (Sigma.sigma (Pi.X2 hε hle hg₁_ge2).val j).1 = 1 :=
                        congr_arg Prod.fst hdelta
                      have hd2 : (Sigma.sigma (Pi.Y2 hε hle hg₁_ge2).val j).2 -
                                 (Sigma.sigma (Pi.X2 hε hle hg₁_ge2).val j).2 = 1 :=
                        congr_arg Prod.snd hdelta
                      have ha1 : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 :=
                        by exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp haj)
                      have hb1 : (↑nX.2 : ℚ) + 1 ≤ ↑nY.2 :=
                        by exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp hbj)
                      exact ⟨by simp only [Prod.fst_add, hnX, hnY]; linarith,
                             by simp only [Prod.snd_add, hnX, hnY]; linarith⟩
                    · -- Right boundary: j = g₂.rank + 1, delta = (0, 1)
                      rw [if_neg (by omega : ¬((j > g₁.rank - 1) ∧ (j < g₂.rank + 1))),
                          if_neg (by omega : j ≠ g₁.rank - 1)] at hdelta
                      have hbj := hbj_lt_dj j (by omega) (by omega)
                      rw [hnX, hnY] at hbj
                      have hd1 : (Sigma.sigma (Pi.Y2 hε hle hg₁_ge2).val j).1 -
                                 (Sigma.sigma (Pi.X2 hε hle hg₁_ge2).val j).1 = 0 :=
                        congr_arg Prod.fst hdelta
                      have hd2 : (Sigma.sigma (Pi.Y2 hε hle hg₁_ge2).val j).2 -
                                 (Sigma.sigma (Pi.X2 hε hle hg₁_ge2).val j).2 = 1 :=
                        congr_arg Prod.snd hdelta
                      have hb1 : (↑nX.2 : ℚ) + 1 ≤ ↑nY.2 :=
                        by exact_mod_cast Nat.succ_le_iff.mpr (Nat.cast_lt.mp hbj)
                      exact ⟨by simp only [Prod.fst_add, hnX, hnY]; linarith [hXYj.1],
                             by simp only [Prod.snd_add, hnX, hnY]; linarith⟩
                  · -- g1.rank odd
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
