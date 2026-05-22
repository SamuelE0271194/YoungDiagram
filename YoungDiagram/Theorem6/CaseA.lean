import YoungDiagram.Theorem6.Case1
import YoungDiagram.Theorem6.Case2
import YoungDiagram.Theorem6.Case3
import YoungDiagram.Theorem6.Case4A
import YoungDiagram.Theorem6.Case4B

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
    (_ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2))
    (hXY : X.1 < Y.1)
    (_hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (_hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
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
        · exact exists_mutation_le_case4b X Y hXY hXpn ha hε₁ hXg₁ hXg₁pos
            hg₁min hg₁_ge2 hg₁_one hg₂pos hg₂rank hg₂min hε₂
