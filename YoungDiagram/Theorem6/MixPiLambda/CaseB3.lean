import YoungDiagram.Theorem6.MixPiLambda.CaseB3Prop

/-!
# §16 Case 3 for `Mix (Pi, Lambda)` (label 2): `g₁ = g⁺(m)`, `m = 2m'+2 ≥ 4`.

Mirror of `MixLambdaPi/CaseB3.lean` with parity flipped.  The `g₂ = g(k)` (type6) and
`g₂ = g⁻(k)` (type7) sub-cases reuse the `g₃`-style assemblies
(`branchA_g3_assembly_type{6,7}`) with lower positive gene `g₁ = g⁺(2m'+2)` (`n' = m'`) and
the `a`-propagation `branchB_case4_aprop_gen`.  The `g₂ = g⁺(k)` and `2g₁` (type8) sub-cases
need the deep-interior `(1,1)` absorption machinery (still to be ported).
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- **§16 Case 3** (`m ≥ 4`, `g₁ = g⁺(2m'+2)`, `m' ≥ 1`).  Dispatch on `2g₁` vs the second
gene `g₂`'s charge. -/
lemma branchB_case3 (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pos : g₁.type = .Positive)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 2) (hmpos : 0 < m') :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hmin2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank := fun g hg => by have := hg₁min g hg; omega
  have hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 := by
    have hb1 : (Sigma.sigma X.1.1 1).2 ≤ (Sigma.sigma Y.1.1 1).2 := (le_iff_dominates.mp hXY.le 1).2
    linarith [ha, hb1]
  by_cases hmult : 2 ≤ X.1.1 g₁
  · -- `X ⊇ 2g₁`: type8 diagonal `2g⁺(m) → g⁺(m-2) + g⁺(m+2)`.
    have hmin' : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank := fun g hg => hm' ▸ hg₁min g hg
    have hk1 : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → 2 * m' + 3 ≤ g.rank := by
      intro g hg hgnp
      have hge := hmin' g hg
      rcases Nat.lt_or_ge g.rank (2 * m' + 3) with hlt | hge2
      · exfalso
        have hgr : g.rank = 2 * m' + 2 := by omega
        have hgpos2 : 0 < X.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
        have hgneg : g.type = .Negative := by
          cases hgt : g.type with
          | Positive => exact absurd hgt hgnp
          | Negative => rfl
          | NonPolarized =>
            exfalso
            have hodd := rank_odd_of_nonpolarized_mem X.1.2 hgt hgpos2
            rw [hgr] at hodd; exact (Nat.not_odd_iff_even.mpr ⟨m' + 1, by ring⟩) hodd
        exact hXpn ⟨g₁, g, by rw [hgr, hm'], hg₁pos, hgneg, hXg₁, hgpos2⟩
      · exact hge2
    have hpropa := branchB_case4_aprop_gen X Y hXY ha hmin2 (branchB_hpar X) (2 * m' + 3) hk1
    have hbanchor := branchB_case3_banchor_pl X Y hXY hgap m' hmpos hmin'
    have htail2 : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * m' + 2 ≤ g.rank := by
      intro g hg
      have hgpos : 0 < X.1.1 g := lt_of_lt_of_le
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg))
        (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
      exact hmin' g (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgpos))
    have hhal := branchB_case3_halive X Y hXY hgap g₁ (by omega) (2 * m' + 2) htail2
    refine branchB_case3_assembly_type8_double X Y hXY m' g₁ hm' hg₁pos hmult hbanchor ?_ ?_
    · intro j hjo hj1 hj2
      exact hpropa j (by omega) hj2 hjo
    · intro j hje hj1 hj2
      have hjeq : j = 2 * m' + 2 := by omega
      subst hjeq
      have hjm1 : 2 * m' + 2 - 1 = 2 * m' + 1 := by omega
      have ha_n : (Sigma.sigma X.1.1 (2 * m' + 2 - 1)).1 + 1 ≤
          (Sigma.sigma Y.1.1 (2 * m' + 2 - 1)).1 := by
        rw [hjm1]; exact hpropa (2 * m' + 1) (by omega) (by omega) ⟨m', by ring⟩
      have hb_n : (Sigma.sigma X.1.1 (2 * m' + 2 - 1)).2 + 1 ≤
          (Sigma.sigma Y.1.1 (2 * m' + 2 - 1)).2 := by rw [hjm1]; exact hbanchor
      have hal_n := hhal (2 * m' + 1) (by omega)
      rw [show (2 * m' + 1 : ℕ) = 2 * m' + 2 - 1 from by omega] at hal_n
      exact even_interior_absorb_neighbor X.1.2 Y.1.2 hje ha_n hb_n hal_n
  · -- second gene `g₂` of minimal rank in `X - g₁`
    obtain ⟨g0, hg0mem, hg0np⟩ := branchB_case4_exists X Y hXY ha hmin2
    have hg0ne : g0 ≠ g₁ := fun h => hg0np (h ▸ hg₁pos)
    obtain ⟨g₂, hg₂mem, hg₂minS⟩ := Finset.exists_min_image
      (X.1.1.support.filter (fun g => g ≠ g₁)) Gene.rank
      ⟨g0, Finset.mem_filter.mpr ⟨hg0mem, hg0ne⟩⟩
    rw [Finset.mem_filter] at hg₂mem
    obtain ⟨hg₂supp, hg₂ne⟩ := hg₂mem
    have hXg₂' : 0 < X.1.1 g₂ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂supp)
    have hk2 : ∀ g ∈ X.1.1.support, g ≠ g₁ → g₂.rank ≤ g.rank :=
      fun g hg hgne => hg₂minS g (Finset.mem_filter.mpr ⟨hg, hgne⟩)
    have hkprop : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → g₂.rank ≤ g.rank :=
      fun g hg hgnp => hk2 g hg (fun he => hgnp (he ▸ hg₁pos))
    have hne : g₁ ≠ g₂ := fun h => hg₂ne h.symm
    have hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]; exact hXg₂'
    have hprop := branchB_case4_aprop_gen X Y hXY ha hmin2 (branchB_hpar X) g₂.rank hkprop
    have hge : 2 * m' + 2 ≤ g₂.rank := hm' ▸ hg₁min g₂ hg₂supp
    cases hch : g₂.type with
    | NonPolarized =>
      have hodd : Odd g₂.rank := rank_odd_of_nonpolarized_mem X.1.2 hch hXg₂'
      obtain ⟨nn, hnn⟩ : ∃ nn, g₂.rank = 2 * nn + 3 := by
        rcases hodd with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
      have hmn : m' ≤ nn := by omega
      have hYwin : ∀ j, 2 * m' + 1 ≤ j → j < 2 * nn + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0 :=
        fun j _ hj => Ywin_below_pl X Y hXY g₂ hXg₂' (by rw [hnn]; omega)
      exact branchA_g3_assembly_type6 X Y hXY hsigeq m' nn hmn g₁ g₂
        hm' hg₁pos hnn hch hXg₁ hXg₂ hne
        (fun j hj1 hj2 hoj => hprop j (by omega) (by rw [hnn]; exact hj2) hoj) hYwin
    | Negative =>
      have hev : Even g₂.rank := rank_even_of_polarized X.1.2 (by rw [hch]; decide) hXg₂'
      obtain ⟨nn, hnn⟩ : ∃ nn, g₂.rank = 2 * nn + 2 := by
        rcases hev with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
      have hmn : m' ≤ nn := by omega
      have hYwin : ∀ j, 2 * m' + 1 ≤ j → j ≤ 2 * nn + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0 := by
        intro j _ hj
        rcases lt_or_eq_of_le hj with hlt | heq
        · exact Ywin_below_pl X Y hXY g₂ hXg₂' (by rw [hnn]; omega)
        · subst heq
          exact branchA_g3_Ynonzero_top X Y hXY hcommon nn g₂ hnn hch hXg₂'
      exact branchA_g3_assembly_type7 X Y hXY hsigeq m' nn hmn g₁ g₂
        hm' hg₁pos hnn hch hXg₁ hXg₂ hne
        (fun j hj1 hj2 hoj => hprop j (by omega) (by rw [hnn]; omega) hoj) hYwin
    | Positive =>
      -- `g₂ = g⁺(k)`: type8 `g⁺(m) + g⁺(k) → g⁺(m-2) + g⁺(k+2)`.
      have hmin' : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank := fun g hg => hm' ▸ hg₁min g hg
      have hg₁mult1 : X.1.1 g₁ = 1 := by
        have h1 : 1 ≤ X.1.1 g₁ := hXg₁
        have h2 : ¬ 2 ≤ X.1.1 g₁ := hmult
        omega
      have hev : Even g₂.rank := rank_even_of_polarized X.1.2 (by rw [hch]; decide) hXg₂'
      have hgt : 2 * m' + 4 ≤ g₂.rank := by
        rcases Nat.lt_or_ge g₂.rank (2 * m' + 4) with hlt | hge2
        · exfalso
          have hgr : g₂.rank = 2 * m' + 2 := by
            rcases hev with ⟨t, ht⟩; omega
          exact hne (Gene.ext (by rw [hm', hgr]) (by rw [hg₁pos, hch]))
        · exact hge2
      obtain ⟨q, hq⟩ : ∃ q, g₂.rank = 2 * q + 2 := by
        rcases hev with ⟨t, ht⟩
        exact ⟨t - 1, by omega⟩
      have hmq : m' < q := by omega
      have hk1 : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → 2 * q + 3 ≤ g.rank := by
        intro g hg hgnp
        have hge2 := hkprop g hg hgnp; rw [hq] at hge2
        rcases Nat.lt_or_ge g.rank (2 * q + 3) with hlt | hge3
        · exfalso
          have hgr : g.rank = 2 * q + 2 := by omega
          have hgpos2 : 0 < X.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
          have hgneg : g.type = .Negative := by
            cases hgt2 : g.type with
            | Positive => exact absurd hgt2 hgnp
            | Negative => rfl
            | NonPolarized =>
              exfalso
              have hodd := rank_odd_of_nonpolarized_mem X.1.2 hgt2 hgpos2
              rw [hgr] at hodd; exact (Nat.not_odd_iff_even.mpr ⟨q + 1, by ring⟩) hodd
          exact hXpn ⟨g₂, g, by rw [hgr, hq], hch, hgneg, hXg₂', hgpos2⟩
        · exact hge3
      have hpropa := branchB_case4_aprop_gen X Y hXY ha hmin2 (branchB_hpar X) (2 * q + 3) hk1
      have hbanchor := branchB_case3_banchor_pl X Y hXY hgap m' hmpos hmin'
      have htail : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * q + 2 ≤ g.rank := by
        intro g hg
        have hgne : g ≠ g₁ := by
          rintro rfl
          rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl,
            hg₁mult1] at hg
          simp at hg
        have hgX : g ∈ X.1.1.support := by
          rw [Finsupp.mem_support_iff] at hg ⊢
          rwa [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hgne), Nat.sub_zero] at hg
        have := hk2 g hgX hgne; rwa [hq] at this
      have hdeep := branchB_case3_deep_bprop X Y hXY hgap m' g₁
        hg₁mult1.ge (2 * q + 2) htail hbanchor
      have hhal := branchB_case3_halive X Y hXY hgap g₁ (by omega) (2 * q + 2) htail
      refine branchB_case3_assembly_type8 X Y hXY m' q (by omega) g₁ g₂
        hm' hg₁pos hq hch hXg₁ hXg₂ hne hbanchor ?_ ?_ ?_
      · -- haodd: odd j ∈ [2m'+3, 2q+3]
        intro j hjo hj1 hj2; exact hpropa j (by omega) hj2 hjo
      · -- hbodd: odd j ∈ [2m'+3, 2q+1]
        intro j hjo hj1 hj2
        obtain ⟨t, ht⟩ : ∃ t, j = 2 * m' + 1 + 2 * t := by
          obtain ⟨r, hr⟩ := hjo; exact ⟨r - m', by omega⟩
        rw [ht]; exact hdeep t (by omega)
      · -- hevenabsorb: even j ∈ [2m'+2, 2q+2]
        intro j hje hj1 hj2
        obtain ⟨s, hs⟩ : ∃ s, j = 2 * m' + 2 + 2 * s := by
          obtain ⟨r, hr⟩ := hje; exact ⟨r - m' - 1, by omega⟩
        have hjm1 : j - 1 = 2 * m' + 1 + 2 * s := by omega
        have ha_n : (Sigma.sigma X.1.1 (j - 1)).1 + 1 ≤ (Sigma.sigma Y.1.1 (j - 1)).1 := by
          rw [hjm1]; exact hpropa (2 * m' + 1 + 2 * s) (by omega) (by omega) ⟨m' + s, by ring⟩
        have hb_n : (Sigma.sigma X.1.1 (j - 1)).2 + 1 ≤ (Sigma.sigma Y.1.1 (j - 1)).2 := by
          rw [hjm1]; exact hdeep s (by omega)
        have hal_n := hhal (j - 1) (by omega)
        rw [show j - 1 + 1 = j from by omega] at hal_n
        exact even_interior_absorb_neighbor X.1.2 Y.1.2 hje ha_n hb_n hal_n

/-- §16 Branch B, positive charge (`g₁ = g⁺(m)`, `m = 2m'+2` even).  Dispatch on `m = 2`
(`m' = 0`, Case 4) vs `m ≥ 4` (`m' ≥ 1`, Case 3). -/
lemma branchB_pos (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pos : g₁.type = .Positive) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨m', hm'⟩ : ∃ m', g₁.rank = 2 * m' + 2 := by
    have hev := rank_even_of_polarized X.1.2 (by rw [hg₁pos]; decide) hXg₁
    have hpos := g₁.rank_pos
    rcases hev with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m' with hm0 | hmpos
  · exact branchB_case4 m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hg₁pos m' hm' hm0
  · exact branchB_case3 m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hg₁pos m' hm' hmpos

-- `branchB_neg` and the Branch B dispatcher live in `CaseB4` (they need the b-deficient
-- dispatch `branchB_pos_bdef` for the `b₁ = d₁` edge case).

end MixPiLambda
