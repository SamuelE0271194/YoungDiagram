import YoungDiagram.Theorem6.MixPiLambda.CaseB3

/-!
# §16 Branch B for `Mix (Pi, Lambda)`, b-deficient (Case A `b`-version).

The `branchB_neg` edge case (`g₁ = g⁻`, `a₁ < c₁`, `b₁ = d₁`) sign-duals to a `g⁺`,
`b`-deficient problem.  Here we close that problem: the minimal gene is `g⁺`, the level-1
gap is on the `b`-component (`b₁ < d₁`, supplied as `hbd`), and `a` is balanced at level 1.
All `a`-propagation comes from the self-dual total gap (`branchB_a_anchor_totalgap`,
`branchB_case4_aprop_totalgap`); the bottom even level `j = 2` of the type8 cases is absorbed
by `even2_absorb_totalgap` (the odd neighbour `j = 1` is `a`-balanced).
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- Integrality bump of the level-1 `b`-deficiency. -/
private lemma bd_anchor {N : ℕ} (X Y : nMixPiLambda N)
    (hbd : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2) :
    (Sigma.sigma X.1.1 1).2 + 1 ≤ (Sigma.sigma Y.1.1 1).2 := by
  obtain ⟨zX, hzX⟩ := sig_snd_isInt_odd X.1.2 (by decide : Odd 1)
  obtain ⟨zY, hzY⟩ := sig_snd_isInt_odd Y.1.2 (by decide : Odd 1)
  rw [hzX, hzY] at hbd ⊢
  have hz : zX < zY := by exact_mod_cast hbd
  have : (zX : ℚ) + 1 ≤ zY := by exact_mod_cast (by omega : zX + 1 ≤ zY)
  linarith

/-- **Total-gap `a`-propagation, positive-gene-aware** (`Mix (Pi, Lambda)`).  Proves
`a_X(j) + 1 ≤ a_Y(j)` for every `j ∈ [2, k]` (both parities) by mutual induction:
the even level `2` is the base (`even2_absorb_totalgap`); an odd level inherits the gap
`≥ 1` from the even level below via the per-level identity (`xdrop_eq_pl`, which tolerates
positive genes below the window); an even level inherits from the odd level below via
`even_interior_absorb_neighbor` (using the supplied odd `b`-gaps `hbodd` and alive-count
`hhal`).  This is the b-deficient counterpart of `branchB_case4_aprop_gen` (anchored at the
total gap rather than `a₁ < c₁`). -/
lemma branchB_aprop_bdef {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (hmin2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank)
    (hpar : ∀ g ∈ X.1.1.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank))
    (k : ℕ) (hk : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → k ≤ g.rank)
    (hbodd : ∀ j, Odd j → 1 ≤ j → j < k →
      (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2)
    (hhal : ∀ i, Odd i → 1 ≤ i → i + 1 ≤ k →
      (Sigma.sigma Y.1.1 i).1 + (Sigma.sigma Y.1.1 i).2 -
          ((Sigma.sigma Y.1.1 (i + 1)).1 + (Sigma.sigma Y.1.1 (i + 1)).2) ≤
      (Sigma.sigma X.1.1 i).1 + (Sigma.sigma X.1.1 i).2 -
          ((Sigma.sigma X.1.1 (i + 1)).1 + (Sigma.sigma X.1.1 (i + 1)).2)) :
    ∀ j, 2 ≤ j → j ≤ k → (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 := by
  have ha0 : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 := by
    have hXr : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
      simpa [Sigma.sigma, X.2] using this
    have hYr : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
      simpa [Sigma.sigma, Y.2] using this
    have h1 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 := (le_iff_dominates.mp hXY.le 0).1
    have h2 : (Sigma.sigma X.1.1 0).2 ≤ (Sigma.sigma Y.1.1 0).2 := (le_iff_dominates.mp hXY.le 0).2
    linarith
  have hdom1 : (Sigma.sigma X.1.1 1).1 ≤ (Sigma.sigma Y.1.1 1).1 := (le_iff_dominates.mp hXY.le 1).1
  have hgap0 : (Sigma.sigma X.1.1 0).1 - (Sigma.sigma X.1.1 1).1 -
      ((Sigma.sigma X.1.1 1).2 - (Sigma.sigma X.1.1 2).2) = 0 := xgap_zero_pl hmin2 hpar
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj2 hjk
    rcases Nat.lt_or_ge j 3 with hjlt | hjge
    · have hjeq : j = 2 := by omega
      subst hjeq
      have h := (even2_absorb_totalgap X Y hXY hgap hmin2).1
      simp only [Prod.fst_add] at h; linarith
    · rcases Nat.even_or_odd j with hje | hjo
      · -- even `j`: `even_interior` from the odd level `j - 1`
        have hjm1odd : Odd (j - 1) := by rcases hje with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
        have hPa : (Sigma.sigma X.1.1 (j - 1)).1 + 1 ≤ (Sigma.sigma Y.1.1 (j - 1)).1 :=
          ih (j - 1) (by omega) (by omega) (by omega)
        have hPb : (Sigma.sigma X.1.1 (j - 1)).2 + 1 ≤ (Sigma.sigma Y.1.1 (j - 1)).2 :=
          hbodd (j - 1) hjm1odd (by omega) (by omega)
        have hali := hhal (j - 1) hjm1odd (by omega) (by omega)
        rw [show j - 1 + 1 = j from by omega] at hali
        have h := (even_interior_absorb_neighbor X.1.2 Y.1.2 hje hPa hPb hali).1
        simp only [Prod.fst_add] at h; linarith
      · -- odd `j`: per-level from the even level `j - 1`
        have hjm1even : Even (j - 1) := by rcases hjo with ⟨t, ht⟩; exact ⟨t, by omega⟩
        have hPa : (Sigma.sigma X.1.1 (j - 1)).1 + 1 ≤ (Sigma.sigma Y.1.1 (j - 1)).1 :=
          ih (j - 1) (by omega) (by omega) (by omega)
        obtain ⟨t, ht⟩ : ∃ t, j - 1 = 2 * t := ⟨(j - 1) / 2, by
          obtain ⟨r, hr⟩ := hjm1even; omega⟩
        have hsurv : ∀ g ∈ X.1.1.support, g.type ≠ .Positive →
            (g.rank ≤ 1 ∨ (j - 1) + 1 ≤ g.rank) :=
          fun g hg hgnp => Or.inr (by have := hk g hg hgnp; omega)
        have hxd : (Sigma.sigma X.1.1 (j - 1)).1 - (Sigma.sigma X.1.1 j).1 =
            (Sigma.sigma X.1.1 1).2 - (Sigma.sigma X.1.1 2).2 := by
          have h := xdrop_eq_pl (X := X.1.1) (i := j - 1) hjm1even (by omega) hpar hsurv
          rwa [show j - 1 + 1 = j from by omega] at h
        have hYanti : (Sigma.sigma Y.1.1 (j - 1)).1 - (Sigma.sigma Y.1.1 j).1 ≤
            (Sigma.sigma Y.1.1 0).1 - (Sigma.sigma Y.1.1 1).1 := by
          have h := adrop_even_le Y.1.2 t
          rwa [← ht, show j - 1 + 1 = j from by omega] at h
        linarith [hPa, hxd, hYanti, hgap0, ha0, hdom1]

/-- **§16 Case 4, b-deficient** (`m = 2`, `g₁ = g⁺(2)`, `b₁ < d₁`, `a₁ = c₁`). -/
lemma branchB_case4_bdef (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (hbd : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pos : g₁.type = .Positive) (hg₁rank : g₁.rank = 2) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hmin2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank := fun g hg => hg₁rank ▸ hg₁min g hg
  -- every rank-2 gene is positive (a negative one would clash with `g₁ = g⁺(2)` via hXpn)
  have hX2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Positive) := by
    intro g hg
    refine ⟨hmin2 g hg, fun hgr => ?_⟩
    have hgpos : 0 < X.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
    cases hgt : g.type with
    | Positive => rfl
    | Negative => exact absurd ⟨g₁, g, by rw [hg₁rank, hgr], hg₁pos, hgt, hXg₁, hgpos⟩ hXpn
    | NonPolarized =>
      exfalso
      have hodd := rank_odd_of_nonpolarized_mem X.1.2 hgt hgpos
      rw [hgr] at hodd; exact (Nat.not_odd_iff_even.mpr ⟨1, by ring⟩) hodd
  have hbanchor1 : (Sigma.sigma X.1.1 1).2 + 1 ≤ (Sigma.sigma Y.1.1 1).2 := bd_anchor X Y hbd
  by_cases hmult : 2 ≤ X.1.1 g₁
  · -- `2 g⁺(2) → g⁺(4)` (type8 double, `p = 0`)
    have hpropa : ∀ j, Odd j → 2 * 0 + 3 ≤ j → j ≤ 2 * 0 + 3 →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 := by
      intro j _ hj1 hj2
      have hjeq : j = 3 := by omega
      rw [hjeq]; exact branchB_case4_a3_anchor X Y hXY hgap hX2
    refine branchB_case3_assembly_type8_double X Y hXY 0 g₁ (by rw [hg₁rank]) hg₁pos hmult
      (by simpa using hbanchor1) hpropa ?_
    intro j _ hj1 hj2
    have hjeq : j = 2 := by omega
    rw [hjeq]; exact even2_absorb_totalgap X Y hXY hgap hmin2
  · -- minimal gene `g₂` of `X - g₁`
    have hg₁mult1 : X.1.1 g₁ = 1 := by
      have h1 : 1 ≤ X.1.1 g₁ := hXg₁; omega
    obtain ⟨g0, hg0mem, hg0ne⟩ : ∃ g ∈ X.1.1.support, g ≠ g₁ := by
      by_contra hcon
      push Not at hcon
      -- then `X = g₁` (mult 1), so `|X| = 1`, but `|Y| < |X|` and `|Y| ≥ 1`
      have hX1 : X.1.1.sum (fun _ m => (m : ℚ)) = 1 := by
        rw [Finsupp.sum, Finset.sum_eq_single g₁]
        · exact_mod_cast hg₁mult1
        · exact fun g hg hgne => absurd (hcon g hg) hgne
        · intro hni
          exact absurd (Finsupp.mem_support_iff.mpr (by rw [hg₁mult1]; norm_num)) hni
      have hYpos : 1 ≤ Y.1.1.sum (fun _ m => (m : ℚ)) := by
        have hYne : Y.1.1 ≠ 0 := by
          intro h0; have := Y.2; rw [h0] at this; simp at this
        obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hYne
        calc (1 : ℚ) ≤ (Y.1.1 g : ℚ) := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hg)
          _ ≤ Y.1.1.sum (fun _ m => (m : ℚ)) := by
              rw [Finsupp.sum]
              exact Finset.single_le_sum (f := fun a => ((Y.1.1 a : ℕ) : ℚ))
                (fun i _ => by positivity) hg
      have hXcellsdef : X.1.1.sum (fun _ m => (m : ℚ)) =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
        have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
          have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
          simpa [Sigma.sigma] using this
        have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
            ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
        rw [h0, h1, Function.iterate_one]; exact cells.symm
      have hYcellsdef : Y.1.1.sum (fun _ m => (m : ℚ)) =
          (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
            ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) := by
        have h0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
          have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
          simpa [Sigma.sigma] using this
        have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
            ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
        rw [h0, h1, Function.iterate_one]; exact cells.symm
      have hr0X : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (m + 2 : ℕ) := by
        have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
        simpa [Sigma.sigma, X.2] using this
      have hr0Y : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (m + 2 : ℕ) := by
        have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
        simpa [Sigma.sigma, Y.2] using this
      rw [hXcellsdef] at hX1; rw [hYcellsdef] at hYpos
      push_cast at hr0X hr0Y
      linarith [hgap, hX1, hYpos, hr0X, hr0Y]
    obtain ⟨g₂, hg₂mem, hg₂minS⟩ := Finset.exists_min_image
      (X.1.1.support.filter (fun g => g ≠ g₁)) Gene.rank
      ⟨g0, Finset.mem_filter.mpr ⟨hg0mem, hg0ne⟩⟩
    rw [Finset.mem_filter] at hg₂mem
    obtain ⟨hg₂supp, hg₂ne⟩ := hg₂mem
    have hXg₂' : 0 < X.1.1 g₂ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂supp)
    have hk2 : ∀ g ∈ X.1.1.support, g ≠ g₁ → g₂.rank ≤ g.rank :=
      fun g hg hgne => hg₂minS g (Finset.mem_filter.mpr ⟨hg, hgne⟩)
    have hne : g₁ ≠ g₂ := fun h => hg₂ne h.symm
    have hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]; exact hXg₂'
    have htailk : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, g₂.rank ≤ g.rank := by
      intro g hg
      have hgne : g ≠ g₁ := by
        rintro rfl
        rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl,
          hg₁mult1] at hg
        simp at hg
      have hgX : g ∈ X.1.1.support := by
        rw [Finsupp.mem_support_iff] at hg ⊢
        rwa [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hgne), Nat.sub_zero] at hg
      exact hk2 g hgX hgne
    have hg₂ge2 : 2 ≤ g₂.rank := hmin2 g₂ hg₂supp
    have hprop := branchB_case4_aprop_totalgap X Y hXY hgap g₁ hg₁mult1 hX2 g₂.rank htailk
    cases hch : g₂.type with
    | NonPolarized =>
      have hodd : Odd g₂.rank := rank_odd_of_nonpolarized_mem X.1.2 hch hXg₂'
      obtain ⟨nn, hnn⟩ : ∃ nn, g₂.rank = 2 * nn + 3 := by
        rcases hodd with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
      have hYwin : ∀ j, 2 * 0 + 1 ≤ j → j < 2 * nn + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0 :=
        fun j _ hj => Ywin_below_pl X Y hXY g₂ hXg₂' (by rw [hnn]; omega)
      exact branchA_g3_assembly_type6 X Y hXY hsigeq 0 nn (Nat.zero_le _) g₁ g₂
        (by rw [hg₁rank]) hg₁pos hnn hch hXg₁ hXg₂ hne
        (fun j hj1 hj2 hoj => hprop j hj1 (by rw [hnn]; exact hj2) hoj) hYwin
    | Negative =>
      have hev : Even g₂.rank := rank_even_of_polarized X.1.2 (by rw [hch]; decide) hXg₂'
      have hg₂gt2 : 3 ≤ g₂.rank := by
        rcases Nat.lt_or_ge g₂.rank 3 with hlt | hge
        · exfalso
          have heq2 : g₂.rank = 2 := by omega
          exact hXpn ⟨g₁, g₂, by rw [hg₁rank, heq2], hg₁pos, hch, hXg₁, hXg₂'⟩
        · exact hge
      obtain ⟨nn, hnn⟩ : ∃ nn, g₂.rank = 2 * nn + 2 := by
        rcases hev with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
      have hYwin : ∀ j, 2 * 0 + 1 ≤ j → j ≤ 2 * nn + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0 := by
        intro j _ hj
        rcases lt_or_eq_of_le hj with hlt | heq
        · exact Ywin_below_pl X Y hXY g₂ hXg₂' (by rw [hnn]; omega)
        · subst heq
          exact branchA_g3_Ynonzero_top X Y hXY hcommon nn g₂ hnn hch hXg₂'
      exact branchA_g3_assembly_type7 X Y hXY hsigeq 0 nn (Nat.zero_le _) g₁ g₂
        (by rw [hg₁rank]) hg₁pos hnn hch hXg₁ hXg₂ hne
        (fun j hj1 hj2 hoj => hprop j hj1 (by rw [hnn]; omega) hoj) hYwin
    | Positive =>
      -- `g₂ = g⁺(2q+2)`, type8 (non-double).  `a`-propagation via the positive-gene-aware
      -- `branchB_aprop_bdef`; `b` via `deep_bprop`; bottom even level via even2/even_interior.
      have hev : Even g₂.rank := rank_even_of_polarized X.1.2 (by rw [hch]; decide) hXg₂'
      have hgt : 4 ≤ g₂.rank := by
        rcases Nat.lt_or_ge g₂.rank 4 with hlt | hge2
        · exfalso
          have hgr : g₂.rank = 2 := by rcases hev with ⟨t, ht⟩; omega
          exact hne (Gene.ext (by rw [hg₁rank, hgr]) (by rw [hg₁pos, hch]))
        · exact hge2
      obtain ⟨q, hq⟩ : ∃ q, g₂.rank = 2 * q + 2 := by
        rcases hev with ⟨t, ht⟩
        exact ⟨t - 1, by omega⟩
      have hmq : 0 < q := by omega
      have hpar : ∀ g ∈ X.1.1.support,
          (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank) :=
        branchB_hpar X
      have hk1 : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → 2 * q + 3 ≤ g.rank := by
        intro g hg hgnp
        have hge2 := hk2 g hg (fun he => hgnp (he ▸ hg₁pos)); rw [hq] at hge2
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
      have htailq : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * q + 2 ≤ g.rank := by
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
      have hbdeep := branchB_case3_deep_bprop X Y hXY hgap 0 g₁ hg₁mult1.ge
        (2 * q + 2) htailq (by simpa using hbanchor1)
      have hbodd_fn : ∀ j, Odd j → 1 ≤ j → j < 2 * q + 3 →
          (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2 := by
        intro j hjo hj1 hjk
        obtain ⟨t, ht⟩ : ∃ t, j = 1 + 2 * t := ⟨(j - 1) / 2, by obtain ⟨r, hr⟩ := hjo; omega⟩
        have := hbdeep t (by omega)
        rwa [show 2 * 0 + 1 + 2 * t = j from by omega] at this
      have hhal_lem := branchB_case3_halive X Y hXY hgap g₁ (by omega) (2 * q + 2) htailq
      have hhal_fn : ∀ i, Odd i → 1 ≤ i → i + 1 ≤ 2 * q + 3 →
          (Sigma.sigma Y.1.1 i).1 + (Sigma.sigma Y.1.1 i).2 -
              ((Sigma.sigma Y.1.1 (i + 1)).1 + (Sigma.sigma Y.1.1 (i + 1)).2) ≤
          (Sigma.sigma X.1.1 i).1 + (Sigma.sigma X.1.1 i).2 -
              ((Sigma.sigma X.1.1 (i + 1)).1 + (Sigma.sigma X.1.1 (i + 1)).2) :=
        fun i hio hi1 hik => hhal_lem i (by obtain ⟨r, hr⟩ := hio; omega)
      have hpropa := branchB_aprop_bdef X Y hXY hgap hmin2 hpar (2 * q + 3) hk1 hbodd_fn hhal_fn
      refine branchB_case3_assembly_type8 X Y hXY 0 q (Nat.zero_le q) g₁ g₂
        (by rw [hg₁rank]) hg₁pos hq hch hXg₁ hXg₂ hne (by simpa using hbanchor1) ?_ ?_ ?_
      · intro j hjo hj1 hj2; exact hpropa j (by omega) hj2
      · intro j hjo hj1 hj2
        obtain ⟨t, ht⟩ : ∃ t, j = 2 * 0 + 1 + 2 * t := by
          obtain ⟨r, hr⟩ := hjo; exact ⟨r, by omega⟩
        rw [ht]; exact hbdeep t (by omega)
      · intro j hje hj1 hj2
        rcases Nat.lt_or_ge j 4 with hjlt | hjge
        · have hjeq : j = 2 := by obtain ⟨t, ht⟩ := hje; omega
          rw [hjeq]; exact even2_absorb_totalgap X Y hXY hgap hmin2
        · obtain ⟨s, hs⟩ : ∃ s, j = 2 * 0 + 2 + 2 * s := by
            obtain ⟨r, hr⟩ := hje; exact ⟨r - 1, by omega⟩
          have hjm1 : j - 1 = 2 * 0 + 1 + 2 * s := by omega
          have ha_n : (Sigma.sigma X.1.1 (j - 1)).1 + 1 ≤ (Sigma.sigma Y.1.1 (j - 1)).1 := by
            rw [hjm1]; exact hpropa (2 * 0 + 1 + 2 * s) (by omega) (by omega)
          have hb_n : (Sigma.sigma X.1.1 (j - 1)).2 + 1 ≤ (Sigma.sigma Y.1.1 (j - 1)).2 := by
            rw [hjm1]; exact hbdeep s (by omega)
          have hal_n := hhal_lem (j - 1) (by omega)
          rw [show j - 1 + 1 = j from by omega] at hal_n
          exact even_interior_absorb_neighbor X.1.2 Y.1.2 hje ha_n hb_n hal_n

/-- **§16 Case 3, b-deficient** (`m ≥ 4`, `g₁ = g⁺(2m'+2)`, `m' ≥ 1`, `b₁ < d₁`).  Mirror of
`branchB_case4_bdef`: type6/7 via `branchB_case4_aprop_totalgap`, type8/2g₁ via the
positive-gene-aware `branchB_aprop_bdef`; `b`-propagation from the level-1 deficiency
(`deep_bprop`), even levels via `even_interior_absorb_neighbor` (bottom even `2m'+2 ≥ 4`). -/
lemma branchB_case3_bdef (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (hbd : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pos : g₁.type = .Positive) (m' : ℕ) (hm' : g₁.rank = 2 * m' + 2) (hmpos : 0 < m') :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hminr : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank := fun g hg => hm' ▸ hg₁min g hg
  have hmin2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank := fun g hg => by have := hminr g hg; omega
  have hX2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Positive) :=
    fun g hg => ⟨hmin2 g hg, fun hgr => absurd (hminr g hg) (by rw [hgr]; omega)⟩
  have hpar : ∀ g ∈ X.1.1.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank) := branchB_hpar X
  have hg₁mult1 : X.1.1 g₁ = 1 ∨ 2 ≤ X.1.1 g₁ := by
    rcases Nat.lt_or_ge (X.1.1 g₁) 2 with h | h
    · exact Or.inl (by have : 1 ≤ X.1.1 g₁ := hXg₁; omega)
    · exact Or.inr h
  by_cases hmult : 2 ≤ X.1.1 g₁
  · -- `2 g⁺(2m'+2)` (type8 double, `p = m'`)
    have hk1 : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → 2 * m' + 3 ≤ g.rank := by
      intro g hg hgnp
      have hge := hminr g hg
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
    have htailq : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * m' + 2 ≤ g.rank := by
      intro g hg
      have hgpos : 0 < X.1.1 g := lt_of_lt_of_le
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg))
        (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
      exact hminr g (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgpos))
    have hbdeep := branchB_case3_deep_bprop X Y hXY hgap 0 g₁ (by omega)
      (2 * m' + 2) htailq (by
        obtain ⟨zX, hzX⟩ := sig_snd_isInt_odd X.1.2 (by decide : Odd 1)
        obtain ⟨zY, hzY⟩ := sig_snd_isInt_odd Y.1.2 (by decide : Odd 1)
        rw [hzX, hzY] at hbd ⊢
        have hz : zX < zY := by exact_mod_cast hbd
        have : (zX : ℚ) + 1 ≤ zY := by exact_mod_cast (by omega : zX + 1 ≤ zY)
        simpa using this)
    have hbodd_fn : ∀ j, Odd j → 1 ≤ j → j < 2 * m' + 3 →
        (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2 := by
      intro j hjo hj1 hjk
      obtain ⟨t, ht⟩ : ∃ t, j = 1 + 2 * t := ⟨(j - 1) / 2, by obtain ⟨r, hr⟩ := hjo; omega⟩
      have := hbdeep t (by omega)
      rwa [show 2 * 0 + 1 + 2 * t = j from by omega] at this
    have hhal_lem := branchB_case3_halive X Y hXY hgap g₁ (by omega) (2 * m' + 2) htailq
    have hhal_fn : ∀ i, Odd i → 1 ≤ i → i + 1 ≤ 2 * m' + 3 →
        (Sigma.sigma Y.1.1 i).1 + (Sigma.sigma Y.1.1 i).2 -
            ((Sigma.sigma Y.1.1 (i + 1)).1 + (Sigma.sigma Y.1.1 (i + 1)).2) ≤
        (Sigma.sigma X.1.1 i).1 + (Sigma.sigma X.1.1 i).2 -
            ((Sigma.sigma X.1.1 (i + 1)).1 + (Sigma.sigma X.1.1 (i + 1)).2) :=
      fun i hio hi1 hik => hhal_lem i (by obtain ⟨r, hr⟩ := hio; omega)
    have hpropa := branchB_aprop_bdef X Y hXY hgap hmin2 hpar (2 * m' + 3) hk1 hbodd_fn hhal_fn
    have hbanchor : (Sigma.sigma X.1.1 (2 * m' + 1)).2 + 1 ≤
        (Sigma.sigma Y.1.1 (2 * m' + 1)).2 := by
      have := hbdeep m' (by omega); rwa [show 2 * 0 + 1 + 2 * m' = 2 * m' + 1 from by omega] at this
    refine branchB_case3_assembly_type8_double X Y hXY m' g₁ hm' hg₁pos hmult hbanchor ?_ ?_
    · intro j hjo hj1 hj2; exact hpropa j (by omega) (by omega)
    · intro j hje hj1 hj2
      have hjeq : j = 2 * m' + 2 := by omega
      rw [hjeq]
      have ha_n : (Sigma.sigma X.1.1 (2 * m' + 2 - 1)).1 + 1 ≤
          (Sigma.sigma Y.1.1 (2 * m' + 2 - 1)).1 := by
        rw [show 2 * m' + 2 - 1 = 2 * m' + 1 from by omega]
        exact hpropa (2 * m' + 1) (by omega) (by omega)
      have hb_n : (Sigma.sigma X.1.1 (2 * m' + 2 - 1)).2 + 1 ≤
          (Sigma.sigma Y.1.1 (2 * m' + 2 - 1)).2 := by
        rw [show 2 * m' + 2 - 1 = 2 * m' + 1 from by omega]; exact hbanchor
      have hal_n := hhal_lem (2 * m' + 1) (by omega)
      rw [show 2 * m' + 1 + 1 = 2 * m' + 2 from by omega] at hal_n
      rw [show 2 * m' + 2 - 1 = 2 * m' + 1 from by omega] at *
      exact even_interior_absorb_neighbor X.1.2 Y.1.2 (by rw [hjeq] at hje; exact hje) ha_n hb_n
        (by rw [show 2 * m' + 1 + 1 = 2 * m' + 2 from by omega]; exact hal_n)
  · -- minimal gene `g₂` of `X - g₁`
    have hg₁one : X.1.1 g₁ = 1 := by have h1 : 1 ≤ X.1.1 g₁ := hXg₁; omega
    obtain ⟨g0, hg0mem, hg0ne⟩ : ∃ g ∈ X.1.1.support, g ≠ g₁ := by
      by_contra hcon
      push Not at hcon
      have hX1 : X.1.1.sum (fun _ m => (m : ℚ)) = 1 := by
        rw [Finsupp.sum, Finset.sum_eq_single g₁]
        · exact_mod_cast hg₁one
        · exact fun g hg hgne => absurd (hcon g hg) hgne
        · intro hni
          exact absurd (Finsupp.mem_support_iff.mpr (by rw [hg₁one]; norm_num)) hni
      have hYpos : 1 ≤ Y.1.1.sum (fun _ m => (m : ℚ)) := by
        have hYne : Y.1.1 ≠ 0 := by
          intro h0; have := Y.2; rw [h0] at this; simp at this
        obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hYne
        calc (1 : ℚ) ≤ (Y.1.1 g : ℚ) := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hg)
          _ ≤ Y.1.1.sum (fun _ m => (m : ℚ)) := by
              rw [Finsupp.sum]
              exact Finset.single_le_sum (f := fun a => ((Y.1.1 a : ℕ) : ℚ))
                (fun i _ => by positivity) hg
      have hXc : X.1.1.sum (fun _ m => (m : ℚ)) =
          (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
            ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
        have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
          have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
          simpa [Sigma.sigma] using this
        have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
            ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
        rw [h0, h1, Function.iterate_one]; exact cells.symm
      have hYc : Y.1.1.sum (fun _ m => (m : ℚ)) =
          (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
            ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) := by
        have h0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
          have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
          simpa [Sigma.sigma] using this
        have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
            ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
        rw [h0, h1, Function.iterate_one]; exact cells.symm
      have hr0X : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (m + 2 : ℕ) := by
        have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
        simpa [Sigma.sigma, X.2] using this
      have hr0Y : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (m + 2 : ℕ) := by
        have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
        simpa [Sigma.sigma, Y.2] using this
      rw [hXc] at hX1; rw [hYc] at hYpos; push_cast at hr0X hr0Y
      linarith [hgap, hX1, hYpos, hr0X, hr0Y]
    obtain ⟨g₂, hg₂mem, hg₂minS⟩ := Finset.exists_min_image
      (X.1.1.support.filter (fun g => g ≠ g₁)) Gene.rank
      ⟨g0, Finset.mem_filter.mpr ⟨hg0mem, hg0ne⟩⟩
    rw [Finset.mem_filter] at hg₂mem
    obtain ⟨hg₂supp, hg₂ne⟩ := hg₂mem
    have hXg₂' : 0 < X.1.1 g₂ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂supp)
    have hk2 : ∀ g ∈ X.1.1.support, g ≠ g₁ → g₂.rank ≤ g.rank :=
      fun g hg hgne => hg₂minS g (Finset.mem_filter.mpr ⟨hg, hgne⟩)
    have hne : g₁ ≠ g₂ := fun h => hg₂ne h.symm
    have hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]; exact hXg₂'
    have htailk : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, g₂.rank ≤ g.rank := by
      intro g hg
      have hgne : g ≠ g₁ := by
        rintro rfl
        rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl,
          hg₁one] at hg
        simp at hg
      have hgX : g ∈ X.1.1.support := by
        rw [Finsupp.mem_support_iff] at hg ⊢
        rwa [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hgne), Nat.sub_zero] at hg
      exact hk2 g hgX hgne
    have hge : 2 * m' + 2 ≤ g₂.rank := hm' ▸ hg₁min g₂ hg₂supp
    have hprop := branchB_case4_aprop_totalgap X Y hXY hgap g₁ hg₁one hX2 g₂.rank htailk
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
      have hev : Even g₂.rank := rank_even_of_polarized X.1.2 (by rw [hch]; decide) hXg₂'
      have hgt : 2 * m' + 4 ≤ g₂.rank := by
        rcases Nat.lt_or_ge g₂.rank (2 * m' + 4) with hlt | hge2
        · exfalso
          have hgr : g₂.rank = 2 * m' + 2 := by rcases hev with ⟨t, ht⟩; omega
          exact hne (Gene.ext (by rw [hm', hgr]) (by rw [hg₁pos, hch]))
        · exact hge2
      obtain ⟨q, hq⟩ : ∃ q, g₂.rank = 2 * q + 2 := by
        rcases hev with ⟨t, ht⟩
        exact ⟨t - 1, by omega⟩
      have hmq : m' < q := by omega
      have hk1 : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → 2 * q + 3 ≤ g.rank := by
        intro g hg hgnp
        have hge2 := hk2 g hg (fun he => hgnp (he ▸ hg₁pos)); rw [hq] at hge2
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
      have htailq : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * q + 2 ≤ g.rank :=
        fun g hg => by have := htailk g hg; rwa [hq] at this
      have hb1 : (Sigma.sigma X.1.1 1).2 + 1 ≤ (Sigma.sigma Y.1.1 1).2 := bd_anchor X Y hbd
      have hbdeep := branchB_case3_deep_bprop X Y hXY hgap 0 g₁ hg₁one.ge
        (2 * q + 2) htailq (by simpa using hb1)
      have hbanchor : (Sigma.sigma X.1.1 (2 * m' + 1)).2 + 1 ≤
          (Sigma.sigma Y.1.1 (2 * m' + 1)).2 := by
        have := hbdeep m' (by omega)
        rwa [show 2 * 0 + 1 + 2 * m' = 2 * m' + 1 from by omega] at this
      have hbodd_fn : ∀ j, Odd j → 1 ≤ j → j < 2 * q + 3 →
          (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2 := by
        intro j hjo hj1 hjk
        obtain ⟨t, ht⟩ : ∃ t, j = 1 + 2 * t := ⟨(j - 1) / 2, by obtain ⟨r, hr⟩ := hjo; omega⟩
        have := hbdeep t (by omega)
        rwa [show 2 * 0 + 1 + 2 * t = j from by omega] at this
      have hhal_lem := branchB_case3_halive X Y hXY hgap g₁ (by omega) (2 * q + 2) htailq
      have hhal_fn : ∀ i, Odd i → 1 ≤ i → i + 1 ≤ 2 * q + 3 →
          (Sigma.sigma Y.1.1 i).1 + (Sigma.sigma Y.1.1 i).2 -
              ((Sigma.sigma Y.1.1 (i + 1)).1 + (Sigma.sigma Y.1.1 (i + 1)).2) ≤
          (Sigma.sigma X.1.1 i).1 + (Sigma.sigma X.1.1 i).2 -
              ((Sigma.sigma X.1.1 (i + 1)).1 + (Sigma.sigma X.1.1 (i + 1)).2) :=
        fun i hio hi1 hik => hhal_lem i (by obtain ⟨r, hr⟩ := hio; omega)
      have hpropa := branchB_aprop_bdef X Y hXY hgap hmin2 hpar (2 * q + 3) hk1 hbodd_fn hhal_fn
      refine branchB_case3_assembly_type8 X Y hXY m' q hmq.le g₁ g₂
        hm' hg₁pos hq hch hXg₁ hXg₂ hne hbanchor ?_ ?_ ?_
      · intro j hjo hj1 hj2; exact hpropa j (by omega) hj2
      · intro j hjo hj1 hj2
        obtain ⟨t, ht⟩ : ∃ t, j = 1 + 2 * t := ⟨(j - 1) / 2, by obtain ⟨r, hr⟩ := hjo; omega⟩
        rw [ht]; have := hbdeep t (by omega)
        rwa [show 2 * 0 + 1 + 2 * t = 1 + 2 * t from by omega] at this
      · intro j hje hj1 hj2
        obtain ⟨s, hs⟩ : ∃ s, j = 2 * m' + 2 + 2 * s := by
          obtain ⟨r, hr⟩ := hje; exact ⟨r - m' - 1, by omega⟩
        have hjm1 : j - 1 = 2 * m' + 1 + 2 * s := by omega
        have ha_n : (Sigma.sigma X.1.1 (j - 1)).1 + 1 ≤ (Sigma.sigma Y.1.1 (j - 1)).1 := by
          rw [hjm1]; exact hpropa (2 * m' + 1 + 2 * s) (by omega) (by omega)
        have hb_n : (Sigma.sigma X.1.1 (j - 1)).2 + 1 ≤ (Sigma.sigma Y.1.1 (j - 1)).2 := by
          rw [hjm1]; have := hbdeep (m' + s) (by omega)
          rwa [show 2 * 0 + 1 + 2 * (m' + s) = 2 * m' + 1 + 2 * s from by omega] at this
        have hal_n := hhal_lem (j - 1) (by omega)
        rw [show j - 1 + 1 = j from by omega] at hal_n
        exact even_interior_absorb_neighbor X.1.2 Y.1.2 hje ha_n hb_n hal_n

/-- §16 Branch B, b-deficient, dispatch on `m' = (rank-2)/2`. -/
lemma branchB_pos_bdef (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (hbd : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pos : g₁.type = .Positive) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨m', hm'⟩ : ∃ m', g₁.rank = 2 * m' + 2 := by
    have hev := rank_even_of_polarized X.1.2 (by rw [hg₁pos]; decide) hXg₁
    have hpos := g₁.rank_pos
    rcases hev with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m' with hm0 | hmpos
  · exact branchB_case4_bdef m X Y hXY hcommon hsigeq hXpn hgap hbd g₁ hXg₁ hg₁min hg₁pos
      (by rw [hm', hm0])
  · exact branchB_case3_bdef m X Y hXY hcommon hsigeq hXpn hgap hbd
      g₁ hXg₁ hg₁min hg₁pos m' hm' hmpos

/-- §16 Branch B, negative charge (`g₁ = g⁻(m)`): sign-dual to the `g⁺` problem on `(-X, -Y)`.
When `b₁ < d₁` the dual has the level-1 `a`-deficiency (`branchB_pos`); otherwise `b₁ = d₁`
and the dual is `b`-deficient with the self-dual total gap (`branchB_pos_bdef`). -/
lemma branchB_neg (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁neg : g₁.type = .Negative) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg₁pos' : (-g₁ : Gene).type = .Positive := by rw [Gene.neg_type, hg₁neg]; rfl
  set Xd : nMixPiLambda (m + 2) :=
    ⟨- X.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, X.2]⟩ with Xd_def
  set Yd : nMixPiLambda (m + 2) :=
    ⟨- Y.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, Y.2]⟩ with Yd_def
  have hXdYd : Xd.1 < Yd.1 := by change (- X.1) < (- Y.1); exact Chromosome.neg_lt_neg_iff.2 hXY
  have hcommond : ¬∃ g : Gene, 0 < Xd.1.1 g ∧ 0 < Yd.1.1 g := by
    refine fun ⟨g, hgX, hgY⟩ ↦ hcommon ⟨- g, ?_, ?_⟩
    · rw [← Chromosome.neg_apply]; convert hgX using 2; rfl
    · rw [← Chromosome.neg_apply]; convert hgY using 2; rfl
  have hsigeqd : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Yd.1.1 ≠ 0 ∧
      Sigma.sigma Xd.1.1 k = Sigma.sigma Yd.1.1 k := by
    refine fun ⟨k, hkpos, hYd_ne, hsig⟩ ↦ hsigeq ⟨k, hkpos, ?_, ?_⟩
    · refine fun hYzero ↦ hYd_ne ?_
      change Chromosome.prime^[k] (- Y.1.1) = 0
      rw [← prime_iterate_neg, hYzero, _root_.neg_zero]
    · have hsig_swap : (signature (Chromosome.prime^[k] (- X.1.1))).swap =
        (signature (Chromosome.prime^[k] (- Y.1.1))).swap := congrArg Prod.swap hsig
      rwa [← @prime_iterate_neg k X.1.1, ← @prime_iterate_neg k Y.1.1,
        signature_neg, signature_neg, Prod.swap_swap, Prod.swap_swap] at hsig_swap
  have hXpnd : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < Xd.1.1 g ∧ 0 < Xd.1.1 h := by
    refine fun ⟨g, h, hrank, hgpos, hhneg, hgX, hhX⟩ ↦ hXpn ⟨- h, - g, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Gene.neg_rank, hrank]
    · rw [Gene.neg_type, hhneg]; rfl
    · rw [Gene.neg_type, hgpos]; rfl
    · rw [← Chromosome.neg_apply]; convert hhX using 2; rfl
    · rw [← Chromosome.neg_apply]; convert hgX using 2; rfl
  have hXg₁d : 0 < Xd.1.1 (-g₁) := by
    change 0 < (- X.1.1) (-g₁); rw [Chromosome.neg_apply, neg_neg]; exact hXg₁
  have hg₁mind : ∀ g ∈ Xd.1.1.support, (-g₁ : Gene).rank ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff] at hg
    have hng : X.1.1 (-g) ≠ 0 := by
      change (- X.1.1) g ≠ 0 at hg; rwa [Chromosome.neg_apply] at hg
    have h := hg₁min (-g) (Finsupp.mem_support_iff.mpr hng)
    rw [Gene.neg_rank] at h ⊢; exact h
  obtain ⟨W, hstepW, hWY⟩ : ∃ W : Mix (Pi, Lambda), MixPiLambda.Step Xd.1 W ∧ W ≤ Yd.1 := by
    by_cases hbd : (Sigma.sigma X.1.1 1).2 < (Sigma.sigma Y.1.1 1).2
    · have had : (Sigma.sigma Xd.1.1 1).1 < (Sigma.sigma Yd.1.1 1).1 := by
        change (signature (Chromosome.prime^[1] (- X.1.1))).1 <
          (signature (Chromosome.prime^[1] (- Y.1.1))).1
        rw [← @prime_iterate_neg 1 X.1.1, ← @prime_iterate_neg 1 Y.1.1,
          signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
        exact hbd
      exact branchB_pos m Xd Yd hXdYd hcommond hsigeqd hXpnd had (-g₁) hXg₁d hg₁mind hg₁pos'
    · have hbdom : (Sigma.sigma X.1.1 1).2 ≤ (Sigma.sigma Y.1.1 1).2 :=
        (le_iff_dominates.mp hXY.le 1).2
      have hgapd : (Sigma.sigma Xd.1.1 1).1 + (Sigma.sigma Xd.1.1 1).2 <
          (Sigma.sigma Yd.1.1 1).1 + (Sigma.sigma Yd.1.1 1).2 := by
        change (signature (Chromosome.prime^[1] (- X.1.1))).1 +
            (signature (Chromosome.prime^[1] (- X.1.1))).2 <
          (signature (Chromosome.prime^[1] (- Y.1.1))).1 +
            (signature (Chromosome.prime^[1] (- Y.1.1))).2
        rw [← @prime_iterate_neg 1 X.1.1, ← @prime_iterate_neg 1 Y.1.1,
          signature_neg, signature_neg, Prod.fst_swap, Prod.snd_swap, Prod.fst_swap, Prod.snd_swap]
        have ha' : (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 := ha
        have hbdom' : (signature (Chromosome.prime^[1] X.1.1)).2 ≤
          (signature (Chromosome.prime^[1] Y.1.1)).2 := hbdom
        linarith [ha', hbdom']
      have hbdd : (Sigma.sigma Xd.1.1 1).2 < (Sigma.sigma Yd.1.1 1).2 := by
        change (signature (Chromosome.prime^[1] (- X.1.1))).2 <
          (signature (Chromosome.prime^[1] (- Y.1.1))).2
        rw [← @prime_iterate_neg 1 X.1.1, ← @prime_iterate_neg 1 Y.1.1,
          signature_neg, signature_neg, Prod.snd_swap, Prod.snd_swap]
        exact ha
      exact branchB_pos_bdef m Xd Yd hXdYd hcommond hsigeqd hXpnd hgapd hbdd
        (-g₁) hXg₁d hg₁mind hg₁pos'
  refine ⟨- W, ?_, ?_⟩
  · exact MixPiLambda.Step.of_neg (by simpa only [neg_neg] using hstepW)
  · change (- W).1 ≤ Y.1.1
    rw [Mix.Pi_Lambda_neg_val]
    have hWY' : W.1 ≤ (- Y.1).1 := hWY
    rw [Mix.Pi_Lambda_neg_val] at hWY'
    simpa only [neg_neg] using Chromosome.neg_le_neg_iff.2 hWY'

/-- **Branch B** of §16 Case A for `Mix (Pi, Lambda)`: the minimal-rank gene `g₁` is
polarized.  Dispatch on its charge. -/
lemma exists_mutation_le_caseA_branchB (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pol : g₁.type ≠ .NonPolarized) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  cases hch : g₁.type with
  | NonPolarized => exact absurd hch hg₁pol
  | Positive => exact branchB_pos m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hch
  | Negative => exact branchB_neg m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hch

end MixPiLambda
