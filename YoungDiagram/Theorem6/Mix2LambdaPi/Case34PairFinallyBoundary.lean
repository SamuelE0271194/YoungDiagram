import YoungDiagram.Theorem6.Mix2LambdaPi.Case34PairFinallyQuad
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34PairFinallyTriple

/-!
# §17 "Finally m = 1" pair boundary dispatch (`Case34PairBranch:60`)

This file closes the `m = 1` boundary of the equal-rank-pair branch: the minimal
polarized pair of `X` is the rank-one pair `g⁺(1) + g⁻(1)` (both multiplicity
one).  Following Djoković's "Finally m = 1" argument, we take the minimal-rank
gene `gk` of the residue `X - g⁺(1) - g⁻(1)` (odd rank `k ≥ 3`, sign `ε`), and:

* if `X` also carries the opposite-sign gene `g⁻ᵉ(k)`, use the four-gene type13
  move `g⁺(1)+g⁻(1)+g⁺(k)+g⁻(k) → 2 g(k+1)`
  (`exists_mutation_le_pair_finally_quad`);
* otherwise use the three-gene type12 move `g⁺(1)+g⁻(1)+gᵉ(k) → gᵉ(k+2)`
  (`exists_mutation_le_pair_finally_triple`).

The residue-empty case `X = g⁺(1)+g⁻(1)` is vacuous: it forces every gene of `Y`
to have rank `≥ 3` (no rank-1 gene by disjointness, no rank-2 gene since the even
part sits in `2 • Λ`), so `Y.rank ≥ 3 > 2 = X.rank`, contradicting equal rank.
-/

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-- §17 "Finally m = 1" rank-one pair boundary dispatch. -/
lemma exists_mutation_le_pair_finally_boundary
    {m : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (_ : ∀ (p' n' : Gene),
      p'.rank = n'.rank →
        p'.type = .Positive → n'.type = .Negative →
          0 < X.1.1 p' → 0 < X.1.1 n' → gpos.rank ≤ p'.rank)
    (hone_one : X.1.1 gpos = 1 ∧ X.1.1 gneg = 1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  classical
  have hne_pos_neg : gpos ≠ gneg := fun h => by
    have := congrArg Gene.type h; rw [hgpos, hgneg] at this; exact absurd this (by decide)
  obtain ⟨hpos1, hneg1⟩ := hone_one
  set restPair : Chromosome :=
    X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1 with hrestPair
  have hX_pair_decomp :
      Finsupp.single gpos 1 + Finsupp.single gneg 1 + restPair = X.1.1 :=
    Mix2LambdaSection17.single_pair_add_rest (by omega) (by omega) hne_pos_neg
  by_cases hrest_ne : restPair = 0
  · -- Empty residue: `X = g⁺(1) + g⁻(1)`, rank 2; vacuous.
    exfalso
    have hXeq : X.1.1 = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
      rw [← hX_pair_decomp, hrest_ne, add_zero]
    have hXrank : X.1.1.rank = 2 := by
      rw [hXeq, map_add, rank_single, rank_single, hgpos1, hgneg1]; rfl
    have hXYrank : X.1.1.rank = Y.1.1.rank := by rw [X.2, Y.2]
    have hYne : Y.1.1 ≠ 0 := by
      intro hY
      rw [hY, map_zero] at hXYrank; omega
    have hYrank_ge : ∀ g : Gene, 0 < Y.1.1 g → 3 ≤ g.rank := by
      intro g hg
      by_contra hlt
      have hgpos_rank := g.rank_pos
      rcases (by omega : g.rank = 1 ∨ g.rank = 2) with hgr | hgr
      · have hgodd : Odd g.rank := by rw [hgr]; exact ⟨0, rfl⟩
        have hodd_part : 0 < Y.1.1.oddPart g := by
          rw [oddPart_eq, Finsupp.filter_apply, if_pos hgodd]; exact hg
        have hgpol : g.type ≠ GeneType.NonPolarized :=
          IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) g
            (Finsupp.mem_support_iff.mpr hodd_part.ne')
        cases htype : g.type with
        | NonPolarized => exact hgpol htype
        | Positive =>
            have hgeq : g = gpos := Gene.ext (by rw [hgr, hgpos1]) (by rw [htype, hgpos])
            have := hcommon gpos (by omega); rw [← hgeq] at this; omega
        | Negative =>
            have hgeq : g = gneg := Gene.ext (by rw [hgr, hgneg1]) (by rw [htype, hgneg])
            have := hcommon gneg (by omega); rw [← hgeq] at this; omega
      · have hgeven : Even g.rank := by rw [hgr]; exact ⟨1, rfl⟩
        have hg_evenPart : 0 < Y.1.1.evenPart g := by
          rw [evenPart_eq, Finsupp.filter_apply, if_pos hgeven]; exact hg
        have hg2 := Mix2LambdaSection17.two_le_coeff_of_mem_twoLambda Y.1.2.1
          (g := g) hg_evenPart
        rw [evenPart_eq, Finsupp.filter_apply, if_pos hgeven] at hg2
        have hmulle : Y.1.1 g • g.rank ≤ Y.1.1.rank := by
          rw [rank_def, Finsupp.sum]
          exact Finset.single_le_sum (f := fun g => Y.1.1 g • g.rank)
            (fun i _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hg.ne')
        have hle : 2 * g.rank ≤ Y.1.1.rank := by
          rw [smul_eq_mul] at hmulle
          calc 2 * g.rank ≤ Y.1.1 g * g.rank := Nat.mul_le_mul_right _ hg2
            _ ≤ Y.1.1.rank := hmulle
        rw [hgr] at hle; omega
    obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hYne
    have hgY : 0 < Y.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
    have h3 := hYrank_ge g hgY
    have hle_rank : g.rank ≤ Y.1.1.rank :=
      le_trans (le_maxRank g hg) (maxRank_le_rank _)
    omega
  · -- Nonempty residue: pick the minimal-rank gene `gk`.
    obtain ⟨gk, hgk_rest, hgk_min⟩ :=
      Mix2LambdaSection17.exists_min_rank_gene hrest_ne
    have hgkX : 0 < X.1.1 gk := by
      rw [← hX_pair_decomp]
      exact lt_of_lt_of_le hgk_rest (by rw [hrestPair]; exact Nat.le_add_left _ _)
    have hgk_pol : gk.type ≠ GeneType.NonPolarized :=
      IsPolarized_def'.mp hXpol gk (Finsupp.mem_support_iff.mpr (ne_of_gt hgkX))
    have hgk_odd : Odd gk.rank :=
      Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
        X.1.2 hgkX hgk_pol
    have hrest_no_one : ∀ l : Gene, 0 < restPair l → l.rank ≠ 1 := by
      intro l hl hl1
      have hlX : 0 < X.1.1 l := by
        rw [← hX_pair_decomp]
        exact lt_of_lt_of_le hl (by rw [hrestPair]; exact Nat.le_add_left _ _)
      have hlpol : l.type ≠ GeneType.NonPolarized :=
        IsPolarized_def'.mp hXpol l (Finsupp.mem_support_iff.mpr (ne_of_gt hlX))
      cases htype : l.type with
      | NonPolarized => exact hlpol htype
      | Positive =>
          have hleq : l = gpos := Gene.ext (by rw [hl1, hgpos1]) (by rw [htype, hgpos])
          have hposrest : (0 : ℕ) < restPair gpos := by rw [← hleq]; exact hl
          rw [hrestPair, Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_apply,
            Finsupp.single_apply, if_neg (Ne.symm hne_pos_neg), if_pos rfl,
            hpos1] at hposrest
          omega
      | Negative =>
          have hleq : l = gneg := Gene.ext (by rw [hl1, hgneg1]) (by rw [htype, hgneg])
          have hnegrest : (0 : ℕ) < restPair gneg := by rw [← hleq]; exact hl
          rw [hrestPair, Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_apply,
            Finsupp.single_apply, if_pos rfl, if_neg hne_pos_neg, hneg1] at hnegrest
          omega
    have hgk_ne_one : gk.rank ≠ 1 := hrest_no_one gk hgk_rest
    obtain ⟨n, hn⟩ := hgk_odd
    have hgk_rank : gk.rank = 2 * n + 1 := by omega
    have hn1 : 1 ≤ n := by omega
    have h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support,
        2 * n + 1 ≤ g.rank := by
      intro g hg
      have hgp : 0 < restPair g := by
        rw [hrestPair]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
      have := hgk_min g hgp
      rw [hgk_rank] at this; exact this
    have hXprime1_ne : Chromosome.prime^[1] X.1.1 ≠ 0 := by
      intro hprime
      have hall := (Chromosome.prime_iterate_eq_zero_rank_le (X := X.1.1) (k := 1)).2 hprime
      have := hall gk (Finsupp.mem_support_iff.mpr (ne_of_gt hgkX))
      omega
    have hYprime1_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
      intro hYzero
      have hle := le_iff_dominates.mp hXY.le 1
      rw [hYzero, map_zero] at hle
      exact hXprime1_ne (signature_eq_zero (le_antisymm hle (signature_nonneg _)))
    have hr1 : (Chromosome.prime^[1] X.1.1).rank <
        (Chromosome.prime^[1] Y.1.1).rank := h17_1 1 (by omega) hYprime1_ne
    have hseed1 :
        (signature (Chromosome.prime^[1] X.1.1)).1 <
            (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
          (signature (Chromosome.prime^[1] X.1.1)).2 <
            (signature (Chromosome.prime^[1] Y.1.1)).2 :=
      Mix2LambdaSection17.seed_strict_lt_at_odd X.1.2 Y.1.2 (i := 1) (by decide) hr1
    -- `prime^[k] Y ≠ 0` via the top-charge argument: `X` has `gᵉ(k)` but `Y`
    -- has no gene of rank `k` sign `ε` (disjointness), so `sig (prime^[k-1] Y)`
    -- vanishes in the `ε` component while `sig (prime^[k-1] X)` is `≥ 1`.
    have hYk_ne : Chromosome.prime^[2 * n + 1] Y.1.1 ≠ 0 := by
      intro hYzero
      have hYrank : ∀ h : Gene, 0 < Y.1.1 h → h.rank ≤ 2 * n + 1 := by
        intro h hh
        exact (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := 2 * n + 1)).2
          hYzero h (Finsupp.mem_support_iff.mpr (ne_of_gt hh))
      have hYpol_top : ∀ h : Gene, 0 < Y.1.1 h → h.rank = 2 * n + 1 →
          h.type ≠ GeneType.NonPolarized := by
        intro h hh hhrank
        have hhodd : Odd h.rank := by rw [hhrank]; exact ⟨n, by ring⟩
        have hodd_part : 0 < Y.1.1.oddPart h := by
          rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]; exact hh
        exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
          (Finsupp.mem_support_iff.mpr hodd_part.ne')
      cases htype : gk.type with
      | NonPolarized => exact absurd htype hgk_pol
      | Positive =>
          have hno_pos : Y.1.1 ⟨2 * n + 1, GeneType.Positive, by omega⟩ = 0 := by
            have htop_eq : (⟨2 * n + 1, GeneType.Positive, by omega⟩ : Gene) = gk :=
              Gene.ext (by dsimp; rw [hgk_rank]) htype.symm
            have hle := hcommon gk hgkX
            rw [htop_eq]; omega
          have hYfst0 :=
            signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
              (W := Y.1.1) (p := n) hYpol_top hYrank hno_pos
          have hXfst1 :=
            one_le_signature_prime_pred_fst_of_positive (X := X.1.1) (gpos := gk) htype hgkX
          have hXfst1' : 1 ≤ (signature (Chromosome.prime^[2 * n] X.1.1)).1 := by
            simpa [hgk_rank, show 2 * n + 1 - 1 = 2 * n by omega] using hXfst1
          have hdom := (le_iff_dominates.mp hXY.le (2 * n)).1
          rw [hYfst0] at hdom
          linarith
      | Negative =>
          have hno_neg : Y.1.1 ⟨2 * n + 1, GeneType.Negative, by omega⟩ = 0 := by
            have htop_eq : (⟨2 * n + 1, GeneType.Negative, by omega⟩ : Gene) = gk :=
              Gene.ext (by dsimp; rw [hgk_rank]) htype.symm
            have hle := hcommon gk hgkX
            rw [htop_eq]; omega
          have hYsnd0 :=
            signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
              (W := Y.1.1) (p := n) hYpol_top hYrank hno_neg
          have hXsnd1 :=
            one_le_signature_prime_pred_snd_of_negative (X := X.1.1) (gneg := gk) htype hgkX
          have hXsnd1' : 1 ≤ (signature (Chromosome.prime^[2 * n] X.1.1)).2 := by
            simpa [hgk_rank, show 2 * n + 1 - 1 = 2 * n by omega] using hXsnd1
          have hdom := (le_iff_dominates.mp hXY.le (2 * n)).2
          rw [hYsnd0] at hdom
          linarith
    have hgap : ∀ j, 0 < j → j ≤ 2 * n + 1 →
        ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1) :=
      pair_finally_gap' X Y hXY h17_1 hseed1 hgpos1 hgneg1 hgpos hgneg hne_pos_neg
        hpos1 hneg1 (k := 2 * n + 1) h2nd hgkX hgk_rank (by omega) ⟨n, by ring⟩ hYk_ne
    set gkn : Gene := ⟨2 * n + 1, -gk.type, by omega⟩ with hgkn_def
    by_cases hXgkn : 0 < X.1.1 gkn
    · cases htype : gk.type with
      | NonPolarized => exact absurd htype hgk_pol
      | Positive =>
          exact exists_mutation_le_pair_finally_quad X Y hXY hn1
            (gpos := gpos) (gneg := gneg) (gkp := gk) (gkn := gkn)
            hgpos1 hgneg1 hgpos hgneg hgk_rank rfl htype (by rw [hgkn_def, htype]; rfl)
            (by omega) (by omega) hgkX hXgkn hgap
      | Negative =>
          exact exists_mutation_le_pair_finally_quad X Y hXY hn1
            (gpos := gpos) (gneg := gneg) (gkp := gkn) (gkn := gk)
            hgpos1 hgneg1 hgpos hgneg rfl hgk_rank (by rw [hgkn_def, htype]; rfl) htype
            (by omega) (by omega) hXgkn hgkX hgap
    · have hXgkn0 : X.1.1 gkn = 0 := by omega
      have hlow : ∀ g : Gene, 0 < X.1.1 g → g.rank = 2 * n + 1 → g.type = gk.type := by
        intro g hgX hgr
        by_contra hne
        have hgpol : g.type ≠ GeneType.NonPolarized :=
          IsPolarized_def'.mp hXpol g (Finsupp.mem_support_iff.mpr (ne_of_gt hgX))
        have hg_eq_gkn : g = gkn := by
          apply Gene.ext
          · rw [hgr, hgkn_def]
          · rw [hgkn_def]
            cases htg : gk.type with
            | NonPolarized => exact absurd htg hgk_pol
            | Positive =>
                cases htg2 : g.type with
                | NonPolarized => exact absurd htg2 hgpol
                | Positive => exact absurd (htg2.trans htg.symm) hne
                | Negative => change GeneType.Negative = -GeneType.Positive; decide
            | Negative =>
                cases htg2 : g.type with
                | NonPolarized => exact absurd htg2 hgpol
                | Positive => change GeneType.Positive = -GeneType.Negative; decide
                | Negative => exact absurd (htg2.trans htg.symm) hne
        rw [hg_eq_gkn] at hgX; omega
      exact exists_mutation_le_pair_finally_triple hgk_pol X Y hXY hn1 hseed1
        hgpos1 hgneg1 hgpos hgneg hgk_rank rfl hpos1 hneg1 hgkX h2nd hlow hgap

end Mix2LambdaPi
