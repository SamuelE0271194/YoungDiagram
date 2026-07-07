import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Seed

/-!
# §17 "Finally m = 1" pair case: value-(1,1) gap chain

This file builds the reusable seed + even-window strictness for the boundary
case where `X ⊃ g⁺(1) + g⁻(1)` is the minimal (rank-one) pair.  Removing the
rank-one pair `gpos + gneg` yields `Xr := X - gpos - gneg`, all of whose genes
have rank `≥ k` (the minimal rank of `X - pair`).  Since `prime` annihilates
rank-one genes, `sigma X j = sigma Xr j` for `j ≥ 1`, so `X`'s interior
two-step drops equal `Xr.sum = D - 2`, while the level `0 → 2` drop is
`D - 1` (the rank-one pair contributes `(1,1)` at level `0`).  Against the
strong `Y`-drop bound `≤ D - 2` (from the level-1 `+2` gap) this yields strict
domination on every even level `2 ≤ j ≤ k` in both components.
-/

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

variable {N k : ℕ}

/-- Level `≥ 1` agreement after removing the rank-one pair: both rank-one genes
are annihilated by a single `prime`, so all higher iterates agree. -/
private lemma pair_shift (X : nMix2LambdaPi N) {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1)
    {i : ℕ} (hi : 1 ≤ i) :
    Sigma.sigma X.1.1 i =
      Sigma.sigma (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1) i := by
  have hkillpos : Chromosome.prime^[i] (Finsupp.single gpos 1) = 0 := by
    rw [← prime_iterate_eq_zero_rank_le]
    intro g hg
    rw [Finsupp.support_single_ne_zero _ (by norm_num), Finset.mem_singleton] at hg
    subst hg; omega
  have hkillneg : Chromosome.prime^[i] (Finsupp.single gneg 1) = 0 := by
    rw [← prime_iterate_eq_zero_rank_le]
    intro g hg
    rw [Finsupp.support_single_ne_zero _ (by norm_num), Finset.mem_singleton] at hg
    subst hg; omega
  have hdecomp :
      Finsupp.single gpos 1 + Finsupp.single gneg 1 +
        (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1) = X.1.1 :=
    Mix2LambdaSection17.single_pair_add_rest hXpos1.ge hXneg1.ge hne
  conv_lhs => rw [← hdecomp]
  rw [Sigma.sigma_linearity, Sigma.sigma_linearity]
  simp only [Sigma.sigma, hkillpos, hkillneg, map_zero, zero_add]

/-- Level-`0` signature of `Xr = X - pair` is `sigma X 0 - (1,1)`. -/
private lemma pair_level0 (X : nMix2LambdaPi N) {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1) :
    Sigma.sigma (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1) 0 =
      Sigma.sigma X.1.1 0 - ((1 : ℚ), (1 : ℚ)) := by
  have hdecomp :
      Finsupp.single gpos 1 + Finsupp.single gneg 1 +
        (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1) = X.1.1 :=
    Mix2LambdaSection17.single_pair_add_rest hXpos1.ge hXneg1.ge hne
  have hpos_sig : Sigma.sigma (Finsupp.single gpos 1 : Chromosome) 0 = ((1 : ℚ), (0 : ℚ)) := by
    have he : (Finsupp.single gpos 1 : Chromosome) = Gene.ofRank gpos.rank gpos.type :=
      Gene.ofRank_eq_gene.symm
    rw [Sigma.sigma, Function.iterate_zero, id, he, hgpos1, hgpos, signature_ofRank_one_positive]
  have hneg_sig : Sigma.sigma (Finsupp.single gneg 1 : Chromosome) 0 = ((0 : ℚ), (1 : ℚ)) := by
    have he : (Finsupp.single gneg 1 : Chromosome) = Gene.ofRank gneg.rank gneg.type :=
      Gene.ofRank_eq_gene.symm
    rw [Sigma.sigma, Function.iterate_zero, id, he, hgneg1, hgneg, signature_ofRank_one_negative]
  have hlin : Sigma.sigma X.1.1 0 =
      Sigma.sigma (Finsupp.single gpos 1 : Chromosome) 0 +
        Sigma.sigma (Finsupp.single gneg 1 : Chromosome) 0 +
        Sigma.sigma (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1) 0 := by
    conv_lhs => rw [← hdecomp]
    rw [Sigma.sigma_linearity, Sigma.sigma_linearity]
  rw [hlin, hpos_sig, hneg_sig]
  ext <;> simp

/-- Total gene count of `Xr` in terms of the level `0`/`1` sums of `X`:
`Xr.sum = D - 2` where `D = (r_0 - r_1)`.  Removing the two rank-one genes drops
the total rank by `2`, and `prime Xr = prime X`. -/
private lemma pair_cells (X : nMix2LambdaPi N) {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1) :
    ((X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).sum fun _ m => (m : ℚ)) =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
  have hcells := MixLambdaPi.cells (Z := X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1)
  have hN : X.1.1.rank = N := X.2
  -- rank of Xr = N - 2
  have hgneg_pos_after : 0 < (X.1.1 - Finsupp.single gpos 1 : Chromosome) gneg := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne]
    omega
  have hrank1 : (X.1.1 - Finsupp.single gpos 1).rank = X.1.1.rank - gpos.rank :=
    rank_sub_single (show 0 < X.1.1 gpos by rw [hXpos1]; omega)
  have hrank2 : (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).rank =
      (X.1.1 - Finsupp.single gpos 1).rank - gneg.rank :=
    rank_sub_single hgneg_pos_after
  have hXrank : (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).rank = N - 2 := by
    rw [hrank2, hrank1, hgpos1, hgneg1, hN]; omega
  -- prime Xr = prime X
  have hkillpos : Chromosome.prime (Finsupp.single gpos 1) = 0 := by
    have h1 : Chromosome.prime^[1] (Finsupp.single gpos 1) = 0 := by
      rw [← prime_iterate_eq_zero_rank_le]
      intro g hg
      rw [Finsupp.support_single_ne_zero _ (by norm_num), Finset.mem_singleton] at hg
      subst hg; omega
    simpa using h1
  have hkillneg : Chromosome.prime (Finsupp.single gneg 1) = 0 := by
    have h1 : Chromosome.prime^[1] (Finsupp.single gneg 1) = 0 := by
      rw [← prime_iterate_eq_zero_rank_le]
      intro g hg
      rw [Finsupp.support_single_ne_zero _ (by norm_num), Finset.mem_singleton] at hg
      subst hg; omega
    simpa using h1
  have hprime_eq :
      (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).prime = X.1.1.prime := by
    have hdecomp :
        Finsupp.single gpos 1 + Finsupp.single gneg 1 +
          (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1) = X.1.1 :=
      Mix2LambdaSection17.single_pair_add_rest hXpos1.ge hXneg1.ge hne
    have := congrArg Chromosome.prime hdecomp
    rw [map_add, map_add, hkillpos, hkillneg, zero_add, zero_add] at this
    exact this
  have hr0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, hN] using @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
  have hr1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      (X.1.1.prime.rank : ℚ) := by
    simpa [Sigma.sigma, Function.iterate_one] using
      @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
  rw [hr0, hr1, ← hcells, hXrank, hprime_eq]
  have hN2 : (2 : ℕ) ≤ N := by
    have hle : gneg.rank ≤ (X.1.1 - Finsupp.single gpos 1).rank :=
      le_trans (le_maxRank gneg (Finsupp.mem_support_iff.mpr (ne_of_gt hgneg_pos_after)))
        (maxRank_le_rank _)
    rw [hrank1, hgpos1, hgneg1, hN] at hle
    omega
  push_cast [Nat.cast_sub hN2]
  ring

/-- Interior first-component 2-step drop (level `≥ 1`, below `k`): equals
`D - 2 = r_0 - r_1 - 2`, since at levels `≥ 1` the rank-one pair is gone and all
surviving genes have rank `≥ k`. -/
private lemma pair_Xdrop_fst (X : nMix2LambdaPi N) {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, k ≤ g.rank)
    {i : ℕ} (hi : 1 ≤ i) (hik : i + 2 ≤ k) :
    (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
  have hshift_i := pair_shift X hgpos1 hgneg1 hne hXpos1 hXneg1 (i := i) hi
  have hshift_i2 := pair_shift X hgpos1 hgneg1 hne hXpos1 hXneg1 (i := i + 2) (by omega)
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, i + 2 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  have hdrop := MixLambdaPi.twostep h2
  have hcells := pair_cells X hgpos1 hgneg1 hne hXpos1 hXneg1
  have e_i := congrArg Prod.fst hshift_i
  have e_i2 := congrArg Prod.fst hshift_i2
  rw [e_i, e_i2, hdrop, hcells]

/-- Interior second-component 2-step drop. -/
private lemma pair_Xdrop_snd (X : nMix2LambdaPi N) {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, k ≤ g.rank)
    {i : ℕ} (hi : 1 ≤ i) (hik : i + 2 ≤ k) :
    (Sigma.sigma X.1.1 i).2 - (Sigma.sigma X.1.1 (i + 2)).2 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
  have hshift_i := pair_shift X hgpos1 hgneg1 hne hXpos1 hXneg1 (i := i) hi
  have hshift_i2 := pair_shift X hgpos1 hgneg1 hne hXpos1 hXneg1 (i := i + 2) (by omega)
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, i + 2 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  have hdrop := MixLambdaPi.twostep_snd h2
  have hcells := pair_cells X hgpos1 hgneg1 hne hXpos1 hXneg1
  have e_i := congrArg Prod.snd hshift_i
  have e_i2 := congrArg Prod.snd hshift_i2
  rw [e_i, e_i2, hdrop, hcells]

/-- Level-2 seed, first component: `a_2 < c_2`.  At the seed the `X`-drop
`a_0 - a_2 = D - 1` (the pair contributes `1`), while the strong `Y`-drop bound
gives `c_0 - c_2 ≤ D - 2`; with `a_0 = c_0` this yields strict domination. -/
private lemma pair_seed_fst (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 < (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 < (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, k ≤ g.rank)
    (hk : 2 ≤ k) :
    (Sigma.sigma X.1.1 2).1 < (Sigma.sigma Y.1.1 2).1 := by
  have hshift2 := pair_shift X hgpos1 hgneg1 hne hXpos1 hXneg1 (i := 2) (by omega)
  have hlevel0 := pair_level0 X hgpos1 hgneg1 hgpos hgneg hne hXpos1 hXneg1
  have hcells := pair_cells X hgpos1 hgneg1 hne hXpos1 hXneg1
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, 0 + 2 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  have hXrdrop := MixLambdaPi.twostep h2
  have hYdrop := case4_Ydrop_fst_strong_even (i := 0) X Y hseed1 (by decide)
  have h0eq := congrArg Prod.fst (sigma_zero_eq X Y hXY)
  have e_shift2 := congrArg Prod.fst hshift2
  have e_lvl0 := congrArg Prod.fst hlevel0
  simp only [Prod.fst_sub, Prod.fst_one] at e_lvl0
  linarith

/-- Level-2 seed, second component: `b_2 < d_2`. -/
private lemma pair_seed_snd (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 < (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 < (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, k ≤ g.rank)
    (hk : 2 ≤ k) :
    (Sigma.sigma X.1.1 2).2 < (Sigma.sigma Y.1.1 2).2 := by
  have hshift2 := pair_shift X hgpos1 hgneg1 hne hXpos1 hXneg1 (i := 2) (by omega)
  have hlevel0 := pair_level0 X hgpos1 hgneg1 hgpos hgneg hne hXpos1 hXneg1
  have hcells := pair_cells X hgpos1 hgneg1 hne hXpos1 hXneg1
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, 0 + 2 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  have hXrdrop := MixLambdaPi.twostep_snd h2
  have hYdrop := case4_Ydrop_snd_strong_even (i := 0) X Y hseed1 (by decide)
  have h0eq := congrArg Prod.snd (sigma_zero_eq X Y hXY)
  have e_shift2 := congrArg Prod.snd hshift2
  have e_lvl0 := congrArg Prod.snd hlevel0
  simp only [Prod.snd_sub, Prod.snd_one] at e_lvl0
  linarith

/-- Even-level first-component window: strict on every even level `2 ≤ 2+2t ≤ k`. -/
private lemma pair_window_fst (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 < (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 < (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, k ≤ g.rank)
    (hk : 2 ≤ k) :
    ∀ t : ℕ, 2 + 2 * t ≤ k →
      (Sigma.sigma X.1.1 (2 + 2 * t)).1 < (Sigma.sigma Y.1.1 (2 + 2 * t)).1 := by
  intro t
  induction t with
  | zero =>
      intro _
      simpa using pair_seed_fst X Y hXY hseed1 hgpos1 hgneg1 hgpos hgneg hne hXpos1 hXneg1 h2nd hk
  | succ n ih =>
      intro ht
      have hprev := ih (by omega)
      have hXdrop := pair_Xdrop_fst X hgpos1 hgneg1 hne hXpos1 hXneg1 h2nd
        (i := 2 + 2 * n) (by omega) (by omega)
      have hYdrop := case4_Ydrop_fst_strong_even (i := 2 + 2 * n) X Y hseed1 ⟨n + 1, by ring⟩
      have he : 2 + 2 * (n + 1) = (2 + 2 * n) + 2 := by ring
      rw [he]
      linarith

/-- Even-level second-component window. -/
private lemma pair_window_snd (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 < (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 < (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, k ≤ g.rank)
    (hk : 2 ≤ k) :
    ∀ t : ℕ, 2 + 2 * t ≤ k →
      (Sigma.sigma X.1.1 (2 + 2 * t)).2 < (Sigma.sigma Y.1.1 (2 + 2 * t)).2 := by
  intro t
  induction t with
  | zero =>
      intro _
      simpa using pair_seed_snd X Y hXY hseed1 hgpos1 hgneg1 hgpos hgneg hne hXpos1 hXneg1 h2nd hk
  | succ n ih =>
      intro ht
      have hprev := ih (by omega)
      have hXdrop := pair_Xdrop_snd X hgpos1 hgneg1 hne hXpos1 hXneg1 h2nd
        (i := 2 + 2 * n) (by omega) (by omega)
      have hYdrop := case4_Ydrop_snd_strong_even (i := 2 + 2 * n) X Y hseed1 ⟨n + 1, by ring⟩
      have he : 2 + 2 * (n + 1) = (2 + 2 * n) + 2 := by ring
      rw [he]
      linarith

/-- Combined value-`(1,1)` gap on every even level `2 ≤ 2 + 2t ≤ k` for the §17
"Finally m = 1" rank-one pair configuration.  This is the reusable interior gap
consumed by the type12/type13 boundary mutations (odd interior levels and the
`j = k` / successor edge levels are handled separately by the caller). -/
lemma pair_finally_gap_even (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 < (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 < (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hne : gpos ≠ gneg) (hXpos1 : X.1.1 gpos = 1) (hXneg1 : X.1.1 gneg = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support, k ≤ g.rank)
    (hk : 2 ≤ k) :
    ∀ t : ℕ, 2 + 2 * t ≤ k →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[2 + 2 * t] X.1.1) ≤
        signature (Chromosome.prime^[2 + 2 * t] Y.1.1) := by
  intro t ht
  have hfst := pair_window_fst X Y hXY hseed1 hgpos1 hgneg1 hgpos hgneg hne hXpos1 hXneg1 h2nd hk t ht
  have hsnd := pair_window_snd X Y hXY hseed1 hgpos1 hgneg1 hgpos hgneg hne hXpos1 hXneg1 h2nd hk t ht
  exact Mix2LambdaSection17.one_one_le_of_both_lt X.1.2 Y.1.2 hfst hsnd

end Mix2LambdaPi
