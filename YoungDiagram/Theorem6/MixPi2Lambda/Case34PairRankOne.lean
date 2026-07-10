import YoungDiagram.Theorem6.MixPi2Lambda.Case34Gaps

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 pair boundary at the minimal polarized rank

This is the Label 4 analogue of
`Mix2LambdaPi.pair_rank_one_zero_successor_false`.  The name of the file follows
the batch-C mirror plan, but the actual boundary rank is `2`: polarized genes in
`Mix (Pi, 2 • Lambda)` occur at even rank.
-/

/-- Shape core for the Label 4 minimal-pair boundary with vanishing successor.

If `X` is polarized with disjoint positive support from `Y`, both rank-`2`
polarized genes occur in `X`, and `prime^[3] Y = 0`, dominance forces
`prime^[3] X = 0`, so the polarized support of `X` is exactly the two rank-`2`
genes.  The same vanishing plus disjointness forces `Y` to have no even-rank
support, hence `Y ∈ 2 • Lambda` and its signature is diagonal.

Unlike the Label 3 rank-one boundary, this is not by itself contradictory:
rank-`2` positive and negative genes both have signature `(1,1)`. -/
lemma pair_rank_two_zero_successor_shape
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgpos2 : gpos.rank = 2) (hgneg2 : gneg.rank = 2)
    (hXpos : 0 < X.1.1 gpos) (hXneg : 0 < X.1.1 gneg)
    (hY3 : Chromosome.prime^[3] Y.1.1 = 0) :
    X.1.1 =
        Finsupp.single gpos (X.1.1 gpos) + Finsupp.single gneg (X.1.1 gneg) ∧
      Y.1.1 ∈ 2 • Lambda ∧
      ∃ n : ℕ, signature Y.1.1 = ((n : ℚ), (n : ℚ)) ∧
        signature X.1.1 =
          (((X.1.1 gpos + X.1.1 gneg : ℕ) : ℚ),
            ((X.1.1 gpos + X.1.1 gneg : ℕ) : ℚ)) := by
  -- Step 1: `prime^[3] X = 0`, hence every gene of `X` and `Y` has rank `≤ 3`.
  have hX3 : Chromosome.prime^[3] X.1.1 = 0 := by
    have hle := le_iff_dominates.mp hXY.le 3
    rw [hY3, map_zero] at hle
    exact signature_eq_zero (le_antisymm hle (signature_nonneg _))
  have hXrank : ∀ g ∈ X.1.1.support, g.rank ≤ 3 :=
    prime_iterate_eq_zero_rank_le.mpr hX3
  have hYrank : ∀ g ∈ Y.1.1.support, g.rank ≤ 3 :=
    prime_iterate_eq_zero_rank_le.mpr hY3
  have hgne : gpos ≠ gneg := by
    intro h; rw [h, hgneg] at hgpos; exact absurd hgpos (by decide)
  -- Step 2: `X.support ⊆ {gpos, gneg}`.
  have hXsupp : X.1.1.support ⊆ {gpos, gneg} := by
    intro g hg
    have hgX : 0 < X.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
    have hgpol : g.type ≠ GeneType.NonPolarized := IsPolarized_def'.mp hXpol g hg
    have hgeven : Even g.rank :=
      Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
        X.1.2 hgX hgpol
    have hg2 : g.rank = 2 := by
      have := hXrank g hg
      rcases hgeven with ⟨t, ht⟩
      have hpos := g.rank_pos
      omega
    cases htype : g.type with
    | NonPolarized => exact absurd htype hgpol
    | Positive =>
        have : g = gpos := Gene.ext (by rw [hg2, hgpos2]) (by rw [htype, hgpos])
        simp [this]
    | Negative =>
        have : g = gneg := Gene.ext (by rw [hg2, hgneg2]) (by rw [htype, hgneg])
        simp [this]
  -- Step 3: reconstruct `X` and compute its signature.
  have hsig_single : ∀ (g : Gene) (n : ℕ),
      signature (Finsupp.single g n) = (n : ℚ) • g.signature := by
    intro g n
    rw [signature_def]
    exact Finsupp.sum_single_index (by simp)
  have hXeq : X.1.1 =
      Finsupp.single gpos (X.1.1 gpos) + Finsupp.single gneg (X.1.1 gneg) := by
    ext g
    by_cases h1 : g = gpos
    · subst h1; simp [Finsupp.add_apply, hgne.symm]
    · by_cases h2 : g = gneg
      · subst h2; simp [Finsupp.add_apply, hgne]
      · have hgnot : g ∉ X.1.1.support := by
          intro hg
          rcases Finset.mem_insert.mp (hXsupp hg) with h | h
          · exact h1 h
          · exact h2 (Finset.mem_singleton.mp h)
        rw [Finsupp.notMem_support_iff.mp hgnot]
        simp [Finsupp.add_apply, Ne.symm h1, Ne.symm h2]
  have hgpos_sig : gpos.signature = (1, 1) := by
    rw [Gene.signature_of_positive hgpos, hgpos2]
    norm_num
  have hgneg_sig : gneg.signature = (1, 1) := by
    rw [Gene.signature_of_negative hgneg, hgneg2]
    norm_num
  have hsigX : signature X.1.1 =
      (((X.1.1 gpos + X.1.1 gneg : ℕ) : ℚ),
        ((X.1.1 gpos + X.1.1 gneg : ℕ) : ℚ)) := by
    conv_lhs => rw [hXeq, map_add, hsig_single, hsig_single, hgpos_sig, hgneg_sig]
    simp [smul_eq_mul, Nat.cast_add]
  -- Step 4: `Y` has no even-rank support, hence all of `Y` lies in `2 • Lambda`.
  have hYeven_zero : Y.1.1.evenPart = 0 := by
    rw [evenPart_eq]
    ext g
    rw [Finsupp.filter_apply]
    by_cases hg : g ∈ Y.1.1.support
    · have hYg : 0 < Y.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
      by_cases heven : Even g.rank
      · have hg2 : g.rank = 2 := by
          have := hYrank g hg
          rcases heven with ⟨t, ht⟩
          have hpos := g.rank_pos
          omega
        have hpol : g.type ≠ GeneType.NonPolarized := by
          have hgev : 0 < Y.1.1.evenPart g := by
            rw [evenPart_eq, Finsupp.filter_apply, if_pos heven]
            exact hYg
          exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.1) g
            (Finsupp.mem_support_iff.mpr hgev.ne')
        cases htype : g.type with
        | NonPolarized => exact absurd htype hpol
        | Positive =>
            have hggpos : g = gpos :=
              Gene.ext (by rw [hg2, hgpos2]) (by rw [htype, hgpos])
            have := hcommon gpos hXpos
            rw [← hggpos] at this
            omega
        | Negative =>
            have hggneg : g = gneg :=
              Gene.ext (by rw [hg2, hgneg2]) (by rw [htype, hgneg])
            have := hcommon gneg hXneg
            rw [← hggneg] at this
            omega
      · rw [if_neg heven]
        rfl
    · rw [Finsupp.notMem_support_iff.mp hg]
      simp
  have hYoddPart : Y.1.1.oddPart = Y.1.1 := by
    have hpd := Y.1.1.parity_decomposition
    rw [hYeven_zero, add_zero] at hpd
    exact hpd.symm
  have hY2L : Y.1.1 ∈ 2 • Lambda := hYoddPart ▸ Y.1.2.2
  obtain ⟨n, hn⟩ := Mix2LambdaSection17.signature_twoLambda_isNat hY2L
  exact ⟨hXeq, hY2L, n, hn, hsigX⟩

end MixPi2Lambda
