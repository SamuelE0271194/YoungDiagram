import YoungDiagram.Theorem6.Mix2LambdaPi.Case34NoPair

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-- Vacuity core for the rank-one `2+1` pair boundary with vanishing successor.

If `X` is polarized with `X < Y` disjoint, both `gpos = g⁺(1)` and `gneg = g⁻(1)`
occur in `X` with unequal multiplicities, and `prime^[2] Y = 0`, the hypotheses
are contradictory: dominance forces all of `X` to sit at rank `1`
(so `sig X = (X gpos, X gneg)`), while all of `Y` sits at rank `2`
(so `sig Y` is diagonal), forcing `X gpos = X gneg`.

This is the `m = 1` boundary of §17's `X ⊇ 2g⁺(m)+g⁻(m)`, `Y^{(m+1)} = 0` case,
where the paper's mutation `g⁺(m-2)+2g(m+1)` underflows. -/
lemma pair_rank_one_zero_successor_false
    {m : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hXpos : 0 < X.1.1 gpos) (hXneg : 0 < X.1.1 gneg)
    (hne : X.1.1 gpos ≠ X.1.1 gneg)
    (hY2 : Chromosome.prime^[2] Y.1.1 = 0) :
    False := by
  -- Step 1: `prime^[2] X = 0`, hence every gene of `X` (and `Y`) has rank `≤ 2`.
  have hX2 : Chromosome.prime^[2] X.1.1 = 0 := by
    have hle := le_iff_dominates.mp hXY.le 2
    rw [hY2, map_zero] at hle
    exact signature_eq_zero (le_antisymm hle (signature_nonneg _))
  have hXrank : ∀ g ∈ X.1.1.support, g.rank ≤ 2 :=
    prime_iterate_eq_zero_rank_le.mpr hX2
  have hYrank : ∀ g ∈ Y.1.1.support, g.rank ≤ 2 :=
    prime_iterate_eq_zero_rank_le.mpr hY2
  have hgne : gpos ≠ gneg := by
    intro h; rw [h, hgneg] at hgpos; exact absurd hgpos (by decide)
  -- Step 2: `X.support ⊆ {gpos, gneg}` (rank-1 polarized genes).
  have hXsupp : X.1.1.support ⊆ {gpos, gneg} := by
    intro g hg
    have hgX : 0 < X.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
    have hgpol : g.type ≠ GeneType.NonPolarized := IsPolarized_def'.mp hXpol g hg
    have hgodd : Odd g.rank :=
      Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi X.1.2 hgX hgpol
    have hg1 : g.rank = 1 := by
      have := hXrank g hg; obtain ⟨t, ht⟩ := hgodd; omega
    cases htype : g.type with
    | NonPolarized => exact absurd htype hgpol
    | Positive =>
        have : g = gpos := Gene.ext (by rw [hg1, hgpos1]) (by rw [htype, hgpos])
        simp [this]
    | Negative =>
        have : g = gneg := Gene.ext (by rw [hg1, hgneg1]) (by rw [htype, hgneg])
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
    · subst h1; simp [Finsupp.single_apply, Finsupp.add_apply, hgne.symm]
    · by_cases h2 : g = gneg
      · subst h2; simp [Finsupp.single_apply, Finsupp.add_apply, hgne]
      · have hgnot : g ∉ X.1.1.support := by
          intro hg
          rcases Finset.mem_insert.mp (hXsupp hg) with h | h
          · exact h1 h
          · exact h2 (Finset.mem_singleton.mp h)
        rw [Finsupp.notMem_support_iff.mp hgnot]
        simp [Finsupp.single_apply, Finsupp.add_apply, Ne.symm h1, Ne.symm h2]
  have hgpos_sig : gpos.signature = (1, 0) := by
    rw [Gene.signature_of_positive hgpos, if_neg (by rw [hgpos1]; decide), hgpos1]; norm_num
  have hgneg_sig : gneg.signature = (0, 1) := by
    rw [Gene.signature_of_negative hgneg, if_neg (by rw [hgneg1]; decide), hgneg1]; norm_num
  have hsigX : signature X.1.1 = ((X.1.1 gpos : ℚ), (X.1.1 gneg : ℚ)) := by
    conv_lhs => rw [hXeq, map_add, hsig_single, hsig_single, hgpos_sig, hgneg_sig]
    rw [Prod.ext_iff]
    constructor <;> simp
  -- Step 4: `Y` sits entirely at even rank, so `sig Y` is diagonal.
  have hYeven : ∀ g ∈ Y.1.1.support, Even g.rank := by
    intro g hg
    have hYg : 0 < Y.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
    by_contra hnoteven
    have hodd : Odd g.rank := Nat.not_even_iff_odd.mp hnoteven
    have hgodd_mem : 0 < Y.1.1.oddPart g := by
      rw [oddPart_eq, Finsupp.filter_apply, if_pos hodd]; exact hYg
    have hgpolY : g.type ≠ GeneType.NonPolarized :=
      IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) g
        (Finsupp.mem_support_iff.mpr (ne_of_gt hgodd_mem))
    have hg1 : g.rank = 1 := by
      have := hYrank g hg; obtain ⟨t, ht⟩ := hodd; omega
    cases htype : g.type with
    | NonPolarized => exact hgpolY htype
    | Positive =>
        have hggpos : g = gpos := Gene.ext (by rw [hg1, hgpos1]) (by rw [htype, hgpos])
        have := hcommon gpos hXpos; rw [← hggpos] at this; omega
    | Negative =>
        have hggneg : g = gneg := Gene.ext (by rw [hg1, hgneg1]) (by rw [htype, hgneg])
        have := hcommon gneg hXneg; rw [← hggneg] at this; omega
  have hYevenPart : Y.1.1.evenPart = Y.1.1 := by
    rw [evenPart_eq]; ext g
    rw [Finsupp.filter_apply]
    by_cases hg : g ∈ Y.1.1.support
    · rw [if_pos (hYeven g hg)]
    · rw [Finsupp.notMem_support_iff.mp hg]; simp
  have hY2L : Y.1.1 ∈ 2 • Lambda := hYevenPart ▸ Y.1.2.1
  obtain ⟨n, hn⟩ := Mix2LambdaSection17.signature_twoLambda_isNat hY2L
  -- Step 5: level-0 dominance + equal rank gives `sig X = sig Y`.
  have hle0 := le_iff_dominates.mp hXY.le 0
  simp only [Function.iterate_zero, id_eq] at hle0
  have hsum : (signature X.1.1).1 + (signature X.1.1).2 =
      (signature Y.1.1).1 + (signature Y.1.1).2 := by
    rw [signature_sum_eq_rank, signature_sum_eq_rank, X.2, Y.2]
  have hsigeq : signature X.1.1 = signature Y.1.1 :=
    Prod.ext (le_antisymm hle0.1 (by linarith [hle0.2]))
      (le_antisymm hle0.2 (by linarith [hle0.1]))
  rw [hsigX, hn] at hsigeq
  have e1 : (X.1.1 gpos : ℚ) = n := congrArg Prod.fst hsigeq
  have e2 : (X.1.1 gneg : ℚ) = n := congrArg Prod.snd hsigeq
  exact hne (by exact_mod_cast e1.trans e2.symm)

end Mix2LambdaPi
