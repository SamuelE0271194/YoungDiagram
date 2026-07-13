import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairSingleBoundary

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

private lemma pair_high_zero_Y_np_successor_two
    {m q : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1)
    (hpos_rank : gpos.rank = 2 * q + 4)
    (hYsucc : Chromosome.prime^[2 * q + 5] Y.1.1 = 0) :
    2 ≤ Y.1.1 ⟨2 * q + 5, GeneType.NonPolarized, by omega⟩ := by
  have hgap := type15_diagonal_gap_rank
    (q := q + 1) (ε := GeneType.Positive) (by decide)
    X Y hXY hcommon h17_1 gpos gneg hgpos (by simpa using hgneg)
      (by omega) hrank (by omega) (by omega)
  have hgap' : ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * q + 4] X.1.1) ≤
      signature (Chromosome.prime^[2 * q + 4] Y.1.1) := by
    rw [show 2 * q + 4 = 2 * (q + 1) + 2 by omega]
    exact hgap
  let Ytop : Chromosome := Chromosome.prime^[2 * q + 4] Y.1.1
  have hYtop_ne : Ytop ≠ 0 := by
    intro hz
    have hYsigTop : signature Ytop = 0 := by rw [hz, map_zero]
    have hYsig : signature (Chromosome.prime^[2 * q + 4] Y.1.1) = 0 := by
      change signature Ytop = 0
      exact hYsigTop
    have hf := hgap'.1
    rw [hYsig] at hf
    have hnn := (signature_nonneg
      (Chromosome.prime^[2 * q + 4] X.1.1)).1
    have hnn' : (0 : ℚ) ≤
        (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 := hnn
    simp only [Prod.fst_add, Prod.fst_zero] at hf
    linarith
  obtain ⟨gtop, hgtop_support⟩ := Finsupp.support_nonempty_iff.mpr hYtop_ne
  have hgtop_pos : 0 < Ytop gtop :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hgtop_support)
  have hYtop_prime : Ytop.prime = 0 := by
    change Chromosome.prime (Chromosome.prime^[2 * q + 4] Y.1.1) = 0
    simpa [Function.iterate_succ_apply',
      show 2 * q + 4 + 1 = 2 * q + 5 by omega] using hYsucc
  have hgtop_rank : gtop.rank = 1 :=
    rank_one_of_prime_eq_zero hYtop_prime hgtop_support
  have hYtop_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate
    Y.1.2 (2 * q + 4)
  rw [if_pos (show Even (2 * q + 4) from ⟨q + 2, by ring⟩)] at hYtop_mem
  have hodd : Odd gtop.rank := by rw [hgtop_rank]; exact ⟨0, rfl⟩
  have hodd_pos : 0 < Ytop.oddPart gtop := by
    rw [oddPart_eq, Finsupp.filter_apply, if_pos hodd]
    exact hgtop_pos
  have htwo : 2 ≤ Ytop.oddPart gtop := by
    have hmem := hYtop_mem.2
    obtain ⟨W0, _, hW0eq⟩ :=
      (AddSubmonoid.mem_smul_pointwise_iff_exists Ytop.oddPart 2 Lambda).mp hmem
    change 2 • W0 = Ytop.oddPart at hW0eq
    have heq := DFunLike.congr_fun hW0eq gtop
    simp only [Finsupp.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at heq
    rw [← heq]
    omega
  have hgtop_type : gtop.type = GeneType.NonPolarized :=
    Mix2LambdaSection17.type_eq_nonpolarized_of_mem_twoLambda
      hYtop_mem.2 hodd_pos
  have hcoeff := prime_iterate_coeff (2 * q + 4) Y.1.1 gtop
  have hgene :
      (⟨gtop.rank + (2 * q + 4), gtop.type,
        Nat.le_add_right_of_le gtop.rank_pos⟩ : Gene) =
        ⟨2 * q + 5, GeneType.NonPolarized, by omega⟩ := by
    apply Gene.ext
    · dsimp
      omega
    · exact hgtop_type
  have htwo_top : 2 ≤ Ytop gtop := by
    simpa [oddPart_eq, Finsupp.filter_apply, hodd] using htwo
  change 2 ≤ (Chromosome.prime^[2 * q + 4] Y.1.1) gtop at htwo_top
  rwa [hcoeff, hgene] at htwo_top

lemma pair_high_zero_rest_ne
    {m q : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1)
    (hpos_rank : gpos.rank = 2 * q + 4)
    (hYsucc : Chromosome.prime^[2 * q + 5] Y.1.1 = 0) :
    X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1 ≠ 0 := by
  intro hrest
  have hne : gpos ≠ gneg := by
    intro h
    have := congrArg Gene.type h
    rw [hgpos, hgneg] at this
    contradiction
  have hdecomp := Mix2LambdaSection17.single_pair_add_rest
    (X := X.1.1) (g := gpos) (h := gneg) (by omega) (by omega) hne
  have hXeq : X.1.1 = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
    rw [← hdecomp, hrest, add_zero]
  have hXrank : X.1.1.rank = 2 * q + 4 + (2 * q + 4) := by
    have hneg_rank : gneg.rank = 2 * q + 4 := by omega
    rw [hXeq, map_add, rank_single, rank_single, hpos_rank, hneg_rank]
    simp
  have hYtwo := pair_high_zero_Y_np_successor_two
    X Y hXY hcommon h17_1 gpos gneg hrank hgpos hgneg hpos hneg
      hpos_rank hYsucc
  let gNP : Gene := ⟨2 * q + 5, GeneType.NonPolarized, by omega⟩
  have hYrank_lower : 2 * (2 * q + 5) ≤ Y.1.1.rank := by
    have hYg : 0 < Y.1.1 gNP := by simpa [gNP] using (lt_of_lt_of_le (by omega) hYtwo)
    let Yminus : Chromosome := Y.1.1 - Finsupp.single gNP 1
    have hsub_rank : Yminus.rank = Y.1.1.rank - gNP.rank :=
      rank_sub_single hYg
    have hsub_pos : 0 < Yminus gNP := by
      dsimp [Yminus]
      simp [gNP]
      omega
    have hgene_le : gNP.rank ≤ Yminus.rank :=
      le_trans (le_maxRank gNP
        (Finsupp.mem_support_iff.mpr hsub_pos.ne')) (maxRank_le_rank _)
    rw [hsub_rank] at hgene_le
    dsimp [gNP] at hgene_le
    omega
  have hXYrank : X.1.1.rank = Y.1.1.rank := by rw [X.2, Y.2]
  rw [← hXYrank, hXrank] at hYrank_lower
  omega

lemma pair_high_zero_max_remainder_data
    {m q : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1)
    (hpos_rank : gpos.rank = 2 * q + 4)
    (hYsucc : Chromosome.prime^[2 * q + 5] Y.1.1 = 0) :
    ∃ (gε : Gene) (s : ℕ),
      0 < (X.1.1 - Finsupp.single gpos 1 -
        Finsupp.single gneg 1 : Chromosome) gε ∧
      0 < X.1.1 gε ∧ gε ≠ gpos ∧ gε ≠ gneg ∧
      (∀ h : Gene,
        0 < (X.1.1 - Finsupp.single gpos 1 -
          Finsupp.single gneg 1 : Chromosome) h →
          h.rank ≤ gε.rank) ∧
      gε.type ≠ GeneType.NonPolarized ∧
      gε.rank = 2 * s + 2 ∧ s ≤ q + 1 := by
  have hne : gpos ≠ gneg := by
    intro h
    have := congrArg Gene.type h
    rw [hgpos, hgneg] at this
    contradiction
  have hrest := pair_high_zero_rest_ne X Y hXY hcommon h17_1
    gpos gneg hrank hgpos hgneg hpos hneg hpos_rank hYsucc
  obtain ⟨gε, hgε_rest, hgεX, hne_pos, hne_neg, hgεmax⟩ :=
    Mix2LambdaSection17.exists_max_rank_gene_of_single_pair_rest_ne_zero
      hpos hneg hne hrest
  have hgεpol : gε.type ≠ GeneType.NonPolarized :=
    IsPolarized_def'.mp hXpol gε (Finsupp.mem_support_iff.mpr hgεX.ne')
  have hgεeven :=
    Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
      X.1.2 hgεX hgεpol
  have hgεle : gε.rank ≤ 2 * q + 5 :=
    Mix2LambdaSection17.rank_le_of_le_prime_zero hXY.le hYsucc hgεX
  obtain ⟨r, hr⟩ := hgεeven
  have hrpos : 0 < r := by
    have := gε.rank_pos
    omega
  let s := r - 1
  have hrs : r = s + 1 := by omega
  have hgrank : gε.rank = 2 * s + 2 := by omega
  have hsle : s ≤ q + 1 := by omega
  exact ⟨gε, s, hgε_rest, hgεX, hne_pos, hne_neg, hgεmax,
    hgεpol, hgrank, hsle⟩

private lemma pair_high_zero_mid_gap
    {m q s j : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (gpos gneg gε : Gene)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1)
    (hpos_rank : gpos.rank = 2 * q + 4)
    (hneg_rank : gneg.rank = 2 * q + 4)
    (hgε_rank : gε.rank = 2 * s + 2)
    (hgεmax : ∀ h : Gene,
      0 < (X.1.1 - Finsupp.single gpos 1 -
        Finsupp.single gneg 1 : Chromosome) h → h.rank ≤ gε.rank)
    (hYtwo : 2 ≤
      Y.1.1 ⟨2 * q + 5, GeneType.NonPolarized, by omega⟩)
    (hjlo : 2 * s + 1 < j) (hjhi : j ≤ 2 * q + 4) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := by
  have hne : gpos ≠ gneg := by
    intro h
    have := congrArg Gene.type h
    rw [hgpos, hgneg] at this
    contradiction
  let restPair : Chromosome :=
    X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1
  have hrest_zero : Chromosome.prime^[j] restPair = 0 := by
    apply prime_iterate_eq_zero_rank_le.mp
    intro g hg
    have hgpos' : 0 < restPair g :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
    have hle := hgεmax g (by simpa [restPair] using hgpos')
    rw [hgε_rank] at hle
    omega
  have hXdecomp :
      Finsupp.single gpos 1 + Finsupp.single gneg 1 + restPair = X.1.1 :=
    Mix2LambdaSection17.single_pair_add_rest (by omega) (by omega) hne
  have hXsig :
      signature (Chromosome.prime^[j] X.1.1) =
        signature (Chromosome.prime^[j]
          (Finsupp.single gpos 1 + Finsupp.single gneg 1 : Chromosome)) := by
    conv_lhs => rw [← hXdecomp]
    rw [iterate_map_add, map_add, hrest_zero, map_zero, add_zero]
  let gNP : Gene :=
    ⟨2 * q + 5, GeneType.NonPolarized, by omega⟩
  have hYdecomp :
      Finsupp.single gNP 1 + Finsupp.single gNP 1 +
          (Y.1.1 - Finsupp.single gNP 1 - Finsupp.single gNP 1) = Y.1.1 :=
    Mix2LambdaSection17.double_single_add_rest hYtwo
  have hYge :
      signature (Chromosome.prime^[j]
          (Finsupp.single gNP 1 + Finsupp.single gNP 1 : Chromosome)) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    conv_rhs => rw [← hYdecomp, iterate_map_add, map_add]
    exact le_add_of_nonneg_right (signature_nonneg _)
  have hpos_single :
      Gene.ofRank (2 * q + 4) GeneType.Positive =
        (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hpos_rank, hgpos] at h
  have hneg_single :
      Gene.ofRank (2 * q + 4) GeneType.Negative =
        (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rwa [hneg_rank, hgneg] at h
  have hnp_single :
      Gene.ofRank (2 * q + 5) GeneType.NonPolarized =
        (Finsupp.single gNP 1 : Chromosome) := by
    exact Gene.ofRank_eq_gene (g := gNP)
  have hdiag :
      signature (Chromosome.prime^[j]
          (Finsupp.single gNP 1 + Finsupp.single gNP 1 : Chromosome)) =
        ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j]
            (Finsupp.single gpos 1 + Finsupp.single gneg 1 : Chromosome)) := by
    conv_lhs => rw [← hnp_single]
    conv_rhs => rw [← hpos_single, ← hneg_single]
    simp only [iterate_map_add, prime_iterate_ofRank, map_add]
    have hsucc : 2 * q + 5 - j = (2 * q + 4 - j) + 1 := by omega
    rw [hsucc, signature_ofRank_nonPolarized]
    have hpair := signature_sum_ofRank_neg_eq_rank
      (k := 2 * q + 4 - j) (ε := GeneType.Positive)
    rw [GeneType.neg_positive] at hpair
    rw [hpair]
    ext <;> simp [add_halves] <;> ring
  calc
    ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) =
        ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j]
          (Finsupp.single gpos 1 + Finsupp.single gneg 1 : Chromosome)) := by
            rw [hXsig]
    _ = signature (Chromosome.prime^[j]
          (Finsupp.single gNP 1 + Finsupp.single gNP 1 : Chromosome)) := hdiag.symm
    _ ≤ signature (Chromosome.prime^[j] Y.1.1) := hYge

private lemma signature_prime_iterate_snd_eq_zero_of_rank_le_no_negative
    {W : Chromosome} {i : ℕ}
    (hpol : ∀ g : Gene, 0 < W g → g.type ≠ GeneType.NonPolarized)
    (hrank : ∀ g : Gene, 0 < W g → g.rank ≤ i + 1)
    (hno : W ⟨i + 1, GeneType.Negative, by omega⟩ = 0) :
    (signature (Chromosome.prime^[i] W)).2 = 0 := by
  rw [signature_snd, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro g hg
  by_cases hcoeff : (Chromosome.prime^[i] W) g = 0
  · simp [hcoeff]
  · have hcoeff_pos : 0 < (Chromosome.prime^[i] W) g :=
      Nat.pos_of_ne_zero hcoeff
    let g0 : Gene :=
      ⟨g.rank + i, g.type, Nat.le_add_right_of_le g.rank_pos⟩
    have hg0_pos : 0 < W g0 := by
      simpa [g0, prime_iterate_coeff] using hcoeff_pos
    have hg_rank : g.rank = 1 := by
      have hle := hrank g0 hg0_pos
      dsimp [g0] at hle
      have hpositive := g.rank_pos
      omega
    have hg_pol : g.type ≠ GeneType.NonPolarized := hpol g0 hg0_pos
    have hg_not_neg : g.type ≠ GeneType.Negative := by
      intro hneg
      have hg0_eq : g0 = ⟨i + 1, GeneType.Negative, by omega⟩ := by
        ext
        · dsimp [g0]
          omega
        · exact hneg
      have : 0 < W ⟨i + 1, GeneType.Negative, by omega⟩ := by
        simpa [hg0_eq] using hg0_pos
      rw [hno] at this
      omega
    have hg_pos : g.type = GeneType.Positive := by
      cases htype : g.type
      · exact False.elim (hg_pol htype)
      · rfl
      · exact False.elim (hg_not_neg htype)
    simp [Gene.signature, hg_rank, hg_pos]

private lemma signature_prime_iterate_fst_eq_zero_of_rank_le_no_positive
    {W : Chromosome} {i : ℕ}
    (hpol : ∀ g : Gene, 0 < W g → g.type ≠ GeneType.NonPolarized)
    (hrank : ∀ g : Gene, 0 < W g → g.rank ≤ i + 1)
    (hno : W ⟨i + 1, GeneType.Positive, by omega⟩ = 0) :
    (signature (Chromosome.prime^[i] W)).1 = 0 := by
  rw [signature_fst, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro g hg
  by_cases hcoeff : (Chromosome.prime^[i] W) g = 0
  · simp [hcoeff]
  · have hcoeff_pos : 0 < (Chromosome.prime^[i] W) g :=
      Nat.pos_of_ne_zero hcoeff
    let g0 : Gene :=
      ⟨g.rank + i, g.type, Nat.le_add_right_of_le g.rank_pos⟩
    have hg0_pos : 0 < W g0 := by
      simpa [g0, prime_iterate_coeff] using hcoeff_pos
    have hg_rank : g.rank = 1 := by
      have hle := hrank g0 hg0_pos
      dsimp [g0] at hle
      have hpositive := g.rank_pos
      omega
    have hg_pol : g.type ≠ GeneType.NonPolarized := hpol g0 hg0_pos
    have hg_not_pos : g.type ≠ GeneType.Positive := by
      intro hpos
      have hg0_eq : g0 = ⟨i + 1, GeneType.Positive, by omega⟩ := by
        ext
        · dsimp [g0]
          omega
        · exact hpos
      have : 0 < W ⟨i + 1, GeneType.Positive, by omega⟩ := by
        simpa [hg0_eq] using hg0_pos
      rw [hno] at this
      omega
    have hg_neg : g.type = GeneType.Negative := by
      cases htype : g.type
      · exact False.elim (hg_pol htype)
      · exact False.elim (hg_not_pos htype)
      · rfl
    simp [Gene.signature, hg_rank, hg_neg]

private lemma pair_high_zero_pair_diagonal_le
    {m q j : ℕ} (Y : nMixPi2Lambda (m + 2))
    (gpos gneg : Gene)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos_rank : gpos.rank = 2 * q + 4)
    (hneg_rank : gneg.rank = 2 * q + 4)
    (hYtwo : 2 ≤
      Y.1.1 ⟨2 * q + 5, GeneType.NonPolarized, by omega⟩)
    (hj : j ≤ 2 * q + 4) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[j]
          (Finsupp.single gpos 1 + Finsupp.single gneg 1 : Chromosome)) ≤
      signature (Chromosome.prime^[j] Y.1.1) := by
  let gNP : Gene :=
    ⟨2 * q + 5, GeneType.NonPolarized, by omega⟩
  have hYdecomp :
      Finsupp.single gNP 1 + Finsupp.single gNP 1 +
          (Y.1.1 - Finsupp.single gNP 1 - Finsupp.single gNP 1) = Y.1.1 :=
    Mix2LambdaSection17.double_single_add_rest hYtwo
  have hYge :
      signature (Chromosome.prime^[j]
          (Finsupp.single gNP 1 + Finsupp.single gNP 1 : Chromosome)) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    conv_rhs => rw [← hYdecomp, iterate_map_add, map_add]
    exact le_add_of_nonneg_right (signature_nonneg _)
  have hpos_single :
      Gene.ofRank (2 * q + 4) GeneType.Positive =
        (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hpos_rank, hgpos] at h
  have hneg_single :
      Gene.ofRank (2 * q + 4) GeneType.Negative =
        (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rwa [hneg_rank, hgneg] at h
  have hnp_single :
      Gene.ofRank (2 * q + 5) GeneType.NonPolarized =
        (Finsupp.single gNP 1 : Chromosome) :=
    Gene.ofRank_eq_gene (g := gNP)
  have hdiag :
      signature (Chromosome.prime^[j]
          (Finsupp.single gNP 1 + Finsupp.single gNP 1 : Chromosome)) =
        ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j]
            (Finsupp.single gpos 1 + Finsupp.single gneg 1 : Chromosome)) := by
    conv_lhs => rw [← hnp_single]
    conv_rhs => rw [← hpos_single, ← hneg_single]
    simp only [iterate_map_add, prime_iterate_ofRank, map_add]
    have hsucc : 2 * q + 5 - j = (2 * q + 4 - j) + 1 := by omega
    rw [hsucc, signature_ofRank_nonPolarized]
    have hpair := signature_sum_ofRank_neg_eq_rank
      (k := 2 * q + 4 - j) (ε := GeneType.Positive)
    rw [GeneType.neg_positive] at hpair
    rw [hpair]
    ext <;> simp [add_halves] <;> ring
  rw [← hdiag]
  exact hYge

private lemma pair_high_zero_pred_gap
    {m q s : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1) (hXpol : X.1.1.IsPolarized)
    (gpos gneg gε : Gene)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1)
    (hpos_rank : gpos.rank = 2 * q + 4)
    (hgεX : 0 < X.1.1 gε)
    (hne_ε_pos : gε ≠ gpos) (hne_ε_neg : gε ≠ gneg)
    (hgεmax : ∀ h : Gene,
      0 < (X.1.1 - Finsupp.single gpos 1 -
        Finsupp.single gneg 1 : Chromosome) h → h.rank ≤ gε.rank)
    (hgεpol : gε.type ≠ GeneType.NonPolarized)
    (hgε_rank : gε.rank = 2 * s + 2) (hsle : s ≤ q + 1)
    (hmin : ∀ (p n : Gene), p.rank = n.rank →
      p.type = GeneType.Positive → n.type = GeneType.Negative →
      0 < X.1.1 p → 0 < X.1.1 n → gpos.rank ≤ p.rank)
    (hYtwo : 2 ≤
      Y.1.1 ⟨2 * q + 5, GeneType.NonPolarized, by omega⟩) :
    signature (Gene.ofRank 1 (-gε.type)) +
        signature (Chromosome.prime^[2 * s + 1] X.1.1) ≤
      signature (Chromosome.prime^[2 * s + 1] Y.1.1) := by
  have hne_pos_neg : gpos ≠ gneg := by
    intro h
    have := congrArg Gene.type h
    rw [hgpos, hgneg] at this
    contradiction
  have hneg_rank : gneg.rank = 2 * q + 4 := by omega
  have hgε_lt : gε.rank < 2 * q + 4 := by
    have hle : gε.rank ≤ 2 * q + 4 := by omega
    refine lt_of_le_of_ne hle ?_
    intro heq
    cases htype : gε.type with
    | NonPolarized => exact hgεpol htype
    | Positive =>
        apply hne_ε_pos
        apply Gene.ext (heq.trans hpos_rank.symm)
        exact htype.trans hgpos.symm
    | Negative =>
        apply hne_ε_neg
        apply Gene.ext (heq.trans hneg_rank.symm)
        simpa [htype] using hgneg.symm
  have hsmall : 2 * s + 2 < 2 * q + 4 := by omega
  let restPair : Chromosome :=
    X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1
  have hXdecomp :
      Finsupp.single gpos 1 + Finsupp.single gneg 1 + restPair = X.1.1 :=
    Mix2LambdaSection17.single_pair_add_rest (by omega) (by omega) hne_pos_neg
  have hrest_pol : ∀ g : Gene, 0 < restPair g →
      g.type ≠ GeneType.NonPolarized := by
    intro g hg
    have hXg : 0 < X.1.1 g := by
      rw [← hXdecomp]
      exact lt_of_lt_of_le hg (Nat.le_add_left _ _)
    exact IsPolarized_def'.mp hXpol g
      (Finsupp.mem_support_iff.mpr hXg.ne')
  have hrest_rank : ∀ g : Gene, 0 < restPair g → g.rank ≤ 2 * s + 2 := by
    intro g hg
    have := hgεmax g (by simpa [restPair] using hg)
    rwa [hgε_rank] at this
  have hpairgap := pair_high_zero_pair_diagonal_le Y gpos gneg
    hgpos hgneg hpos_rank hneg_rank hYtwo
    (j := 2 * s + 1) (by omega)
  cases htype : gε.type with
  | NonPolarized => exact False.elim (hgεpol htype)
  | Positive =>
      have hoppX :
          X.1.1 ⟨2 * s + 2, GeneType.Negative, by omega⟩ = 0 := by
        by_contra hne
        have hopp : 0 < X.1.1 ⟨2 * s + 2, GeneType.Negative, by omega⟩ :=
          Nat.pos_of_ne_zero hne
        have hbad := hmin gε ⟨2 * s + 2, GeneType.Negative, by omega⟩
          (by rw [hgε_rank]) htype rfl hgεX hopp
        rw [hpos_rank] at hbad
        omega
      have htop_ne_pos :
          (⟨2 * s + 2, GeneType.Negative, by omega⟩ : Gene) ≠ gpos := by
        intro h
        have := congrArg Gene.rank h
        rw [hpos_rank] at this
        exact (ne_of_lt hsmall) this
      have htop_ne_neg :
          (⟨2 * s + 2, GeneType.Negative, by omega⟩ : Gene) ≠ gneg := by
        intro h
        have := congrArg Gene.rank h
        rw [hneg_rank] at this
        exact (ne_of_lt hsmall) this
      have hrest_no :
          restPair ⟨2 * s + 2, GeneType.Negative, by omega⟩ = 0 := by
        dsimp [restPair]
        simp [hoppX, htop_ne_pos, htop_ne_neg]
      have hrest_snd :
          (signature (Chromosome.prime^[2 * s + 1] restPair)).2 = 0 :=
        signature_prime_iterate_snd_eq_zero_of_rank_le_no_negative
          hrest_pol hrest_rank hrest_no
      have hXsnd :
          (signature (Chromosome.prime^[2 * s + 1] X.1.1)).2 =
            (signature (Chromosome.prime^[2 * s + 1]
              (Finsupp.single gpos 1 + Finsupp.single gneg 1 : Chromosome))).2 := by
        have hsig :
            signature (Chromosome.prime^[2 * s + 1] X.1.1) =
              signature (Chromosome.prime^[2 * s + 1]
                (Finsupp.single gpos 1 + Finsupp.single gneg 1 : Chromosome)) +
              signature (Chromosome.prime^[2 * s + 1] restPair) := by
          conv_lhs => rw [← hXdecomp]
          rw [iterate_map_add, map_add]
        have hsnd := congrArg Prod.snd hsig
        simp only [Prod.snd_add] at hsnd
        linarith
      apply type17_pred_gap_positive (q := s) X Y hXY
      have hy := hpairgap.2
      rw [hXsnd]
      simp only [Prod.snd_add] at hy
      linarith
  | Negative =>
      have hoppX :
          X.1.1 ⟨2 * s + 2, GeneType.Positive, by omega⟩ = 0 := by
        by_contra hne
        have hopp : 0 < X.1.1 ⟨2 * s + 2, GeneType.Positive, by omega⟩ :=
          Nat.pos_of_ne_zero hne
        have hbad := hmin ⟨2 * s + 2, GeneType.Positive, by omega⟩ gε
          (by rw [hgε_rank]) rfl htype hopp hgεX
        rw [hpos_rank] at hbad
        change 2 * q + 4 ≤ 2 * s + 2 at hbad
        omega
      have htop_ne_pos :
          (⟨2 * s + 2, GeneType.Positive, by omega⟩ : Gene) ≠ gpos := by
        intro h
        have := congrArg Gene.rank h
        rw [hpos_rank] at this
        exact (ne_of_lt hsmall) this
      have htop_ne_neg :
          (⟨2 * s + 2, GeneType.Positive, by omega⟩ : Gene) ≠ gneg := by
        intro h
        have := congrArg Gene.rank h
        rw [hneg_rank] at this
        exact (ne_of_lt hsmall) this
      have hrest_no :
          restPair ⟨2 * s + 2, GeneType.Positive, by omega⟩ = 0 := by
        dsimp [restPair]
        simp [hoppX, htop_ne_pos, htop_ne_neg]
      have hrest_fst :
          (signature (Chromosome.prime^[2 * s + 1] restPair)).1 = 0 :=
        signature_prime_iterate_fst_eq_zero_of_rank_le_no_positive
          hrest_pol hrest_rank hrest_no
      have hXfst :
          (signature (Chromosome.prime^[2 * s + 1] X.1.1)).1 =
            (signature (Chromosome.prime^[2 * s + 1]
              (Finsupp.single gpos 1 + Finsupp.single gneg 1 : Chromosome))).1 := by
        have hsig :
            signature (Chromosome.prime^[2 * s + 1] X.1.1) =
              signature (Chromosome.prime^[2 * s + 1]
                (Finsupp.single gpos 1 + Finsupp.single gneg 1 : Chromosome)) +
              signature (Chromosome.prime^[2 * s + 1] restPair) := by
          conv_lhs => rw [← hXdecomp]
          rw [iterate_map_add, map_add]
        have hfst := congrArg Prod.fst hsig
        simp only [Prod.fst_add] at hfst
        linarith
      apply type17_pred_gap_negative (q := s) X Y hXY
      have hy := hpairgap.1
      rw [hXfst]
      simp only [Prod.fst_add] at hy
      linarith

lemma exists_mutation_le_pair_high_both_single_zero_successor
    {m q : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hpos : X.1.1 gpos = 1) (hneg : X.1.1 gneg = 1)
    (hpos_rank : gpos.rank = 2 * q + 4)
    (hmin : ∀ (p n : Gene), p.rank = n.rank →
      p.type = GeneType.Positive → n.type = GeneType.Negative →
      0 < X.1.1 p → 0 < X.1.1 n → gpos.rank ≤ p.rank)
    (hYsucc : Chromosome.prime^[2 * q + 5] Y.1.1 = 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨gε, s, hgε_rest, hgεX, hne_ε_pos, hne_ε_neg,
      hgεmax, hgεpol, hgε_rank, hsle⟩ :=
    pair_high_zero_max_remainder_data X Y hXY hcommon h17_1 hXpol
      gpos gneg hrank hgpos hgneg hpos hneg hpos_rank hYsucc
  have hneg_rank : gneg.rank = 2 * q + 4 := by omega
  have hne_pos_neg : gpos ≠ gneg := by
    intro h
    have := congrArg Gene.type h
    rw [hgpos, hgneg] at this
    contradiction
  have hYtwo := pair_high_zero_Y_np_successor_two X Y hXY hcommon h17_1
    gpos gneg hrank hgpos hgneg hpos hneg hpos_rank hYsucc
  apply exists_mutation_le_type11_of_genes_with_diagonal_gap
    (ε := gε.type) hgεpol hsle X Y hXY gε gpos gneg rfl hgpos hgneg
      hgε_rank (by omega) hrank (by omega) (by omega) (by omega)
      hne_ε_pos hne_ε_neg hne_pos_neg
  · exact pair_high_zero_pred_gap X Y hXY hXpol gpos gneg gε hrank
      hgpos hgneg hpos hneg hpos_rank hgεX hne_ε_pos hne_ε_neg
      hgεmax hgεpol hgε_rank hsle hmin hYtwo
  · intro j hjlo hjhi
    exact pair_high_zero_mid_gap X Y gpos gneg gε hgpos hgneg hpos hneg
      hpos_rank hneg_rank hgε_rank hgεmax hYtwo hjlo (by omega)

end MixPi2Lambda
