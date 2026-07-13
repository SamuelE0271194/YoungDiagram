import YoungDiagram.Theorem6.MixPi2Lambda.Case34PairDouble

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

private lemma signature_prime_iterate_eq_components_of_mem_twoLambda
    {W : Chromosome} (hW : W ∈ 2 • Lambda) (k : ℕ) :
    (signature (Chromosome.prime^[k] W)).1 =
      (signature (Chromosome.prime^[k] W)).2 := by
  obtain ⟨W0, hW0, hW0eq⟩ :=
    (AddSubmonoid.mem_smul_pointwise_iff_exists W 2 Lambda).mp hW
  change 2 • W0 = W at hW0eq
  have hW0k : Chromosome.prime^[k] W0 ∈ Lambda :=
    prime_mem_Lambda_iterate hW0
  rw [← hW0eq, iterate_map_nsmul, map_nsmul]
  change 2 * (signature (Chromosome.prime^[k] W0)).1 =
    2 * (signature (Chromosome.prime^[k] W0)).2
  rw [signature_fst, signature_snd]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  have hgNP : g.type = GeneType.NonPolarized :=
    IsNonPolarized_def'.mp (mem_Lambda_iff.mp hW0k) g hg
  have hsig : g.signature.1 = g.signature.2 := by
    rw [Gene.signature_of_nonPolarized hgNP]
  simp [hsig]

private lemma pair_rank_two_positive_double_type11_gaps
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hgpos2 : gpos.rank = 2) (hgneg2 : gneg.rank = 2)
    (hpos : 2 ≤ X.1.1 gpos) (hneg : X.1.1 gneg = 1)
    (hXeq : X.1.1 =
      Finsupp.single gpos (X.1.1 gpos) +
        Finsupp.single gneg (X.1.1 gneg))
    (hY2L : Y.1.1 ∈ 2 • Lambda) :
    signature (Gene.ofRank 1 GeneType.Negative) +
        signature (Chromosome.prime^[1] X.1.1) ≤
      signature (Chromosome.prime^[1] Y.1.1) ∧
    ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[2] X.1.1) ≤
      signature (Chromosome.prime^[2] Y.1.1) := by
  have hne : gpos ≠ gneg := by
    intro h
    have := congrArg Gene.type h
    rw [hgpos, hgneg] at this
    contradiction
  have hX1 : signature (Chromosome.prime^[1] X.1.1) =
      (((X.1.1 gpos : ℕ) : ℚ), (1 : ℚ)) := by
    conv_lhs => rw [hXeq, hneg, iterate_map_add, map_add]
    simp only [Function.iterate_one, prime_single, map_nsmul]
    rw [hgpos2, hgneg2, hgpos, hgneg]
    simp [signature_ofRank_one_positive, signature_ofRank_one_negative]
  have hY1eq :=
    signature_prime_iterate_eq_components_of_mem_twoLambda hY2L 1
  have hdom1 := le_iff_dominates.mp hXY.le 1
  have hpred : signature (Gene.ofRank 1 GeneType.Negative) +
        signature (Chromosome.prime^[1] X.1.1) ≤
      signature (Chromosome.prime^[1] Y.1.1) := by
    rw [hX1, signature_ofRank_one_negative]
    norm_num
    constructor
    · have hf := hdom1.1
      rw [hX1] at hf
      simpa [Function.iterate_one] using hf
    · have heq : (signature (Chromosome.prime Y.1.1)).1 =
          (signature (Chromosome.prime Y.1.1)).2 := by
        simpa [Function.iterate_one] using hY1eq
      rw [← heq]
      have hcast : (2 : ℚ) ≤ (X.1.1 gpos : ℚ) := by exact_mod_cast hpos
      have := hdom1.1
      rw [hX1] at this
      norm_num at this ⊢
      exact hcast.trans (by simpa [Function.iterate_one] using this)
  have hY1 : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
    intro hz
    have hsnd := hdom1.2
    rw [hz, map_zero, hX1] at hsnd
    norm_num at hsnd
  have hY2 : Chromosome.prime^[2] Y.1.1 ≠ 0 := by
    intro hz
    have hrank_le :=
      (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := 2)).2 hz
    have hY1zero : Chromosome.prime^[1] Y.1.1 = 0 := by
      rw [← Chromosome.prime_iterate_eq_zero_rank_le]
      intro h hh
      have hle := hrank_le h hh
      have hhpos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      have hNP := Mix2LambdaSection17.type_eq_nonpolarized_of_mem_twoLambda
        hY2L hhpos
      by_contra hnot
      have hrank2 : h.rank = 2 := by omega
      have heven : Even h.rank := by rw [hrank2]; decide
      have heven_pos : 0 < Y.1.1.evenPart h := by
        rw [evenPart_eq, Finsupp.filter_apply, if_pos heven]
        exact hhpos
      have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.1) h
        (Finsupp.mem_support_iff.mpr heven_pos.ne')
      exact hpol hNP
    exact hY1 hY1zero
  refine ⟨hpred, ?_⟩
  exact type10_mid_gap_even_of_Y_ne X Y h17_1 ⟨1, by omega⟩
    (by omega) hY2

lemma exists_mutation_le_pair_rank_two_positive_double_zero_successor
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hgpos2 : gpos.rank = 2) (hgneg2 : gneg.rank = 2)
    (hpos : 2 ≤ X.1.1 gpos) (hneg : X.1.1 gneg = 1)
    (hY3 : Chromosome.prime^[3] Y.1.1 = 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXpos : 0 < X.1.1 gpos := by omega
  have hXneg : 0 < X.1.1 gneg := by omega
  obtain ⟨hXshape, hY2L, _, _, _⟩ :=
    pair_rank_two_zero_successor_shape X Y hXY hcommon hXpol gpos gneg
      hgpos hgneg hgpos2 hgneg2 hXpos hXneg hY3
  obtain ⟨hgap_pred, hgap_mid⟩ :=
    pair_rank_two_positive_double_type11_gaps X Y hXY h17_1 gpos gneg
      hgpos hgneg hgpos2 hgneg2 hpos hneg hXshape hY2L
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gpos 1 - Finsupp.single gpos 1 -
      Finsupp.single gneg 1
  have heven_pos : Even gpos.rank := by rw [hgpos2]; decide
  have heven_neg : Even gneg.rank := by rw [hgneg2]; decide
  have hrest : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda
        (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 heven_pos) heven_pos)
      heven_neg
  have hpos_single : Gene.ofRank 2 GeneType.Positive =
      (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hgpos2, hgpos] at h
  have hneg_single : Gene.ofRank 2 GeneType.Negative =
      (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rwa [hgneg2, hgneg] at h
  have hX11 : (X11 (le_refl 0)
      (by decide : GeneType.Positive ≠ GeneType.NonPolarized)).1 =
      Finsupp.single gpos 1 + Finsupp.single gpos 1 +
        Finsupp.single gneg 1 := by
    rw [X11_eq, hpos_single, hneg_single]
  have hne : gpos ≠ gneg := by
    intro h
    have := congrArg Gene.type h
    rw [hgpos, hgneg] at this
    contradiction
  have hXdecomp : (X11 (le_refl 0)
      (by decide : GeneType.Positive ≠ GeneType.NonPolarized)).1 +
        restval = X.1.1 := by
    rw [hX11]
    exact Mix2LambdaSection17.double_single_pair_add_rest
      hpos (by omega) hne
  have hZle := type11_target_add_rest_le_of_diagonal_gap
    (by decide : GeneType.Positive ≠ GeneType.NonPolarized) (le_refl 0)
    X Y hXY restval hXdecomp (by simpa using hgap_pred) (by
      intro j hjlo hjhi
      have : j = 2 := by omega
      subst j
      simpa using hgap_mid)
  exact exists_mutation_le_type11_of_decomp
    (by decide : GeneType.Positive ≠ GeneType.NonPolarized) (le_refl 0)
    X Y restval hXdecomp hrest hZle

private lemma pair_rank_two_negative_double_type11_gaps
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hgpos2 : gpos.rank = 2) (hgneg2 : gneg.rank = 2)
    (hpos : X.1.1 gpos = 1) (hneg : 2 ≤ X.1.1 gneg)
    (hXeq : X.1.1 =
      Finsupp.single gpos (X.1.1 gpos) +
        Finsupp.single gneg (X.1.1 gneg))
    (hY2L : Y.1.1 ∈ 2 • Lambda) :
    signature (Gene.ofRank 1 GeneType.Positive) +
        signature (Chromosome.prime^[1] X.1.1) ≤
      signature (Chromosome.prime^[1] Y.1.1) ∧
    ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[2] X.1.1) ≤
      signature (Chromosome.prime^[2] Y.1.1) := by
  have hX1 : signature (Chromosome.prime^[1] X.1.1) =
      ((1 : ℚ), ((X.1.1 gneg : ℕ) : ℚ)) := by
    conv_lhs => rw [hXeq, hpos, iterate_map_add, map_add]
    simp only [Function.iterate_one, prime_single, map_nsmul]
    rw [hgpos2, hgneg2, hgpos, hgneg]
    simp [signature_ofRank_one_positive, signature_ofRank_one_negative]
  have hY1eq :=
    signature_prime_iterate_eq_components_of_mem_twoLambda hY2L 1
  have hdom1 := le_iff_dominates.mp hXY.le 1
  have hpred : signature (Gene.ofRank 1 GeneType.Positive) +
        signature (Chromosome.prime^[1] X.1.1) ≤
      signature (Chromosome.prime^[1] Y.1.1) := by
    rw [hX1, signature_ofRank_one_positive]
    norm_num
    constructor
    · have heq : (signature (Chromosome.prime Y.1.1)).1 =
          (signature (Chromosome.prime Y.1.1)).2 := by
        simpa [Function.iterate_one] using hY1eq
      rw [heq]
      have hcast : (2 : ℚ) ≤ (X.1.1 gneg : ℚ) := by exact_mod_cast hneg
      have := hdom1.2
      rw [hX1] at this
      norm_num at this ⊢
      exact hcast.trans (by simpa [Function.iterate_one] using this)
    · have hs := hdom1.2
      rw [hX1] at hs
      simpa [Function.iterate_one] using hs
  have hY1 : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
    intro hz
    have hfst := hdom1.1
    rw [hz, map_zero, hX1] at hfst
    norm_num at hfst
  have hY2 : Chromosome.prime^[2] Y.1.1 ≠ 0 := by
    intro hz
    have hrank_le :=
      (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := 2)).2 hz
    have hY1zero : Chromosome.prime^[1] Y.1.1 = 0 := by
      rw [← Chromosome.prime_iterate_eq_zero_rank_le]
      intro h hh
      have hle := hrank_le h hh
      have hhpos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      have hNP := Mix2LambdaSection17.type_eq_nonpolarized_of_mem_twoLambda
        hY2L hhpos
      by_contra hnot
      have hrank2 : h.rank = 2 := by omega
      have heven : Even h.rank := by rw [hrank2]; decide
      have heven_pos : 0 < Y.1.1.evenPart h := by
        rw [evenPart_eq, Finsupp.filter_apply, if_pos heven]
        exact hhpos
      have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.1) h
        (Finsupp.mem_support_iff.mpr heven_pos.ne')
      exact hpol hNP
    exact hY1 hY1zero
  refine ⟨hpred, ?_⟩
  exact type10_mid_gap_even_of_Y_ne X Y h17_1 ⟨1, by omega⟩
    (by omega) hY2

lemma exists_mutation_le_pair_rank_two_negative_double_zero_successor
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (gpos gneg : Gene)
    (hgpos : gpos.type = GeneType.Positive)
    (hgneg : gneg.type = GeneType.Negative)
    (hgpos2 : gpos.rank = 2) (hgneg2 : gneg.rank = 2)
    (hpos : X.1.1 gpos = 1) (hneg : 2 ≤ X.1.1 gneg)
    (hY3 : Chromosome.prime^[3] Y.1.1 = 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXpos : 0 < X.1.1 gpos := by omega
  have hXneg : 0 < X.1.1 gneg := by omega
  obtain ⟨hXshape, hY2L, _, _, _⟩ :=
    pair_rank_two_zero_successor_shape X Y hXY hcommon hXpol gpos gneg
      hgpos hgneg hgpos2 hgneg2 hXpos hXneg hY3
  obtain ⟨hgap_pred, hgap_mid⟩ :=
    pair_rank_two_negative_double_type11_gaps X Y hXY h17_1 gpos gneg
      hgpos hgneg hgpos2 hgneg2 hpos hneg hXshape hY2L
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gneg 1 - Finsupp.single gneg 1 -
      Finsupp.single gpos 1
  have heven_pos : Even gpos.rank := by rw [hgpos2]; decide
  have heven_neg : Even gneg.rank := by rw [hgneg2]; decide
  have hrest : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda
        (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 heven_neg) heven_neg)
      heven_pos
  have hpos_single : Gene.ofRank 2 GeneType.Positive =
      (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hgpos2, hgpos] at h
  have hneg_single : Gene.ofRank 2 GeneType.Negative =
      (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rwa [hgneg2, hgneg] at h
  have hX11 : (X11 (le_refl 0)
      (by decide : GeneType.Negative ≠ GeneType.NonPolarized)).1 =
      Finsupp.single gneg 1 + Finsupp.single gneg 1 +
        Finsupp.single gpos 1 := by
    rw [X11_eq, hpos_single, hneg_single]
    abel
  have hne : gneg ≠ gpos := by
    intro h
    have := congrArg Gene.type h
    rw [hgneg, hgpos] at this
    contradiction
  have hXdecomp : (X11 (le_refl 0)
      (by decide : GeneType.Negative ≠ GeneType.NonPolarized)).1 +
        restval = X.1.1 := by
    rw [hX11]
    exact Mix2LambdaSection17.double_single_pair_add_rest
      hneg (by omega) hne
  have hZle := type11_target_add_rest_le_of_diagonal_gap
    (by decide : GeneType.Negative ≠ GeneType.NonPolarized) (le_refl 0)
    X Y hXY restval hXdecomp (by simpa using hgap_pred) (by
      intro j hjlo hjhi
      have : j = 2 := by omega
      subst j
      simpa using hgap_mid)
  exact exists_mutation_le_type11_of_decomp
    (by decide : GeneType.Negative ≠ GeneType.NonPolarized) (le_refl 0)
    X Y restval hXdecomp hrest hZle

end MixPi2Lambda
