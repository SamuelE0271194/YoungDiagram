import YoungDiagram.Theorem6.Mix2LambdaPi.Type9

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

private lemma type13_diagonal_signature_eq_before
    {p j : ℕ} (hj : j < 2 * p + 1) :
    signature (Chromosome.prime^[j] (Y13 (le_refl p)).1) =
      signature (Chromosome.prime^[j] (X13 (le_refl p)).1) := by
  have h1 : j ≤ 2 * p := by omega
  have h2 : j ≤ 2 * p + 1 := by omega
  have h3 : j ≤ 2 * p + 2 := by omega
  simp only [X13_eq, Y13_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have hpair :
      signature (Gene.ofRank (2 * p + 1 - j) .Positive) +
        signature (Gene.ofRank (2 * p + 1 - j) .Negative) =
          (((2 * p + 1 - j : ℕ) : ℚ), ((2 * p + 1 - j : ℕ) : ℚ)) := by
    have h :=
      signature_sum_ofRank_neg_eq_rank
        (k := 2 * p + 1 - j) (ε := GeneType.Positive)
    rwa [GeneType.neg_positive] at h
  have hnp (a : ℕ) :
      signature (Gene.ofRank a .NonPolarized) +
        signature (Gene.ofRank a .NonPolarized) = ((a : ℚ), (a : ℚ)) := by
    rw [signature_ofRank_nonPolarized]
    ext <;> simp
  rw [show
      signature (Gene.ofRank (2 * p + 1 - j) .Positive) +
            signature (Gene.ofRank (2 * p + 1 - j) .Negative) +
          signature (Gene.ofRank (2 * p + 1 - j) .Positive) +
        signature (Gene.ofRank (2 * p + 1 - j) .Negative) =
      (signature (Gene.ofRank (2 * p + 1 - j) .Positive) +
        signature (Gene.ofRank (2 * p + 1 - j) .Negative)) +
      (signature (Gene.ofRank (2 * p + 1 - j) .Positive) +
        signature (Gene.ofRank (2 * p + 1 - j) .Negative)) by abel,
    hpair,
    show
      signature (Gene.ofRank (2 * p - j) .NonPolarized) +
            signature (Gene.ofRank (2 * p - j) .NonPolarized) +
          signature (Gene.ofRank (2 * p + 2 - j) .NonPolarized) +
        signature (Gene.ofRank (2 * p + 2 - j) .NonPolarized) =
      (signature (Gene.ofRank (2 * p - j) .NonPolarized) +
        signature (Gene.ofRank (2 * p - j) .NonPolarized)) +
      (signature (Gene.ofRank (2 * p + 2 - j) .NonPolarized) +
        signature (Gene.ofRank (2 * p + 2 - j) .NonPolarized)) by abel,
    hnp, hnp]
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  rw [Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_sub h3]
  constructor <;> push_cast <;> first | rfl | ring

private lemma type13_diagonal_signature_mid {p : ℕ} :
    signature (Chromosome.prime^[2 * p + 1] (Y13 (le_refl p)).1) =
      signature (Chromosome.prime^[2 * p + 1] (X13 (le_refl p)).1) +
        ((1 : ℚ), (1 : ℚ)) := by
  simp only [X13_eq, Y13_eq, iterate_map_add, prime_iterate_ofRank]
  have h0 : 2 * p - (2 * p + 1) = 0 := by omega
  have h2 : 2 * p + 2 - (2 * p + 1) = 1 := by omega
  simp [h0, h2, Gene.ofRank_zero, signature_ofRank_nonPolarized]
  norm_num

private lemma type13_diagonal_signature_eq_after
    {p j : ℕ} (hj : 2 * p + 1 < j) :
    signature (Chromosome.prime^[j] (Y13 (le_refl p)).1) =
      signature (Chromosome.prime^[j] (X13 (le_refl p)).1) := by
  simp only [X13_eq, Y13_eq, iterate_map_add, prime_iterate_ofRank]
  have h0 : 2 * p - j = 0 := by omega
  have h1 : 2 * p + 1 - j = 0 := by omega
  have h2 : 2 * p + 2 - j = 0 := by omega
  simp [h0, h1, h2, Gene.ofRank_zero]

lemma exists_mutation_le_type13_diagonal
    {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (p : ℕ) (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgrank : gpos.rank = 2 * p + 1)
    (hrank : gpos.rank = gneg.rank)
    (hXpos2 : 2 ≤ X.1.1 gpos) (hXneg2 : 2 ≤ X.1.1 gneg) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : gpos ≠ gneg := by
    intro h
    have := congrArg Gene.type h
    rw [hgpos, hgneg] at this
    contradiction
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gpos 1 - Finsupp.single gpos 1 -
      Finsupp.single gneg 1 - Finsupp.single gneg 1
  have hoddpos : Odd gpos.rank := by rw [hgrank]; exact ⟨p, rfl⟩
  have hoddneg : Odd gneg.rank := hrank ▸ hoddpos
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi
        (sub_single_one_mem_Mix_2Lambda_Pi
          (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hoddpos) hoddpos)
        hoddneg) hoddneg
  let rest : Mix (2 • Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgpos_eq :
      Gene.ofRank (2 * p + 1) .Positive =
        (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hgrank, hgpos] at h
  have hgneg_eq :
      Gene.ofRank (2 * p + 1) .Negative =
        (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rwa [hgneg, ← hrank, hgrank] at h
  have hX13val :
      (X13 (le_refl p)).1 =
        Finsupp.single gpos 1 + Finsupp.single gpos 1 +
          Finsupp.single gneg 1 + Finsupp.single gneg 1 := by
    rw [X13_eq, hgpos_eq, hgneg_eq]
    abel
  have hXeq : (X13 (le_refl p)).1 + restval = X.1.1 := by
    rw [hX13val]
    exact Mix2LambdaSection17.double_pair_add_rest hXpos2 hXneg2 hne
  have hY_no_gene : ∀ g : Gene, g.rank = 2 * p + 1 → Y.1.1 g = 0 := by
    intro g hgr
    by_contra hzero
    have hgY : 0 < Y.1.1 g := Nat.pos_of_ne_zero hzero
    have hpol : g.type ≠ .NonPolarized := by
      have hgodd : Odd g.rank := by rw [hgr]; exact ⟨p, rfl⟩
      have : 0 < Y.1.1.oddPart g := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hgodd]
        exact hgY
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) g
        (Finsupp.mem_support_iff.mpr this.ne')
    cases ht : g.type with
    | NonPolarized => exact hpol ht
    | Positive =>
        have heq : g = gpos :=
          Gene.ext (hgr.trans hgrank.symm) (ht.trans hgpos.symm)
        have hle := hcommon gpos (by omega)
        rw [heq] at hgY
        omega
    | Negative =>
        have heq : g = gneg :=
          Gene.ext (hgr.trans hgrank.symm |>.trans hrank)
            (ht.trans hgneg.symm)
        have hle := hcommon gneg (by omega)
        rw [heq] at hgY
        omega
  have hYr_pred : Chromosome.prime^[2 * p] Y.1.1 ≠ 0 := by
    intro hzero
    have hdom := le_iff_dominates.mp hXY.le (2 * p)
    have hsource :
        ((2 : ℚ), (2 : ℚ)) ≤
          signature (Chromosome.prime^[2 * p] X.1.1) := by
      have hdecomp :
          signature (Chromosome.prime^[2 * p] X.1.1) =
            signature (Chromosome.prime^[2 * p] (X13 (le_refl p)).1) +
              signature (Chromosome.prime^[2 * p] restval) := by
        conv_lhs => rw [← hXeq]
        rw [iterate_map_add, map_add]
      have hsrc :
          signature (Chromosome.prime^[2 * p] (X13 (le_refl p)).1) =
            ((2 : ℚ), (2 : ℚ)) := by
        simp only [X13_eq, iterate_map_add, prime_iterate_ofRank, map_add]
        have hone : 2 * p + 1 - 2 * p = 1 := by omega
        rw [hone]
        simp [signature_ofRank_one_positive, signature_ofRank_one_negative]
        norm_num
      rw [hdecomp, hsrc]
      exact le_add_of_nonneg_right (signature_nonneg _)
    rw [hzero, map_zero] at hdom
    exact (not_le_of_gt (show (0 : ℚ) < 2 by norm_num))
      (hsource.1.trans hdom.1)
  have hYr : Chromosome.prime^[2 * p + 1] Y.1.1 ≠ 0 :=
    Mix2LambdaSection17.prime_iterate_ne_zero_of_no_gene (by omega)
      hY_no_gene (by simpa only [show 2 * p + 1 - 1 = 2 * p by omega]
        using hYr_pred)
  have hle_r := le_iff_dominates.mp hXY.le (2 * p + 1)
  have hne_r :
      signature (Chromosome.prime^[2 * p + 1] X.1.1) ≠
        signature (Chromosome.prime^[2 * p + 1] Y.1.1) := by
    intro heq
    have hrank_lt := h17_1 (2 * p + 1) (by omega) hYr
    have := congr_arg (fun q : ℚ × ℚ => q.1 + q.2) heq
    simp only [signature_sum_eq_rank] at this
    exact (ne_of_lt hrank_lt) (by exact_mod_cast this)
  have hXr_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 (2 * p + 1)
  have hYr_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 (2 * p + 1)
  have hodd : ¬ Even (2 * p + 1) := Nat.not_even_iff_odd.mpr ⟨p, rfl⟩
  rw [if_neg hodd] at hXr_mem hYr_mem
  have hgap :=
    Mix2LambdaSection17.one_pair_add_le_of_lt_Mix_Pi_2Lambda
      hXr_mem hYr_mem hle_r hne_r
  refine ⟨⟨(Y13 (le_refl p)).1 + restval,
      add_mem (Y13 (le_refl p)).2 rest_mem⟩, ?_, ?_⟩
  · exact (Subtype.ext hXeq :
      (X13 (le_refl p) : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
        Step.mk (X13 (le_refl p)) (Y13 (le_refl p)) rest
          (Primitive.type13 (le_refl p))
  · change (Y13 (le_refl p)).1 + restval ≤ Y.1.1
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp :
        signature (Chromosome.prime^[j] X.1.1) =
          signature (Chromosome.prime^[j] (X13 (le_refl p)).1) +
            signature (Chromosome.prime^[j] restval) := by
      conv_lhs => rw [← hXeq]
      rw [iterate_map_add, map_add]
    rcases lt_trichotomy j (2 * p + 1) with hj | rfl | hj
    · rw [type13_diagonal_signature_eq_before hj, ← hdecomp]
      exact le_iff_dominates.mp hXY.le j
    · rw [type13_diagonal_signature_mid]
      have heq :
          (signature (Chromosome.prime^[2 * p + 1] (X13 (le_refl p)).1) +
              ((1 : ℚ), (1 : ℚ))) +
              signature (Chromosome.prime^[2 * p + 1] restval) =
            ((1 : ℚ), (1 : ℚ)) +
              signature (Chromosome.prime^[2 * p + 1] X.1.1) := by
        rw [hdecomp]
        abel
      rw [heq]
      exact hgap
    · rw [type13_diagonal_signature_eq_after hj, ← hdecomp]
      exact le_iff_dominates.mp hXY.le j

lemma exists_mutation_le_of_double_pair
    {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hXpos2 : 2 ≤ X.1.1 gpos) (hXneg2 : 2 ≤ X.1.1 gneg) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hodd : Odd gpos.rank := by
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    have hgeven : 0 < X.1.1.evenPart gpos := by
      rw [evenPart_eq, Finsupp.filter_apply, if_pos heven]
      omega
    have hNP :=
      Mix2LambdaSection17.type_eq_nonpolarized_of_mem_twoLambda X.1.2.1 hgeven
    rw [hgpos] at hNP
    contradiction
  obtain ⟨p, hgrank⟩ := hodd
  exact exists_mutation_le_type13_diagonal X Y hXY hcommon h17_1 p gpos gneg
    hgpos hgneg hgrank hrank hXpos2 hXneg2

end Mix2LambdaPi
