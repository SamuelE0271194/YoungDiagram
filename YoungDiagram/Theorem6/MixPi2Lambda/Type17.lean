import YoungDiagram.Theorem6.MixPi2Lambda.Type16

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

private lemma negative_ne_nonPolarized : GeneType.Negative ≠ .NonPolarized := by decide
private lemma positive_ne_nonPolarized : GeneType.Positive ≠ .NonPolarized := by decide

private lemma type17_positive_signature_eq_before
    {q j : ℕ} (hj : j < 2 * q + 1) :
    signature (Chromosome.prime^[j]
        (Y17 (le_refl q) negative_ne_nonPolarized).1) =
      signature (Chromosome.prime^[j]
        (X17 (le_refl q) negative_ne_nonPolarized).1) := by
  simp only [X17_eq, Y17_eq, GeneType.neg_negative, iterate_map_add,
    prime_iterate_ofRank, map_add]
  have h := mutation_type17_sig_eq_aux (n := q) (m := q)
    (ε := GeneType.Negative) ((2 * q - j) / 2) ((2 * q - j) % 2)
  have eq1 :
      2 * ((2 * q - j) / 2) + 2 + (2 * q - j) % 2 =
        2 * q + 2 - j := by omega
  have eq2 :
      2 * (((2 * q - j) / 2) + (q - q)) + 2 +
          (2 * q - j) % 2 =
        2 * q + 2 - j := by omega
  have eq3 :
      2 * ((2 * q - j) / 2) + (2 * q - j) % 2 =
        2 * q - j := by omega
  have eq4 :
      2 * (((2 * q - j) / 2) + (q - q)) + 3 +
          (2 * q - j) % 2 =
        2 * q + 3 - j := by omega
  rw [eq1, eq2, eq3, eq4] at h
  exact h.symm

private lemma type17_positive_signature_at_pred
    {q : ℕ} :
    signature (Chromosome.prime^[2 * q + 1]
        (Y17 (le_refl q) negative_ne_nonPolarized).1) =
      signature (Gene.ofRank 1 .Negative) +
        signature (Chromosome.prime^[2 * q + 1]
          (X17 (le_refl q) negative_ne_nonPolarized).1) := by
  simp only [X17_eq, Y17_eq, GeneType.neg_negative, iterate_map_add,
    prime_iterate_ofRank, map_add]
  have h1 : 2 * q - (2 * q + 1) = 0 := by omega
  have h2 : 2 * q + 3 - (2 * q + 1) = 2 := by omega
  have h3 : 2 * q + 2 - (2 * q + 1) = 1 := by omega
  rw [h1, h2, h3, Gene.ofRank_zero, map_zero, zero_add]
  simp [signature_ofRank_eq₂', signature_ofRank_one_positive,
    signature_ofRank_one_negative]

private lemma type17_positive_signature_at_rank
    {q : ℕ} :
    signature (Chromosome.prime^[2 * q + 2]
        (Y17 (le_refl q) negative_ne_nonPolarized).1) =
      ((1 : ℚ), (1 : ℚ)) := by
  simp only [Y17_eq, GeneType.neg_negative, iterate_map_add,
    prime_iterate_ofRank, map_add]
  have h1 : 2 * q - (2 * q + 2) = 0 := by omega
  have h2 : 2 * q + 3 - (2 * q + 2) = 1 := by omega
  rw [h1, h2, Gene.ofRank_zero, map_zero, zero_add]
  simp [signature_ofRank_nonPolarized]
  norm_num

private lemma type17_positive_source_at_rank
    {q : ℕ} :
    signature (Chromosome.prime^[2 * q + 2]
        (X17 (le_refl q) negative_ne_nonPolarized).1) = 0 := by
  simp [X17_eq, prime_iterate_ofRank]

private lemma type17_positive_signature_eq_after
    {q j : ℕ} (hj : 2 * q + 2 < j) :
    signature (Chromosome.prime^[j]
        (Y17 (le_refl q) negative_ne_nonPolarized).1) =
      signature (Chromosome.prime^[j]
        (X17 (le_refl q) negative_ne_nonPolarized).1) := by
  simp only [X17_eq, Y17_eq, GeneType.neg_negative, iterate_map_add,
    prime_iterate_ofRank, map_add]
  have h1 : 2 * q - j = 0 := by omega
  have h2 : 2 * q + 3 - j = 0 := by omega
  have h3 : 2 * q + 2 - j = 0 := by omega
  simp [h1, h2, h3]

/-- At the predecessor (odd) level `2q+1` of the positive type17 branch, a strict
second-component gap gives exactly the `signature (ofRank 1 Negative)` gap.
(L4 parity: the pred level is odd, so we replicate the `type16_succ_gap`
machinery directly rather than delegating, since the odd levels do not align
under a single `p`-instantiation.) -/
lemma type17_pred_gap_positive
    {N q : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hsnd :
      (signature (Chromosome.prime^[2 * q + 1] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q + 1] Y.1.1)).2) :
    signature (Gene.ofRank 1 .Negative) +
        signature (Chromosome.prime^[2 * q + 1] X.1.1) ≤
      signature (Chromosome.prime^[2 * q + 1] Y.1.1) := by
  have hXk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 (2 * q + 1)
  have hYk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 (2 * q + 1)
  have hodd : ¬ Even (2 * q + 1) := Nat.not_even_iff_odd.mpr ⟨q, by ring⟩
  rw [if_neg hodd] at hXk_mem hYk_mem
  have hsnd_gap :=
    Mix2LambdaSection17.add_one_le_snd_of_lt_Mix_2Lambda_Pi
      hXk_mem hYk_mem hsnd
  have hle := le_iff_dominates.mp hXY.le (2 * q + 1)
  rw [signature_ofRank_one_negative]
  exact ⟨by simpa using hle.1, by simpa [Prod.snd_add, add_comm] using hsnd_gap⟩

/-- The type17 diagonal branch
`2g⁺(2q+2)+g⁻(2q+2) → g⁻(2q)+2NP(2q+3)`, assuming the two sigma gaps
where the target exceeds the source. -/
lemma exists_mutation_le_type17_diagonal_positive
    {N q : ℕ}
    (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgpos_rank : gpos.rank = 2 * q + 2)
    (hrank : gpos.rank = gneg.rank)
    (hpos : 2 ≤ X.1.1 gpos) (hneg : 1 ≤ X.1.1 gneg)
    (hgap_pred :
      signature (Gene.ofRank 1 .Negative) +
          signature (Chromosome.prime^[2 * q + 1] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 1] Y.1.1))
    (hgap_rank :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 2] Y.1.1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : gpos ≠ gneg := by
    intro h
    have ht := congrArg Gene.type h
    rw [hgpos, hgneg] at ht
    simp at ht
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gpos 1 - Finsupp.single gpos 1 -
      Finsupp.single gneg 1
  have hevenpos : Even gpos.rank := by
    rw [hgpos_rank]
    exact ⟨q + 1, by ring⟩
  have hevenneg : Even gneg.rank := hrank ▸ hevenpos
  have rest_mem : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda
        (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 hevenpos) hevenpos)
      hevenneg
  let rest : Mix (Pi, 2 • Lambda) := ⟨restval, rest_mem⟩
  have hgneg_eq :
      Gene.ofRank (2 * q + 2) .Negative =
        (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rwa [hgneg, ← hrank, hgpos_rank] at h
  have hgpos_eq :
      Gene.ofRank (2 * q + 2) .Positive =
        (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hgpos_rank, hgpos] at h
  have hX17val :
      (X17 (le_refl q) negative_ne_nonPolarized).1 =
        Finsupp.single gneg 1 + Finsupp.single gpos 1 +
          Finsupp.single gpos 1 := by
    rw [X17_eq, GeneType.neg_negative, hgneg_eq, hgpos_eq]
  have hXeq :
      (X17 (le_refl q) negative_ne_nonPolarized).1 +
          restval = X.1.1 := by
    rw [hX17val]
    exact Mix2LambdaSection17.single_double_pair_add_rest
      hpos hneg hne
  refine ⟨⟨(Y17 (le_refl q) negative_ne_nonPolarized).1 +
      restval, add_mem
        (Y17 (le_refl q) negative_ne_nonPolarized).2
        rest_mem⟩, ?_, ?_⟩
  · exact (Subtype.ext hXeq :
      (X17 (le_refl q) negative_ne_nonPolarized :
          Mix (Pi, 2 • Lambda)) + rest = X.1) ▸
        Step.mk
          (X17 (le_refl q) negative_ne_nonPolarized)
          (Y17 (le_refl q) negative_ne_nonPolarized)
          rest
          (Primitive.type17 GeneType.Negative (by decide) (le_refl q))
  · change (Y17 (le_refl q) negative_ne_nonPolarized).1 +
        restval ≤ Y.1.1
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp :
        signature (Chromosome.prime^[j] X.1.1) =
          signature (Chromosome.prime^[j]
            (X17 (le_refl q) negative_ne_nonPolarized).1) +
            signature (Chromosome.prime^[j] restval) := by
      conv_lhs => rw [← hXeq]
      rw [iterate_map_add, map_add]
    by_cases hj_before : j < 2 * q + 1
    · rw [type17_positive_signature_eq_before hj_before, ← hdecomp]
      exact le_iff_dominates.mp hXY.le j
    · by_cases hj_pred : j = 2 * q + 1
      · subst j
        rw [type17_positive_signature_at_pred]
        calc
          signature (Gene.ofRank 1 GeneType.Negative) +
                signature (Chromosome.prime^[2 * q + 1]
                  (X17 (le_refl q) negative_ne_nonPolarized).1) +
              signature (Chromosome.prime^[2 * q + 1] restval)
              = signature (Gene.ofRank 1 GeneType.Negative) +
                (signature (Chromosome.prime^[2 * q + 1]
                    (X17 (le_refl q) negative_ne_nonPolarized).1) +
                  signature (Chromosome.prime^[2 * q + 1] restval)) := by abel
          _ = signature (Gene.ofRank 1 GeneType.Negative) +
                signature (Chromosome.prime^[2 * q + 1] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[2 * q + 1] Y.1.1) := hgap_pred
      · by_cases hj_rank : j = 2 * q + 2
        · subst j
          rw [type17_positive_signature_at_rank]
          rw [type17_positive_source_at_rank, zero_add] at hdecomp
          rw [← hdecomp]
          exact hgap_rank
        · have hj_after : 2 * q + 2 < j := by omega
          rw [type17_positive_signature_eq_after hj_after, ← hdecomp]
          exact le_iff_dominates.mp hXY.le j

private lemma type17_negative_signature_eq_before
    {q j : ℕ} (hj : j < 2 * q + 1) :
    signature (Chromosome.prime^[j]
        (Y17 (le_refl q) positive_ne_nonPolarized).1) =
      signature (Chromosome.prime^[j]
        (X17 (le_refl q) positive_ne_nonPolarized).1) := by
  simp only [X17_eq, Y17_eq, GeneType.neg_positive, iterate_map_add,
    prime_iterate_ofRank, map_add]
  have h := mutation_type17_sig_eq_aux (n := q) (m := q)
    (ε := GeneType.Positive) ((2 * q - j) / 2) ((2 * q - j) % 2)
  have eq1 :
      2 * ((2 * q - j) / 2) + 2 + (2 * q - j) % 2 =
        2 * q + 2 - j := by omega
  have eq2 :
      2 * (((2 * q - j) / 2) + (q - q)) + 2 +
          (2 * q - j) % 2 =
        2 * q + 2 - j := by omega
  have eq3 :
      2 * ((2 * q - j) / 2) + (2 * q - j) % 2 =
        2 * q - j := by omega
  have eq4 :
      2 * (((2 * q - j) / 2) + (q - q)) + 3 +
          (2 * q - j) % 2 =
        2 * q + 3 - j := by omega
  rw [eq1, eq2, eq3, eq4] at h
  exact h.symm

private lemma type17_negative_signature_at_pred
    {q : ℕ} :
    signature (Chromosome.prime^[2 * q + 1]
        (Y17 (le_refl q) positive_ne_nonPolarized).1) =
      signature (Gene.ofRank 1 .Positive) +
        signature (Chromosome.prime^[2 * q + 1]
          (X17 (le_refl q) positive_ne_nonPolarized).1) := by
  simp only [X17_eq, Y17_eq, GeneType.neg_positive, iterate_map_add,
    prime_iterate_ofRank, map_add]
  have h1 : 2 * q - (2 * q + 1) = 0 := by omega
  have h2 : 2 * q + 3 - (2 * q + 1) = 2 := by omega
  have h3 : 2 * q + 2 - (2 * q + 1) = 1 := by omega
  rw [h1, h2, h3, Gene.ofRank_zero, map_zero, zero_add]
  simp [signature_ofRank_eq₂', signature_ofRank_one_positive,
    signature_ofRank_one_negative]

private lemma type17_negative_signature_at_rank
    {q : ℕ} :
    signature (Chromosome.prime^[2 * q + 2]
        (Y17 (le_refl q) positive_ne_nonPolarized).1) =
      ((1 : ℚ), (1 : ℚ)) := by
  simp only [Y17_eq, GeneType.neg_positive, iterate_map_add,
    prime_iterate_ofRank, map_add]
  have h1 : 2 * q - (2 * q + 2) = 0 := by omega
  have h2 : 2 * q + 3 - (2 * q + 2) = 1 := by omega
  rw [h1, h2, Gene.ofRank_zero, map_zero, zero_add]
  simp [signature_ofRank_nonPolarized]
  norm_num

private lemma type17_negative_source_at_rank
    {q : ℕ} :
    signature (Chromosome.prime^[2 * q + 2]
        (X17 (le_refl q) positive_ne_nonPolarized).1) = 0 := by
  simp [X17_eq, prime_iterate_ofRank]

private lemma type17_negative_signature_eq_after
    {q j : ℕ} (hj : 2 * q + 2 < j) :
    signature (Chromosome.prime^[j]
        (Y17 (le_refl q) positive_ne_nonPolarized).1) =
      signature (Chromosome.prime^[j]
        (X17 (le_refl q) positive_ne_nonPolarized).1) := by
  simp only [X17_eq, Y17_eq, GeneType.neg_positive, iterate_map_add,
    prime_iterate_ofRank, map_add]
  have h1 : 2 * q - j = 0 := by omega
  have h2 : 2 * q + 3 - j = 0 := by omega
  have h3 : 2 * q + 2 - j = 0 := by omega
  simp [h1, h2, h3]

/-- At the predecessor (odd) level `2q+1` of the negative type17 branch, a strict
first-component gap gives exactly the `signature (ofRank 1 Positive)` gap. -/
lemma type17_pred_gap_negative
    {N q : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hfst :
      (signature (Chromosome.prime^[2 * q + 1] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q + 1] Y.1.1)).1) :
    signature (Gene.ofRank 1 .Positive) +
        signature (Chromosome.prime^[2 * q + 1] X.1.1) ≤
      signature (Chromosome.prime^[2 * q + 1] Y.1.1) := by
  have hXk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 (2 * q + 1)
  have hYk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 (2 * q + 1)
  have hodd : ¬ Even (2 * q + 1) := Nat.not_even_iff_odd.mpr ⟨q, by ring⟩
  rw [if_neg hodd] at hXk_mem hYk_mem
  have hfst_gap :=
    Mix2LambdaSection17.add_one_le_fst_of_lt_Mix_2Lambda_Pi
      hXk_mem hYk_mem hfst
  have hle := le_iff_dominates.mp hXY.le (2 * q + 1)
  rw [signature_ofRank_one_positive]
  exact ⟨by simpa [Prod.fst_add, add_comm] using hfst_gap, by simpa using hle.2⟩

/-- The type17 diagonal branch
`g⁺(2q+2)+2g⁻(2q+2) → g⁻(2q)+2NP(2q+3)`, assuming the two sigma gaps
where the target exceeds the source. -/
lemma exists_mutation_le_type17_diagonal_negative
    {N q : ℕ}
    (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgneg_rank : gneg.rank = 2 * q + 2)
    (hrank : gpos.rank = gneg.rank)
    (hpos : 1 ≤ X.1.1 gpos) (hneg : 2 ≤ X.1.1 gneg)
    (hgap_pred :
      signature (Gene.ofRank 1 .Positive) +
          signature (Chromosome.prime^[2 * q + 1] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 1] Y.1.1))
    (hgap_rank :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 2] Y.1.1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : gneg ≠ gpos := by
    intro h
    have ht := congrArg Gene.type h
    rw [hgneg, hgpos] at ht
    simp at ht
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gneg 1 - Finsupp.single gneg 1 -
      Finsupp.single gpos 1
  have hevenneg : Even gneg.rank := by
    rw [hgneg_rank]
    exact ⟨q + 1, by ring⟩
  have hevenpos : Even gpos.rank := hrank ▸ hevenneg
  have rest_mem : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda
        (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 hevenneg) hevenneg)
      hevenpos
  let rest : Mix (Pi, 2 • Lambda) := ⟨restval, rest_mem⟩
  have hgpos_eq :
      Gene.ofRank (2 * q + 2) .Positive =
        (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hgpos, hrank, hgneg_rank] at h
  have hgneg_eq :
      Gene.ofRank (2 * q + 2) .Negative =
        (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rwa [hgneg_rank, hgneg] at h
  have hX17val :
      (X17 (le_refl q) positive_ne_nonPolarized).1 =
        Finsupp.single gpos 1 + Finsupp.single gneg 1 +
          Finsupp.single gneg 1 := by
    rw [X17_eq, GeneType.neg_positive, hgpos_eq, hgneg_eq]
  have hXeq :
      (X17 (le_refl q) positive_ne_nonPolarized).1 +
          restval = X.1.1 := by
    rw [hX17val]
    exact Mix2LambdaSection17.single_double_pair_add_rest
      hneg hpos hne
  refine ⟨⟨(Y17 (le_refl q) positive_ne_nonPolarized).1 +
      restval, add_mem
        (Y17 (le_refl q) positive_ne_nonPolarized).2
        rest_mem⟩, ?_, ?_⟩
  · exact (Subtype.ext hXeq :
      (X17 (le_refl q) positive_ne_nonPolarized :
          Mix (Pi, 2 • Lambda)) + rest = X.1) ▸
        Step.mk
          (X17 (le_refl q) positive_ne_nonPolarized)
          (Y17 (le_refl q) positive_ne_nonPolarized)
          rest
          (Primitive.type17 GeneType.Positive (by decide) (le_refl q))
  · change (Y17 (le_refl q) positive_ne_nonPolarized).1 +
        restval ≤ Y.1.1
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp :
        signature (Chromosome.prime^[j] X.1.1) =
          signature (Chromosome.prime^[j]
            (X17 (le_refl q) positive_ne_nonPolarized).1) +
            signature (Chromosome.prime^[j] restval) := by
      conv_lhs => rw [← hXeq]
      rw [iterate_map_add, map_add]
    by_cases hj_before : j < 2 * q + 1
    · rw [type17_negative_signature_eq_before hj_before, ← hdecomp]
      exact le_iff_dominates.mp hXY.le j
    · by_cases hj_pred : j = 2 * q + 1
      · subst j
        rw [type17_negative_signature_at_pred]
        calc
          signature (Gene.ofRank 1 GeneType.Positive) +
                signature (Chromosome.prime^[2 * q + 1]
                  (X17 (le_refl q) positive_ne_nonPolarized).1) +
              signature (Chromosome.prime^[2 * q + 1] restval)
              = signature (Gene.ofRank 1 GeneType.Positive) +
                (signature (Chromosome.prime^[2 * q + 1]
                    (X17 (le_refl q) positive_ne_nonPolarized).1) +
                  signature (Chromosome.prime^[2 * q + 1] restval)) := by abel
          _ = signature (Gene.ofRank 1 GeneType.Positive) +
                signature (Chromosome.prime^[2 * q + 1] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[2 * q + 1] Y.1.1) := hgap_pred
      · by_cases hj_rank : j = 2 * q + 2
        · subst j
          rw [type17_negative_signature_at_rank]
          rw [type17_negative_source_at_rank, zero_add] at hdecomp
          rw [← hdecomp]
          exact hgap_rank
        · have hj_after : 2 * q + 2 < j := by omega
          rw [type17_negative_signature_eq_after hj_after, ← hdecomp]
          exact le_iff_dominates.mp hXY.le j

end MixPi2Lambda
