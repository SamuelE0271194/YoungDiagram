import YoungDiagram.Theorem6.Mix2LambdaPi.Type15

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-- A thin theorem-level wrapper for type12.  The caller supplies the concrete
decomposition of `X` into the primitive source plus a rest term, and the
post-mutation dominance bound.  This keeps the later case split independent of
whether the third polarized gene is distinct from the rank-`m` pair. -/
lemma exists_mutation_le_type12_of_decomp
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N) (restval : Chromosome)
    (hXeq : (X12 h_le hε).1 + restval = X.1.1)
    (hrest : restval ∈ Mix (2 • Lambda, Pi))
    (hZle : (Y12 h_le hε).1 + restval ≤ Y.1.1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let rest : Mix (2 • Lambda, Pi) := ⟨restval, hrest⟩
  refine ⟨⟨(Y12 h_le hε).1 + restval,
      add_mem (Y12 h_le hε).2 hrest⟩, ?_, hZle⟩
  exact (Subtype.ext hXeq :
      (X12 h_le hε : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
    Step.mk (X12 h_le hε) (Y12 h_le hε) rest
      (Primitive.type12 ε hε h_le)

/-- Before the interval where the extra polarized gene is shifted upward, the
type12 source and target have the same iterated signature. -/
private lemma type12_signature_eq_before
    {m n j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} (h_le : m ≤ n)
    (hj : j ≤ 2 * m) :
    signature (Chromosome.prime^[j] (Y12 h_le hε).1) =
      signature (Chromosome.prime^[j] (X12 h_le hε).1) := by
  simp only [X12_eq, Y12_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have hpair :
      signature (Gene.ofRank (2 * m + 1 - j) GeneType.Positive) +
          signature (Gene.ofRank (2 * m + 1 - j) GeneType.Negative) =
        (((2 * m + 1 - j : ℕ) : ℚ),
          ((2 * m + 1 - j : ℕ) : ℚ)) := by
    have h :=
      signature_sum_ofRank_neg_eq_rank
        (k := 2 * m + 1 - j) (ε := GeneType.Positive)
    rw [GeneType.neg_positive] at h
    exact h
  have hnp :
      signature (Gene.ofRank (2 * m - j) GeneType.NonPolarized) +
          signature (Gene.ofRank (2 * m - j) GeneType.NonPolarized) =
        (((2 * m - j : ℕ) : ℚ), ((2 * m - j : ℕ) : ℚ)) := by
    rw [signature_ofRank_nonPolarized]
    ext <;> simp
  have hextra :
      signature (Gene.ofRank (2 * n + 3 - j) ε) =
        ((1 : ℚ), (1 : ℚ)) +
          signature (Gene.ofRank (2 * n + 1 - j) ε) := by
    have hsucc : 2 * n + 3 - j = (2 * n + 1 - j) + 2 := by omega
    rw [hsucc, signature_ofRank_eq₂']
    abel
  rw [hpair, hnp, hextra]
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;>
    rw [Nat.cast_sub (by omega : j ≤ 2 * m + 1),
      Nat.cast_sub (by omega : j ≤ 2 * m)] <;>
    push_cast <;> ring

/-- On the middle interval of type12, the target exceeds the source by exactly
`(1,1)`. -/
private lemma type12_signature_mid
    {m n j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} (h_le : m ≤ n)
    (hjlo : 2 * m < j) (hjhi : j ≤ 2 * n + 1) :
    signature (Chromosome.prime^[j] (Y12 h_le hε).1) =
      ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[j] (X12 h_le hε).1) := by
  simp only [X12_eq, Y12_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have hpair_zero : 2 * m + 1 - j = 0 := by omega
  have hnp_zero : 2 * m - j = 0 := by omega
  have hextra : 2 * n + 3 - j = (2 * n + 1 - j) + 2 := by omega
  rw [hpair_zero, hnp_zero, hextra]
  simp [Gene.ofRank_zero, signature_ofRank_eq₂']
  abel

/-- At the last nontrivial level of type12, the target exceeds the source by
the rank-one polarized gene of type `ε`. -/
private lemma type12_signature_at_succ
    {m n : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} (h_le : m ≤ n) :
    signature (Chromosome.prime^[2 * n + 2] (Y12 h_le hε).1) =
      signature (Gene.ofRank 1 ε) +
        signature (Chromosome.prime^[2 * n + 2] (X12 h_le hε).1) := by
  simp only [X12_eq, Y12_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have hpos : 2 * m + 1 - (2 * n + 2) = 0 := by omega
  have hnp : 2 * m - (2 * n + 2) = 0 := by omega
  have hsrc : 2 * n + 1 - (2 * n + 2) = 0 := by omega
  have htgt : 2 * n + 3 - (2 * n + 2) = 1 := by omega
  rw [hpos, hnp, hsrc, htgt]
  simp [Gene.ofRank_zero]

/-- After type12's last nontrivial level, source and target again have the same
iterated signature. -/
private lemma type12_signature_eq_after
    {m n j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} (h_le : m ≤ n)
    (hj : 2 * n + 2 < j) :
    signature (Chromosome.prime^[j] (Y12 h_le hε).1) =
      signature (Chromosome.prime^[j] (X12 h_le hε).1) := by
  simp only [X12_eq, Y12_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have hpos : 2 * m + 1 - j = 0 := by omega
  have hnp : 2 * m - j = 0 := by omega
  have hsrc : 2 * n + 1 - j = 0 := by omega
  have htgt : 2 * n + 3 - j = 0 := by omega
  rw [hpos, hnp, hsrc, htgt, Gene.ofRank_zero, map_zero]
  simp

/-- The theorem-level type12 step for concrete genes, assuming the two kinds of
sigma gap appearing in the type12 profile. -/
lemma exists_mutation_le_type12
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (gpos gneg gε : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgε : gε.type = ε)
    (hgrank : gpos.rank = 2 * m + 1)
    (hrank : gpos.rank = gneg.rank)
    (hgε_rank : gε.rank = 2 * n + 1)
    (hpos : 1 ≤ X.1.1 gpos) (hneg : 1 ≤ X.1.1 gneg)
    (hεcopy : 1 ≤ X.1.1 gε)
    (hne_pos_ε : gpos ≠ gε) (hne_neg_ε : gneg ≠ gε)
    (hgap_mid : ∀ j, 2 * m < j → j ≤ 2 * n + 1 →
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * n + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * n + 2] Y.1.1)) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne_pos_neg : gpos ≠ gneg := by
    intro h
    have ht := congrArg Gene.type h
    rw [hgpos, hgneg] at ht
    contradiction
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1 -
      Finsupp.single gε 1
  have hoddpos : Odd gpos.rank := by
    rw [hgrank]
    exact ⟨m, rfl⟩
  have hoddneg : Odd gneg.rank := hrank ▸ hoddpos
  have hoddε : Odd gε.rank := by
    rw [hgε_rank]
    exact ⟨n, rfl⟩
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi
        (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hoddpos) hoddneg)
      hoddε
  let rest : Mix (2 • Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgpos_eq :
      Gene.ofRank (2 * m + 1) GeneType.Positive =
        (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hgrank, hgpos] at h
  have hgneg_eq :
      Gene.ofRank (2 * m + 1) GeneType.Negative =
        (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rw [hgneg, ← hrank, hgrank] at h
    exact h
  have hgε_eq :
      Gene.ofRank (2 * n + 1) ε =
        (Finsupp.single gε 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gε)
    rwa [hgε_rank, hgε] at h
  have hX12val :
      (X12 h_le hε).1 =
        Finsupp.single gpos 1 + Finsupp.single gneg 1 +
          Finsupp.single gε 1 := by
    rw [X12_eq, hgpos_eq, hgneg_eq, hgε_eq]
  have hXeq : (X12 h_le hε).1 + restval = X.1.1 := by
    rw [hX12val]
    exact Mix2LambdaSection17.single_triple_add_rest
      hpos hneg hεcopy hne_pos_neg hne_pos_ε hne_neg_ε
  refine ⟨⟨(Y12 h_le hε).1 + restval, add_mem (Y12 h_le hε).2 rest_mem⟩,
    ?_, ?_⟩
  · exact (Subtype.ext hXeq :
      (X12 h_le hε : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
        Step.mk (X12 h_le hε) (Y12 h_le hε) rest
          (Primitive.type12 ε hε h_le)
  · change (Y12 h_le hε).1 + restval ≤ Y.1.1
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp :
        signature (Chromosome.prime^[j] X.1.1) =
          signature (Chromosome.prime^[j] (X12 h_le hε).1) +
            signature (Chromosome.prime^[j] restval) := by
      conv_lhs => rw [← hXeq]
      rw [iterate_map_add, map_add]
    by_cases hj_before : j ≤ 2 * m
    · rw [type12_signature_eq_before h_le hj_before, ← hdecomp]
      exact le_iff_dominates.mp hXY.le j
    · by_cases hj_mid : j ≤ 2 * n + 1
      · rw [type12_signature_mid h_le (by omega : 2 * m < j) hj_mid]
        calc
          ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] (X12 h_le hε).1) +
              signature (Chromosome.prime^[j] restval)
              = ((1 : ℚ), (1 : ℚ)) +
                (signature (Chromosome.prime^[j] (X12 h_le hε).1) +
                  signature (Chromosome.prime^[j] restval)) := by abel
          _ = ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
            hgap_mid j (by omega) hj_mid
      · by_cases hj_succ : j = 2 * n + 2
        · subst j
          rw [type12_signature_at_succ h_le]
          calc
            signature (Gene.ofRank 1 ε) +
                  signature (Chromosome.prime^[2 * n + 2] (X12 h_le hε).1) +
                signature (Chromosome.prime^[2 * n + 2] restval)
                = signature (Gene.ofRank 1 ε) +
                  (signature (Chromosome.prime^[2 * n + 2] (X12 h_le hε).1) +
                    signature (Chromosome.prime^[2 * n + 2] restval)) := by abel
            _ = signature (Gene.ofRank 1 ε) +
                  signature (Chromosome.prime^[2 * n + 2] X.1.1) := by rw [← hdecomp]
            _ ≤ signature (Chromosome.prime^[2 * n + 2] Y.1.1) := hgap_succ
        · have hj_after : 2 * n + 2 < j := by omega
          rw [type12_signature_eq_after h_le hj_after, ← hdecomp]
          exact le_iff_dominates.mp hXY.le j

end Mix2LambdaPi
