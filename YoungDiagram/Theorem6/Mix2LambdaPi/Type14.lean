import YoungDiagram.Theorem6.Mix2LambdaPi.Type13
import YoungDiagram.Mutations.Mix2LambdaPi.type14

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

private lemma type14_rank_one_signature_eq_zero
    {q : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[0] (Y14 (Nat.zero_le (q + 1)) hε).1) =
      signature (Chromosome.prime^[0] (X14 (Nat.zero_le (q + 1)) hε).1) := by
  simpa only [Function.iterate_zero_apply, X14_eq, Y14_eq] using
    (mutation_type14_signature_eq (ε := ε) (m := 0) (n := q + 1)).symm

private lemma type14_rank_one_signature_odd_mid
    {q j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hjlo : 1 ≤ j) (hjhi : j ≤ 2 * q + 3) (hjodd : ¬ Even j) :
    signature (Chromosome.prime^[j] (Y14 (Nat.zero_le (q + 1)) hε).1) =
      signature (Chromosome.prime^[j] (X14 (Nat.zero_le (q + 1)) hε).1) +
        ((1 : ℚ), (1 : ℚ)) := by
  simp only [X14_eq, Y14_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h1 : 1 - j = 0 := by omega
  have h0 : 0 - j = 0 := by omega
  have htop : 2 * (q + 1) + 2 - j =
      (2 * (q + 1) + 1 - j) + 1 := by omega
  rw [h1, h0, htop, Gene.ofRank_zero, map_zero, zero_add, zero_add,
    signature_ofRank_nonPolarized]
  have hk_even : Even (2 * (q + 1) + 1 - j) := by
    rcases Nat.not_even_iff_odd.mp hjodd with ⟨t, rfl⟩
    use q + 1 - t
    omega
  rw [signature_ofRank_even_half (ε := -ε) hk_even]
  simp

private lemma type14_rank_one_signature_even_mid
    {q j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hjlo : 1 ≤ j) (hjhi : j ≤ 2 * q + 3) (hjeven : Even j) :
    signature (Chromosome.prime^[j] (Y14 (Nat.zero_le (q + 1)) hε).1) =
      signature (Chromosome.prime^[j] (X14 (Nat.zero_le (q + 1)) hε).1) +
        (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε)) := by
  simp only [X14_eq, Y14_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h1 : 1 - j = 0 := by omega
  have h0 : 0 - j = 0 := by omega
  have htop : 2 * (q + 1) + 2 - j =
      (2 * (q + 1) + 1 - j) + 1 := by omega
  rw [h1, h0, htop, Gene.ofRank_zero, map_zero, zero_add, zero_add,
    signature_ofRank_nonPolarized]
  have hj_le_even : j ≤ 2 * q + 2 := by
    rcases hjeven with ⟨t, ht⟩
    rw [ht] at hjhi ⊢
    omega
  have hk_pos : 1 ≤ 2 * (q + 1) + 1 - j := by omega
  have hk_odd : ¬ Even (2 * (q + 1) + 1 - j) := by
    intro hk_even
    rcases hjeven with ⟨t, ht⟩
    rw [ht] at hk_even
    rcases hk_even with ⟨u, hu⟩
    omega
  have hk_pred_even : Even (2 * (q + 1) + 1 - j - 1) := by
    by_contra h
    exact hk_odd ((Nat.even_sub_one hk_pos).2 h)
  cases ε with
  | NonPolarized => exact False.elim (hε rfl)
  | Positive =>
      simp only [GeneType.neg_positive, signature_ofRank_one_positive]
      rw [signature_ofRank_negative hk_pos,
        signature_ofRank_even_half (ε := GeneType.Positive) hk_pred_even]
      have hk_cast :
          ((2 * (q + 1) + 1 - j : ℕ) : ℚ) =
            ((2 * (q + 1) + 1 - j - 1 : ℕ) : ℚ) + 1 := by
        have hk_eq : 2 * (q + 1) + 1 - j =
            (2 * (q + 1) + 1 - j - 1) + 1 := by omega
        rw [hk_eq]
        norm_num
      simp [hk_cast]
      constructor <;> linarith
  | Negative =>
      simp only [GeneType.neg_negative, signature_ofRank_one_negative]
      rw [signature_ofRank_positive hk_pos,
        signature_ofRank_even_half (ε := GeneType.Negative) hk_pred_even]
      have hk_cast :
          ((2 * (q + 1) + 1 - j : ℕ) : ℚ) =
            ((2 * (q + 1) + 1 - j - 1 : ℕ) : ℚ) + 1 := by
        have hk_eq : 2 * (q + 1) + 1 - j =
            (2 * (q + 1) + 1 - j - 1) + 1 := by omega
        rw [hk_eq]
        norm_num
      simp [hk_cast]
      constructor <;> linarith

private lemma type14_rank_one_signature_eq_after
    {q j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hj : 2 * q + 3 < j) :
    signature (Chromosome.prime^[j] (Y14 (Nat.zero_le (q + 1)) hε).1) =
      signature (Chromosome.prime^[j] (X14 (Nat.zero_le (q + 1)) hε).1) := by
  simp only [X14_eq, Y14_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h0 : 0 - j = 0 := by omega
  have h1 : 1 - j = 0 := by omega
  have hsource : 2 * (q + 1) + 1 - j = 0 := by omega
  have htarget : 2 * (q + 1) + 2 - j = 0 := by omega
  simp [h0, h1, hsource, htarget]

/-- Dominance assembly for the rank-one lower endpoint of type14,
`2g^ε(1)+2g^{-ε}(2q+3) → 2g(0)+2g(2q+4)`.

The target-source signature delta is only parity-dependent in the middle
window: odd levels need `(1,1)` slack, while even levels need two copies of the
rank-one `ε` signature. -/
lemma type14_rank_one_target_add_rest_le_of_gaps
    {N q : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1) (restval : Chromosome)
    (hXeq : (X14 (Nat.zero_le (q + 1)) hε).1 + restval = X.1.1)
    (hgap_odd : ∀ j, 1 ≤ j → j ≤ 2 * q + 3 → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_even : ∀ j, 1 ≤ j → j ≤ 2 * q + 3 → Even j →
      (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1)) :
    (Y14 (Nat.zero_le (q + 1)) hε).1 + restval ≤ Y.1.1 := by
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp :
      signature (Chromosome.prime^[j] X.1.1) =
        signature (Chromosome.prime^[j] (X14 (Nat.zero_le (q + 1)) hε).1) +
          signature (Chromosome.prime^[j] restval) := by
    conv_lhs => rw [← hXeq]
    rw [iterate_map_add, map_add]
  by_cases hj_zero : j = 0
  · subst j
    rw [type14_rank_one_signature_eq_zero, ← hdecomp]
    exact le_iff_dominates.mp hXY.le 0
  · by_cases hj_mid : j ≤ 2 * q + 3
    · have hjlo : 1 ≤ j := by omega
      by_cases hjeven : Even j
      · rw [type14_rank_one_signature_even_mid hjlo hj_mid hjeven]
        calc
          (signature (Chromosome.prime^[j] (X14 (Nat.zero_le (q + 1)) hε).1) +
                  (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε))) +
              signature (Chromosome.prime^[j] restval)
              = (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε)) +
                  (signature (Chromosome.prime^[j]
                      (X14 (Nat.zero_le (q + 1)) hε).1) +
                    signature (Chromosome.prime^[j] restval)) := by abel
          _ = (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε)) +
                signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
            hgap_even j hjlo hj_mid hjeven
      · rw [type14_rank_one_signature_odd_mid hjlo hj_mid hjeven]
        calc
          (signature (Chromosome.prime^[j] (X14 (Nat.zero_le (q + 1)) hε).1) +
                  ((1 : ℚ), (1 : ℚ))) +
              signature (Chromosome.prime^[j] restval)
              = ((1 : ℚ), (1 : ℚ)) +
                  (signature (Chromosome.prime^[j]
                      (X14 (Nat.zero_le (q + 1)) hε).1) +
                    signature (Chromosome.prime^[j] restval)) := by abel
          _ = ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
            hgap_odd j hjlo hj_mid hjeven
    · have hj_after : 2 * q + 3 < j := by omega
      rw [type14_rank_one_signature_eq_after hj_after, ← hdecomp]
      exact le_iff_dominates.mp hXY.le j

/-- A thin theorem-level wrapper for general type14.  The caller supplies the
source decomposition and the dominance bound after replacing the source by the
type14 target. -/
lemma exists_mutation_le_type14_of_decomp
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N) (restval : Chromosome)
    (hXeq : (X14 h_le hε).1 + restval = X.1.1)
    (hrest : restval ∈ Mix (2 • Lambda, Pi))
    (hZle : (Y14 h_le hε).1 + restval ≤ Y.1.1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let rest : Mix (2 • Lambda, Pi) := ⟨restval, hrest⟩
  refine ⟨⟨(Y14 h_le hε).1 + restval,
      add_mem (Y14 h_le hε).2 hrest⟩, ?_, hZle⟩
  exact (Subtype.ext hXeq :
      (X14 h_le hε : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
    Step.mk (X14 h_le hε) (Y14 h_le hε) rest
      (Primitive.type14 ε hε h_le)

/-- Concrete-gene wrapper for general type14.  This packages the source
decomposition `2g^ε(2m+1)+2g^{-ε}(2n+1)+rest` and the rest membership; the
caller still supplies the final dominance bound for the type14 target plus the
rest.  The rank-one boundary used in §17 Case 3 is the specialization `m = 0`. -/
lemma exists_mutation_le_type14_of_genes
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N)
    (gdouble gopp : Gene)
    (hdouble_type : gdouble.type = ε)
    (hopp_type : gopp.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * m + 1)
    (hopp_rank : gopp.rank = 2 * n + 1)
    (hdouble : 2 ≤ X.1.1 gdouble) (hopp : 2 ≤ X.1.1 gopp)
    (hne : gdouble ≠ gopp)
    (hZle :
      (Y14 h_le hε).1 +
          (X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
            Finsupp.single gopp 1 - Finsupp.single gopp 1) ≤ Y.1.1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
      Finsupp.single gopp 1 - Finsupp.single gopp 1
  have hodddouble : Odd gdouble.rank := by rw [hdouble_rank]; exact ⟨m, rfl⟩
  have hoddopp : Odd gopp.rank := by rw [hopp_rank]; exact ⟨n, rfl⟩
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi
        (sub_single_one_mem_Mix_2Lambda_Pi
          (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hodddouble) hodddouble)
        hoddopp)
      hoddopp
  have hgdouble_eq :
      Gene.ofRank (2 * m + 1) ε =
        (Finsupp.single gdouble 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gdouble)
    rwa [hdouble_rank, hdouble_type] at h
  have hgopp_eq :
      Gene.ofRank (2 * n + 1) (-ε) =
        (Finsupp.single gopp 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gopp)
    rwa [hopp_rank, hopp_type] at h
  have hX14val :
      (X14 h_le hε).1 =
        Finsupp.single gdouble 1 + Finsupp.single gdouble 1 +
          Finsupp.single gopp 1 + Finsupp.single gopp 1 := by
    rw [X14_eq, hgdouble_eq, hgopp_eq]
  have hXeq : (X14 h_le hε).1 + restval = X.1.1 := by
    rw [hX14val]
    exact Mix2LambdaSection17.double_pair_add_rest hdouble hopp hne
  exact exists_mutation_le_type14_of_decomp hε h_le X Y restval hXeq
    rest_mem hZle

end Mix2LambdaPi
