import YoungDiagram.Theorem6.MixPi2Lambda.Type11
import YoungDiagram.Mutations.MixPi2Lambda.type10

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-- A thin theorem-level wrapper for type10.  The caller supplies the concrete
source decomposition and the dominance bound after replacing the source by the
type10 target. -/
lemma exists_mutation_le_type10_of_decomp
    {N m n : ℕ} {ε ε' : GeneType}
    (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMixPi2Lambda N) (restval : Chromosome)
    (hXeq : (X10 h_le hε hε').1 + restval = X.1.1)
    (hrest : restval ∈ Mix (Pi, 2 • Lambda))
    (hZle : (Y10 h_le hε hε').1 + restval ≤ Y.1.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let rest : Mix (Pi, 2 • Lambda) := ⟨restval, hrest⟩
  refine ⟨⟨(Y10 h_le hε hε').1 + restval,
      add_mem (Y10 h_le hε hε').2 hrest⟩, ?_, hZle⟩
  exact (Subtype.ext hXeq :
      (X10 h_le hε hε' : Mix (Pi, 2 • Lambda)) + rest = X.1) ▸
    Step.mk (X10 h_le hε hε') (Y10 h_le hε hε') rest
      (Primitive.type10 ε ε' hε hε' h_le)

/-- Concrete-gene wrapper for type10.  This packages the source decomposition
`g^ε(2m+2)+g^{ε'}(2n+2)+rest` and the rest membership; the caller still supplies
the final dominance bound for the type10 target plus the rest.  This is the
`g^+(m)+g^ε(k) → g^+(m-2)+g^ε(k+2)` step used in §17 Case 1 (`m ≥ 3`). -/
lemma exists_mutation_le_type10_of_genes
    {N m n : ℕ} {ε ε' : GeneType}
    (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMixPi2Lambda N)
    (g1 g2 : Gene)
    (hg1 : g1.type = ε) (hg2 : g2.type = ε')
    (hg1_rank : g1.rank = 2 * m + 2) (hg2_rank : g2.rank = 2 * n + 2)
    (hcopy1 : 1 ≤ X.1.1 g1) (hcopy2 : 1 ≤ X.1.1 g2) (hne : g1 ≠ g2)
    (hZle :
      (Y10 h_le hε hε').1 +
          (X.1.1 - Finsupp.single g1 1 - Finsupp.single g2 1) ≤ Y.1.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single g1 1 - Finsupp.single g2 1
  have heven1 : Even g1.rank := by rw [hg1_rank]; exact ⟨m + 1, by ring⟩
  have heven2 : Even g2.rank := by rw [hg2_rank]; exact ⟨n + 1, by ring⟩
  have rest_mem : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 heven1) heven2
  have hg1_eq :
      Gene.ofRank (2 * m + 2) ε = (Finsupp.single g1 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g1)
    rwa [hg1_rank, hg1] at h
  have hg2_eq :
      Gene.ofRank (2 * n + 2) ε' = (Finsupp.single g2 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g2)
    rwa [hg2_rank, hg2] at h
  have hX10val :
      (X10 h_le hε hε').1 = Finsupp.single g1 1 + Finsupp.single g2 1 := by
    rw [X10_eq, hg1_eq, hg2_eq]
  have hXeq : (X10 h_le hε hε').1 + restval = X.1.1 := by
    rw [hX10val]
    exact Mix2LambdaSection17.single_pair_add_rest hcopy1 hcopy2 hne
  exact exists_mutation_le_type10_of_decomp hε hε' h_le X Y restval hXeq
    rest_mem hZle

/-- Degenerate concrete-gene wrapper for type10 with a single doubled gene:
`2 g^ε(2a+2) → g^ε(2a) + g^ε(2a+4)`.  This is the `X ⊃ 2g⁺(m)` sub-case of
§17 Case 1, where the type10 source uses two copies of the same gene. -/
lemma exists_mutation_le_type10_of_double
    {N a : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMixPi2Lambda N) (g : Gene)
    (hg : g.type = ε) (hg_rank : g.rank = 2 * a + 2)
    (hg2 : 2 ≤ X.1.1 g)
    (hZle :
      (Y10 (le_refl a) hε hε).1 +
          (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) ≤ Y.1.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single g 1 - Finsupp.single g 1
  have heven : Even g.rank := by rw [hg_rank]; exact ⟨a + 1, by ring⟩
  have rest_mem : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 heven) heven
  have hg_eq :
      Gene.ofRank (2 * a + 2) ε = (Finsupp.single g 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g)
    rwa [hg_rank, hg] at h
  have hX10val :
      (X10 (le_refl a) hε hε).1 = Finsupp.single g 1 + Finsupp.single g 1 := by
    rw [X10_eq, hg_eq]
  have hXeq : (X10 (le_refl a) hε hε).1 + restval = X.1.1 := by
    rw [hX10val]
    exact Mix2LambdaSection17.double_single_add_rest hg2
  exact exists_mutation_le_type10_of_decomp hε hε (le_refl a) X Y restval hXeq
    rest_mem hZle

/-! ### Per-level signature deltas for the type10 mutation

The type10 mutation moves the `ε`-gene down by two ranks and the `ε'`-gene up by
two ranks.  At level `j`, the signature difference `σ(Y10^[j]) − σ(X10^[j])` is:
`0` for `j ≤ 2m` (the two `(1,1)` increments cancel); `(1,1)` throughout the
middle window `2m+2 ≤ j ≤ 2n+2` (only the up-moving `ε'`-gene contributes); and
`0` again for `j ≥ 2n+4`.  The two transition levels `j = 2m+1, 2n+3` are handled
inline by the assembly. -/

private lemma type10_signature_eq_before {m n j : ℕ} {ε ε' : GeneType}
    (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized) (h_le : m ≤ n)
    (hj : j ≤ 2 * m) :
    signature (Chromosome.prime^[j] (Y10 h_le hε hε').1) =
      signature (Chromosome.prime^[j] (X10 h_le hε hε').1) := by
  simp only [X10_eq, Y10_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have eA : 2 * m + 2 - j = (2 * m - j) + 2 := by omega
  have eC : 2 * n + 4 - j = (2 * n + 2 - j) + 2 := by omega
  rw [eA, eC, signature_ofRank_eq₂', signature_ofRank_eq₂']
  abel

private lemma type10_signature_mid {m n j : ℕ} {ε ε' : GeneType}
    (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized) (h_le : m ≤ n)
    (hj1 : 2 * m + 2 ≤ j) (hj2 : j ≤ 2 * n + 2) :
    signature (Chromosome.prime^[j] (Y10 h_le hε hε').1) =
      signature (Chromosome.prime^[j] (X10 h_le hε hε').1) + ((1 : ℚ), (1 : ℚ)) := by
  simp only [X10_eq, Y10_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have e1 : 2 * m - j = 0 := by omega
  have e2 : 2 * m + 2 - j = 0 := by omega
  have eC : 2 * n + 4 - j = (2 * n + 2 - j) + 2 := by omega
  rw [e1, e2, eC, Gene.ofRank_zero, map_zero, signature_ofRank_eq₂']
  abel

private lemma type10_signature_eq_after {m n j : ℕ} {ε ε' : GeneType}
    (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized) (h_le : m ≤ n)
    (hj : 2 * n + 4 ≤ j) :
    signature (Chromosome.prime^[j] (Y10 h_le hε hε').1) =
      signature (Chromosome.prime^[j] (X10 h_le hε hε').1) := by
  simp only [X10_eq, Y10_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have e1 : 2 * m - j = 0 := by omega
  have e2 : 2 * m + 2 - j = 0 := by omega
  have e3 : 2 * n + 2 - j = 0 := by omega
  have e4 : 2 * n + 4 - j = 0 := by omega
  simp [e1, e2, e3, e4]

/-- Transition level `j = 2m+1` (paper's `m-1`): the delta is `(1,1) - s(1,ε)`,
written additively as `s(1,ε) + σ(Y10) = (1,1) + σ(X10)`. -/
private lemma type10_signature_pred {m n : ℕ} {ε ε' : GeneType}
    (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized) (h_le : m ≤ n) :
    signature (Gene.ofRank 1 ε) +
        signature (Chromosome.prime^[2 * m + 1] (Y10 h_le hε hε').1) =
      ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * m + 1] (X10 h_le hε hε').1) := by
  simp only [X10_eq, Y10_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have e1 : 2 * m - (2 * m + 1) = 0 := by omega
  have e2 : 2 * m + 2 - (2 * m + 1) = 1 := by omega
  have eC : 2 * n + 4 - (2 * m + 1) = (2 * n + 2 - (2 * m + 1)) + 2 := by omega
  rw [e1, e2, eC, Gene.ofRank_zero, map_zero, signature_ofRank_eq₂']
  abel

/-- Transition level `j = 2n+3` (paper's `k+1`): the delta is `s(1,ε')`. -/
private lemma type10_signature_succ {m n : ℕ} {ε ε' : GeneType}
    (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized) (h_le : m ≤ n) :
    signature (Chromosome.prime^[2 * n + 3] (Y10 h_le hε hε').1) =
      signature (Gene.ofRank 1 ε') +
        signature (Chromosome.prime^[2 * n + 3] (X10 h_le hε hε').1) := by
  simp only [X10_eq, Y10_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have e1 : 2 * m - (2 * n + 3) = 0 := by omega
  have e2 : 2 * m + 2 - (2 * n + 3) = 0 := by omega
  have e3 : 2 * n + 2 - (2 * n + 3) = 0 := by omega
  have e4 : 2 * n + 4 - (2 * n + 3) = 1 := by omega
  rw [e1, e2, e3, e4]
  simp [Gene.ofRank_zero]

/-- Dominance assembly for the type10 mutation, mirroring
`type11_target_add_rest_le_of_diagonal_gap`.  Given the source decomposition and
the five-region gap data, the type10 target plus the rest is dominated by `Y`. -/
lemma type10_target_add_rest_le_of_diagonal_gap
    {N m n : ℕ} {ε ε' : GeneType} (hε : ε ≠ .NonPolarized) (hε' : ε' ≠ .NonPolarized)
    (h_le : m ≤ n) (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1) (restval : Chromosome)
    (hXeq : (X10 h_le hε hε').1 + restval = X.1.1)
    (hgap_pred :
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[2 * m + 1] X.1.1) ≤
        signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * m + 1] Y.1.1))
    (hgap_mid : ∀ j, 2 * m + 2 ≤ j → j ≤ 2 * n + 2 →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 ε') +
          signature (Chromosome.prime^[2 * n + 3] X.1.1) ≤
        signature (Chromosome.prime^[2 * n + 3] Y.1.1)) :
    (Y10 h_le hε hε').1 + restval ≤ Y.1.1 := by
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp :
      signature (Chromosome.prime^[j] X.1.1) =
        signature (Chromosome.prime^[j] (X10 h_le hε hε').1) +
          signature (Chromosome.prime^[j] restval) := by
    conv_lhs => rw [← hXeq]
    rw [iterate_map_add, map_add]
  by_cases hj_before : j ≤ 2 * m
  · rw [type10_signature_eq_before hε hε' h_le hj_before, ← hdecomp]
    exact le_iff_dominates.mp hXY.le j
  · by_cases hj_pred : j = 2 * m + 1
    · subst j
      apply le_of_add_le_add_left (a := signature (Gene.ofRank 1 ε))
      calc
        signature (Gene.ofRank 1 ε) +
            (signature (Chromosome.prime^[2 * m + 1] (Y10 h_le hε hε').1) +
              signature (Chromosome.prime^[2 * m + 1] restval))
            = (signature (Gene.ofRank 1 ε) +
                signature (Chromosome.prime^[2 * m + 1] (Y10 h_le hε hε').1)) +
              signature (Chromosome.prime^[2 * m + 1] restval) := by abel
        _ = (((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[2 * m + 1] (X10 h_le hε hε').1)) +
              signature (Chromosome.prime^[2 * m + 1] restval) := by
              rw [type10_signature_pred]
        _ = ((1 : ℚ), (1 : ℚ)) +
              signature (Chromosome.prime^[2 * m + 1] X.1.1) := by
              rw [hdecomp]; abel
        _ ≤ signature (Gene.ofRank 1 ε) +
              signature (Chromosome.prime^[2 * m + 1] Y.1.1) := hgap_pred
    · by_cases hj_mid : j ≤ 2 * n + 2
      · rw [type10_signature_mid hε hε' h_le (by omega : 2 * m + 2 ≤ j) hj_mid]
        calc
          signature (Chromosome.prime^[j] (X10 h_le hε hε').1) +
                ((1 : ℚ), (1 : ℚ)) +
              signature (Chromosome.prime^[j] restval)
              = ((1 : ℚ), (1 : ℚ)) +
                (signature (Chromosome.prime^[j] (X10 h_le hε hε').1) +
                  signature (Chromosome.prime^[j] restval)) := by abel
          _ = ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
            hgap_mid j (by omega) hj_mid
      · by_cases hj_succ : j = 2 * n + 3
        · subst j
          rw [type10_signature_succ hε hε' h_le]
          calc
            signature (Gene.ofRank 1 ε') +
                  signature (Chromosome.prime^[2 * n + 3] (X10 h_le hε hε').1) +
                signature (Chromosome.prime^[2 * n + 3] restval)
                = signature (Gene.ofRank 1 ε') +
                  (signature (Chromosome.prime^[2 * n + 3] (X10 h_le hε hε').1) +
                    signature (Chromosome.prime^[2 * n + 3] restval)) := by abel
            _ = signature (Gene.ofRank 1 ε') +
                  signature (Chromosome.prime^[2 * n + 3] X.1.1) := by rw [← hdecomp]
            _ ≤ signature (Chromosome.prime^[2 * n + 3] Y.1.1) := hgap_succ
        · have hj_after : 2 * n + 4 ≤ j := by omega
          rw [type10_signature_eq_after hε hε' h_le hj_after, ← hdecomp]
          exact le_iff_dominates.mp hXY.le j

end MixPi2Lambda
