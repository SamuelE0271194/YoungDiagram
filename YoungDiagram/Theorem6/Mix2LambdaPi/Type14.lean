import YoungDiagram.Theorem6.Mix2LambdaPi.Type13
import YoungDiagram.Mutations.Mix2LambdaPi.type14

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

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
