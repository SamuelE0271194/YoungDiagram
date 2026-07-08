import YoungDiagram.Theorem6.MixPi2Lambda.Type13
import YoungDiagram.Mutations.MixPi2Lambda.type14

/-!
# Label 4 type14 mutation wrappers (mirror of `Mix2LambdaPi.Type14`)

Parity flip vs Label 3: polarized genes at EVEN rank (`2m+2`), NP at ODD rank
(`2m+1`).  The general `of_decomp` / `of_genes` Step constructors below are a
clean rank-substituted mirror.  The rank-boundary window-signature lemmas are
structurally different for Label 4 (minimal polarized rank is `2`, and rank-`1`
NP genes exist at the bottom) and are added by the §17 case files that need them.
-/

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-- General type14 Step constructor: given `X14 h_le hε + rest = X` and the
target dominance `Y14 h_le hε + rest ≤ Y`, produce the reducing mutation. -/
lemma exists_mutation_le_type14_of_decomp
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMixPi2Lambda N) (restval : Chromosome)
    (hXeq : (X14 h_le hε).1 + restval = X.1.1)
    (hrest : restval ∈ Mix (Pi, 2 • Lambda))
    (hZle : (Y14 h_le hε).1 + restval ≤ Y.1.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let rest : Mix (Pi, 2 • Lambda) := ⟨restval, hrest⟩
  refine ⟨⟨(Y14 h_le hε).1 + restval,
      add_mem (Y14 h_le hε).2 hrest⟩, ?_, hZle⟩
  exact (Subtype.ext hXeq :
      (X14 h_le hε : Mix (Pi, 2 • Lambda)) + rest = X.1) ▸
    Step.mk (X14 h_le hε) (Y14 h_le hε) rest
      (Primitive.type14 ε hε h_le)

/-- Concrete-gene wrapper for general type14: source
`2g^ε(2m+2)+2g^{-ε}(2n+2)+rest`; caller supplies the dominance bound. -/
lemma exists_mutation_le_type14_of_genes
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMixPi2Lambda N)
    (gdouble gopp : Gene)
    (hdouble_type : gdouble.type = ε)
    (hopp_type : gopp.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * m + 2)
    (hopp_rank : gopp.rank = 2 * n + 2)
    (hdouble : 2 ≤ X.1.1 gdouble) (hopp : 2 ≤ X.1.1 gopp)
    (hne : gdouble ≠ gopp)
    (hZle :
      (Y14 h_le hε).1 +
          (X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
            Finsupp.single gopp 1 - Finsupp.single gopp 1) ≤ Y.1.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
      Finsupp.single gopp 1 - Finsupp.single gopp 1
  have hevendouble : Even gdouble.rank := by rw [hdouble_rank]; exact ⟨m + 1, by ring⟩
  have hevenopp : Even gopp.rank := by rw [hopp_rank]; exact ⟨n + 1, by ring⟩
  have rest_mem : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda
        (sub_single_one_mem_Mix_Pi_2Lambda
          (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 hevendouble) hevendouble)
        hevenopp)
      hevenopp
  have hgdouble_eq :
      Gene.ofRank (2 * m + 2) ε =
        (Finsupp.single gdouble 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gdouble)
    rwa [hdouble_rank, hdouble_type] at h
  have hgopp_eq :
      Gene.ofRank (2 * n + 2) (-ε) =
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

end MixPi2Lambda
