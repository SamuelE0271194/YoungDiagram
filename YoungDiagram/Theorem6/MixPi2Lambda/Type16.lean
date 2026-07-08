import YoungDiagram.Theorem6.MixPi2Lambda.Type13
import YoungDiagram.Mutations.MixPi2Lambda.type16

/-!
# Label 4 type16 mutation wrappers (mirror of `Mix2LambdaPi.Type16`)

Parity flip: `2g^ε(2m+2)+g^{-ε}(2n+2) → 2NP(2m+1)+g^ε(2n+4)`.  Only the general
Step constructors are ported here (clean rank-substituted mirror); the boundary
window-signature lemmas are added by the §17 L4 case files with the correct
`a_i=b_i for i even` parity.
-/

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-- General type16 Step constructor. -/
lemma exists_mutation_le_type16_of_decomp
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMixPi2Lambda N) (restval : Chromosome)
    (hXeq : (X16 h_le hε).1 + restval = X.1.1)
    (hrest : restval ∈ Mix (Pi, 2 • Lambda))
    (hZle : (Y16 h_le hε).1 + restval ≤ Y.1.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let rest : Mix (Pi, 2 • Lambda) := ⟨restval, hrest⟩
  refine ⟨⟨(Y16 h_le hε).1 + restval,
      add_mem (Y16 h_le hε).2 hrest⟩, ?_, hZle⟩
  exact (Subtype.ext hXeq :
      (X16 h_le hε : Mix (Pi, 2 • Lambda)) + rest = X.1) ▸
    Step.mk (X16 h_le hε) (Y16 h_le hε) rest
      (Primitive.type16 ε hε h_le)

/-- Concrete-gene wrapper for general type16: source
`2g^ε(2m+2)+g^{-ε}(2n+2)+rest`; caller supplies the dominance bound. -/
lemma exists_mutation_le_type16_of_genes
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMixPi2Lambda N)
    (gdouble gsingle : Gene)
    (hdouble_type : gdouble.type = ε)
    (hsingle_type : gsingle.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * m + 2)
    (hsingle_rank : gsingle.rank = 2 * n + 2)
    (hdouble : 2 ≤ X.1.1 gdouble) (hsingle : 1 ≤ X.1.1 gsingle)
    (hne : gdouble ≠ gsingle)
    (hZle :
      (Y16 h_le hε).1 +
          (X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
            Finsupp.single gsingle 1) ≤ Y.1.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
      Finsupp.single gsingle 1
  have hevendouble : Even gdouble.rank := by rw [hdouble_rank]; exact ⟨m + 1, by ring⟩
  have hevensingle : Even gsingle.rank := by rw [hsingle_rank]; exact ⟨n + 1, by ring⟩
  have rest_mem : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda
        (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 hevendouble) hevendouble)
      hevensingle
  have hgdouble_eq :
      Gene.ofRank (2 * m + 2) ε =
        (Finsupp.single gdouble 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gdouble)
    rwa [hdouble_rank, hdouble_type] at h
  have hgsingle_eq :
      Gene.ofRank (2 * n + 2) (-ε) =
        (Finsupp.single gsingle 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gsingle)
    rwa [hsingle_rank, hsingle_type] at h
  have hX16val :
      (X16 h_le hε).1 =
        Finsupp.single gdouble 1 + Finsupp.single gdouble 1 +
          Finsupp.single gsingle 1 := by
    rw [X16_eq, hgdouble_eq, hgsingle_eq]
  have hXeq : (X16 h_le hε).1 + restval = X.1.1 := by
    rw [hX16val]
    exact Mix2LambdaSection17.double_single_pair_add_rest hdouble hsingle hne
  exact exists_mutation_le_type16_of_decomp hε h_le X Y restval hXeq
    rest_mem hZle

end MixPi2Lambda
