import YoungDiagram.Theorem6.MixPiLambda.Case1
import YoungDiagram.Theorem6.MixPiLambda.Case3

open Variety hiding prime prime_def
open Chromosome Sigma

namespace MixPiLambda

/-- Rank-0 elements of `Mix (Pi, Lambda)` are all zero, so `X < Y` is absurd. -/
lemma exists_mutation_le_rank_zero {X Y : nMixPiLambda 0} (hXY : X < Y) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_zero X.2).trans (rank_zero Y.2).symm) (ne_of_lt hXY)

/-- Any rank-one element of `Mix (Pi, Lambda)` is `Gene.ofRank 1 .NonPolarized`:
its odd part equals itself and must lie in `Lambda`, forcing the gene to be
non-polarized. -/
private lemma rank_one_eq_of_mem {X : Chromosome}
    (hX : X ∈ Mix (Pi, Lambda)) (hr : X.rank = 1) :
    X = Gene.ofRank 1 .NonPolarized := by
  obtain ⟨ε, hε⟩ := rank_one hr
  have hodd : X.oddPart = X := by rw [hε, oddPart_ofRank]; simp
  have hNP : X.IsNonPolarized := by
    rw [← hodd]
    exact mem_Lambda_iff.mp (mem_Mix_iff.mp hX).2
  have : ε = .NonPolarized := by
    rw [hε] at hNP
    exact (IsNonPolarized_ofRank le_rfl).mp hNP
  rw [hε, this]

/-- Rank-1 case: `X < Y` is impossible because every rank-1 element of
`Mix (Pi, Lambda)` equals the unique non-polarized rank-1 chromosome. -/
lemma exists_mutation_le_rank_one {X Y : nMixPiLambda 1} (hXY : X < Y) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_one_eq_of_mem X.1.2 X.2).trans (rank_one_eq_of_mem Y.1.2 Y.2).symm)
    (ne_of_lt hXY)

/-!
The full theorem `MixPiLambda.exists_mutation_le` is established by the joint
induction in `YoungDiagram.Theorem6.MixVarietyJoint`, which proves the Case 2
(disjoint-supports / sigma-agreement) sub-case via the cross-variety inductive
hypothesis for `Mix (Lambda, Pi)`. Only Case 4 (§15.10) remains there.

The dispatcher pieces live here and in `MixPiLambda/Case1.lean` (shared gene)
and `MixPiLambda/Case3.lean` (disjoint pair).
-/

end MixPiLambda
