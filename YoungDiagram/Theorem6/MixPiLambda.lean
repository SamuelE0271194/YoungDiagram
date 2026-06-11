import YoungDiagram.Theorem6.MixPiLambda.Prelim

open Variety hiding prime prime_def
open Chromosome Sigma

namespace MixPiLambda

/-- Rank-0 elements of `Mix (Pi, Lambda)` are all zero, so `X < Y` is absurd. -/
private lemma exists_mutation_le_rank_zero {X Y : nMixPiLambda 0} (hXY : X < Y) :
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
private lemma exists_mutation_le_rank_one {X Y : nMixPiLambda 1} (hXY : X < Y) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_one_eq_of_mem X.1.2 X.2).trans (rank_one_eq_of_mem Y.1.2 Y.2).symm)
    (ne_of_lt hXY)

/--
Theorem 6 of [Djoković 1982] for `Mix (Pi, Lambda)` (Label 2).
Given `X < Y` of equal rank in `Mix (Pi, Lambda)`, there exists a
`MixPiLambda.Step` from `X` to some `Z ≤ Y`.

Proof strategy: planned via `prime`-duality from
`MixLambdaPi.exists_mutation_le` together with
`MixPiLambda.mutation_lifting_odd`. Currently only ranks 0 and 1 are filled
in; higher ranks are sorried.
-/
theorem exists_mutation_le {n : ℕ} : ∀ (X Y : nMixPiLambda n), X < Y →
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X Z ∧ Z ≤ Y :=
  Nat.strongRecOn n fun n _ih X Y hXY ↦
  match n with
  | 0 => exists_mutation_le_rank_zero hXY
  | 1 => exists_mutation_le_rank_one hXY
  | _ + 2 => sorry

end MixPiLambda
