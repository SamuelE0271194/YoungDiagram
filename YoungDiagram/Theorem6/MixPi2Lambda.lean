import YoungDiagram.Theorem6.MixPi2Lambda.Case1
import YoungDiagram.Theorem6.MixPi2Lambda.Case34

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-- Rank-0 elements of `Mix (Pi, 2 • Lambda)` are all zero, so `X < Y` is absurd. -/
private lemma exists_mutation_le_rank_zero {X Y : nMixPi2Lambda 0} (hXY : X < Y) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_zero X.2).trans (rank_zero Y.2).symm) (ne_of_lt hXY)

/-- There are no rank-1 elements of `Mix (Pi, 2 • Lambda)`: a rank-1 chromosome
is a single gene with coefficient `1`, which cannot lie in `2 • Lambda`. -/
private lemma exists_mutation_le_rank_one {X Y : nMixPi2Lambda 1} (_hXY : X < Y) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  exfalso
  obtain ⟨ε, hε⟩ := rank_one X.2
  have hodd : X.1.1.oddPart = X.1.1 := by rw [hε, oddPart_ofRank]; simp
  have hX2L : X.1.1 ∈ 2 • Lambda := by
    rw [← hodd]
    exact (mem_Mix_iff.mp X.1.2).2
  obtain ⟨Y0, _, hY02⟩ := hX2L
  change 2 • Y0 = X.1.1 at hY02
  set g : Gene := ⟨1, ε, Nat.one_pos⟩
  have hone : X.1.1 g = 1 := by
    rw [hε, Gene.ofRank_eq_gene' Nat.one_ne_zero]
    exact Finsupp.single_eq_same
  have htwo : X.1.1 g = 2 * Y0 g := by
    rw [← hY02]; rfl
  rw [hone] at htwo
  omega

/--
Theorem 6 of [Djoković 1982] for `Mix (Pi, 2 • Lambda)` (Label 4).
Given `X < Y` of equal rank in `Mix (Pi, 2 • Lambda)`, there exists a
`MixPi2Lambda.Step` from `X` to some `Z ≤ Y`.

Base cases (rank 0, 1) and the shared-gene sub-case are proved here. The
remaining sub-cases for rank ≥ 2 are sorried, awaiting a port of the §15 case
analysis adapted to the 9 primitive types (X9-X17).
-/
theorem exists_mutation_le {n : ℕ} : ∀ (X Y : nMixPi2Lambda n), X < Y →
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X Z ∧ Z ≤ Y :=
  Nat.strongRecOn n fun n ih X Y hXY ↦
  match n with
  | 0 => exists_mutation_le_rank_zero hXY
  | 1 => exists_mutation_le_rank_one hXY
  | m + 2 => by
    by_cases hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g
    · exact exists_mutation_le_shared_gene m ih X Y hXY hcommon
    · exact exists_mutation_le_case34 m ih X Y hXY hcommon

end MixPi2Lambda
