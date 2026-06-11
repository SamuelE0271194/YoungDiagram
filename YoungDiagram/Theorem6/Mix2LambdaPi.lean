import YoungDiagram.Theorem6.Mix2LambdaPi.Prelim

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-- Rank-0 elements of `Mix (2 • Lambda, Pi)` are all zero, so `X < Y` is absurd. -/
private lemma exists_mutation_le_rank_zero {X Y : nMix2LambdaPi 0} (hXY : X < Y) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_zero X.2).trans (rank_zero Y.2).symm) (ne_of_lt hXY)

/-- A rank-one element of `Mix (2 • Lambda, Pi)` lies in `Pi`: its odd part
equals the element and lies in `Pi` by definition; its even part is `0` so
the `2 • Lambda` constraint is vacuous. -/
private lemma mem_Pi_of_mem_Mix_2Lambda_Pi_rank_one
    {X : Chromosome} (hX : X ∈ Mix (2 • Lambda, Pi)) (hr : X.rank = 1) : X ∈ Pi := by
  obtain ⟨ε, hε⟩ := rank_one hr
  have hodd : X.oddPart = X := by rw [hε, oddPart_ofRank]; simp
  rw [← hodd]
  exact (mem_Mix_iff.mp hX).2

/-- Rank-1 case: `X < Y` is impossible because rank-1 signatures (in `Pi`)
are pairwise incomparable. -/
private lemma exists_mutation_le_rank_one {X Y : nMix2LambdaPi 1} (hXY : X < Y) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXPi : X.1.1 ∈ Pi := mem_Pi_of_mem_Mix_2Lambda_Pi_rank_one X.1.2 X.2
  have hYPi : Y.1.1 ∈ Pi := mem_Pi_of_mem_Mix_2Lambda_Pi_rank_one Y.1.2 Y.2
  have hsig_le : signature X.1.1 ≤ signature Y.1.1 := hXY.le 0
  have hXsum : (signature X.1.1).1 + (signature X.1.1).2 = 1 := by
    rcases rank_one_pi_sig hXPi X.2 with h | h <;> simp only [h, zero_add, add_zero]
  have hYsum : (signature Y.1.1).1 + (signature Y.1.1).2 = 1 := by
    rcases rank_one_pi_sig hYPi Y.2 with h | h <;> simp only [h, zero_add, add_zero]
  have hsig_eq : signature X.1.1 = signature Y.1.1 := by
    obtain ⟨h1_le, h2_le⟩ := Prod.le_def.1 hsig_le
    exact Prod.ext (h1_le.antisymm (by linarith [h2_le])) (h2_le.antisymm (by linarith [h1_le]))
  exact absurd (Pi_rank_one_eq_of_sig_eq hXPi hYPi X.2 Y.2 hsig_eq) (ne_of_lt hXY)

/--
Theorem 6 of [Djoković 1982] for `Mix (2 • Lambda, Pi)` (Label 3).
Given `X < Y` of equal rank in `Mix (2 • Lambda, Pi)`, there exists a
`Mix2LambdaPi.Step` from `X` to some `Z ≤ Y`.

Currently only ranks 0 and 1 are filled in; higher ranks are sorried,
awaiting a port of the §15 case analysis adapted to the 9 primitive types
(X9-X17).
-/
theorem exists_mutation_le {n : ℕ} : ∀ (X Y : nMix2LambdaPi n), X < Y →
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X Z ∧ Z ≤ Y :=
  Nat.strongRecOn n fun n _ih X Y hXY ↦
  match n with
  | 0 => exists_mutation_le_rank_zero hXY
  | 1 => exists_mutation_le_rank_one hXY
  | _ + 2 => sorry

end Mix2LambdaPi
