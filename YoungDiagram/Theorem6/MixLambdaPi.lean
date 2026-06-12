import YoungDiagram.Theorem6.MixLambdaPi.Case1
import YoungDiagram.Theorem6.MixLambdaPi.Case3

open Variety hiding prime prime_def
open Chromosome

namespace MixLambdaPi

/-- Rank-0 elements of `Mix (Lambda, Pi)` are all zero, so `X < Y` is absurd. -/
lemma exists_mutation_le_rank_zero {X Y : nMixLambdaPi 0} (hXY : X < Y) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_zero X.2).trans (rank_zero Y.2).symm) (ne_of_lt hXY)

/-- A rank-one element of `Mix (Lambda, Pi)` lies entirely in its odd part,
which by definition lies in `Pi`. -/
private lemma mem_Pi_of_mem_Mix_LambdaPi_rank_one
    {X : Chromosome} (hX : X ∈ Mix (Lambda, Pi)) (hr : X.rank = 1) : X ∈ Pi := by
  obtain ⟨ε, hε⟩ := rank_one hr
  have hodd : X.oddPart = X := by
    rw [hε, oddPart_ofRank]; simp
  rw [← hodd]
  exact (mem_Mix_iff.mp hX).2

/-- Rank-1 case: `X < Y` is impossible because rank-1 signatures (in `Pi`)
are pairwise incomparable. -/
lemma exists_mutation_le_rank_one {X Y : nMixLambdaPi 1} (hXY : X < Y) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXPi : X.1.1 ∈ Pi := mem_Pi_of_mem_Mix_LambdaPi_rank_one X.1.2 X.2
  have hYPi : Y.1.1 ∈ Pi := mem_Pi_of_mem_Mix_LambdaPi_rank_one Y.1.2 Y.2
  have hsig_le : signature X.1.1 ≤ signature Y.1.1 := hXY.le 0
  have hXsum : (signature X.1.1).1 + (signature X.1.1).2 = 1 := by
    rcases rank_one_pi_sig hXPi X.2 with h | h <;> simp only [h, zero_add, add_zero]
  have hYsum : (signature Y.1.1).1 + (signature Y.1.1).2 = 1 := by
    rcases rank_one_pi_sig hYPi Y.2 with h | h <;> simp only [h, zero_add, add_zero]
  have hsig_eq : signature X.1.1 = signature Y.1.1 := by
    obtain ⟨h1_le, h2_le⟩ := Prod.le_def.1 hsig_le
    exact Prod.ext (h1_le.antisymm (by linarith [h2_le])) (h2_le.antisymm (by linarith [h1_le]))
  exact absurd (Pi_rank_one_eq_of_sig_eq hXPi hYPi X.2 Y.2 hsig_eq) (ne_of_lt hXY)

/-!
The full theorem `MixLambdaPi.exists_mutation_le` is established by the joint
induction in `YoungDiagram.Theorem6.MixVarietyJoint`, which proves the Case 2
(disjoint-supports / sigma-agreement) sub-case via the cross-variety inductive
hypothesis for `Mix (Pi, Lambda)`. Only Case 4 (§15.10) remains there.

The dispatcher pieces live here and in `MixLambdaPi/Case1.lean` (shared gene)
and `MixLambdaPi/Case3.lean` (disjoint pair).
-/

end MixLambdaPi
