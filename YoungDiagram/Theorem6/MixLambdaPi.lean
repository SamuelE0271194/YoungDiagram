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

/--
Theorem 6 of [Djoković 1982] for `Mix (Lambda, Pi)` (Label 1).
Given `X < Y` of equal rank in `Mix (Lambda, Pi)`, there exists a
`MixLambdaPi.Step` from `X` to some `Z ≤ Y`.

Base cases (rank 0, 1) and the shared-gene sub-case, and the disjoint pair sub-case
are proved here. The remaining sub-cases for rank ≥ 2 are sorried.
-/
theorem exists_mutation_le {n : ℕ} : ∀ (X Y : nMixLambdaPi n), X < Y →
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X Z ∧ Z ≤ Y :=
  Nat.strongRecOn n fun n ih X Y hXY ↦
  match n with
  | 0 => exists_mutation_le_rank_zero hXY
  | 1 => exists_mutation_le_rank_one hXY
  | m + 2 => by
    by_cases hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g
    · exact exists_mutation_le_shared_gene m ih X Y hXY hcommon
    · by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
        Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k
      · sorry  -- Case2 (sigma equal)
      · by_cases hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
          g.type = .Positive ∧ h.type = .Negative ∧
          0 < X.1.1 g ∧ 0 < X.1.1 h
        · exact exists_mutation_le_disjoint_pair X Y hXY hcommon hsigeq hXpn
        · sorry  -- Case4 (§15.10)

end MixLambdaPi
