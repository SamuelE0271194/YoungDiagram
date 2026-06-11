import YoungDiagram.Theorem6.MixLambdaPi.Prelim

open Variety hiding prime prime_def
open Chromosome Sigma

namespace MixLambdaPi

/-- Rank-0 elements of `Mix (Lambda, Pi)` are all zero, so `X < Y` is absurd. -/
private lemma exists_mutation_le_rank_zero {X Y : nMixLambdaPi 0} (hXY : X < Y) :
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
private lemma exists_mutation_le_rank_one {X Y : nMixLambdaPi 1} (hXY : X < Y) :
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

/-! ## Case 1: X and Y share a gene -/

/-- Remove a shared gene from both X and Y, apply IH, then reattach.
Mirrors `Pi.exists_mutation_le_shared_gene`. -/
private lemma exists_mutation_le_shared_gene (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nMixLambdaPi k, X.1 < Y.1 →
      ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixLambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨g, hgX, hgY⟩ := hcommon
  have hg1_mem : (Finsupp.single g 1 : Chromosome) ∈ Mix (Lambda, Pi) :=
    single_mem_Mix_Lambda_Pi X.1.2 hgX
  let X'v : Chromosome := X.1.1 - Finsupp.single g 1
  let Y'v : Chromosome := Y.1.1 - Finsupp.single g 1
  have hX'mem : X'v ∈ Mix (Lambda, Pi) := sub_mem_Mix_Lambda_Pi _ X.1.2
  have hY'mem : Y'v ∈ Mix (Lambda, Pi) := sub_mem_Mix_Lambda_Pi _ Y.1.2
  -- Chromosome-level strict inequality descends to the Mix subtype.
  have hlt_chrom : X'v < Y'v := sub_single_lt_sub_single hgX hgY hXY
  have hlt' : (⟨X'v, hX'mem⟩ : Mix (Lambda, Pi)) < ⟨Y'v, hY'mem⟩ := hlt_chrom
  have hX'rank : X'v.rank = m + 2 - g.rank := by
    rw [rank_sub_single hgX]; exact congrArg (· - g.rank) X.2
  have hY'rank : Y'v.rank = m + 2 - g.rank := by
    rw [rank_sub_single hgY]; exact congrArg (· - g.rank) Y.2
  obtain ⟨Z', hmut', hle'⟩ :=
    ih (m + 2 - g.rank) (Nat.sub_lt (by omega) g.rank_pos)
      ⟨⟨X'v, hX'mem⟩, hX'rank⟩ ⟨⟨Y'v, hY'mem⟩, hY'rank⟩ hlt'
  refine ⟨⟨Z'.1 + Finsupp.single g 1, add_mem Z'.2 hg1_mem⟩, ?_, ?_⟩
  · have hX_eq : X.1 = ⟨X'v, hX'mem⟩ + ⟨Finsupp.single g 1, hg1_mem⟩ :=
      Subtype.ext (sub_single_add_single_eq hgX).symm
    rw [hX_eq]
    exact MixLambdaPi.Step.add_right ⟨Finsupp.single g 1, hg1_mem⟩ hmut'
  · change Z'.1 + Finsupp.single g 1 ≤ Y.1.1
    rw [← sub_single_add_single_eq hgY, le_iff_dominates]
    intro k
    have h := (le_iff_dominates.mp hle') k
    simp only [iterate_map_add, map_add, add_le_add_iff_right]
    exact h

/--
Theorem 6 of [Djoković 1982] for `Mix (Lambda, Pi)` (Label 1).
Given `X < Y` of equal rank in `Mix (Lambda, Pi)`, there exists a
`MixLambdaPi.Step` from `X` to some `Z ≤ Y`.

Base cases (rank 0, 1) and the shared-gene sub-case are proved here.
The remaining three sub-cases for rank ≥ 2 are sorried.
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
    · sorry

end MixLambdaPi
