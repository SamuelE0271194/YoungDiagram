import YoungDiagram.Theorem6.MixPiLambda.Prelim

open Variety hiding prime prime_def
open Chromosome Sigma

namespace MixPiLambda

/-! ## Case 1: X and Y share a gene -/

/-- Remove a shared gene from both X and Y, apply IH, then reattach.
Mirrors `MixLambdaPi.exists_mutation_le_shared_gene`. -/
lemma exists_mutation_le_shared_gene (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nMixPiLambda k, X.1 < Y.1 →
      ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixPiLambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨g, hgX, hgY⟩ := hcommon
  have hg1_mem : (Finsupp.single g 1 : Chromosome) ∈ Mix (Pi, Lambda) :=
    single_mem_Mix_Pi_Lambda X.1.2 hgX
  let X'v : Chromosome := X.1.1 - Finsupp.single g 1
  let Y'v : Chromosome := Y.1.1 - Finsupp.single g 1
  have hX'mem : X'v ∈ Mix (Pi, Lambda) := sub_mem_Mix_Pi_Lambda _ X.1.2
  have hY'mem : Y'v ∈ Mix (Pi, Lambda) := sub_mem_Mix_Pi_Lambda _ Y.1.2
  -- Chromosome-level strict inequality descends to the Mix subtype.
  have hlt_chrom : X'v < Y'v := sub_single_lt_sub_single hgX hgY hXY
  have hlt' : (⟨X'v, hX'mem⟩ : Mix (Pi, Lambda)) < ⟨Y'v, hY'mem⟩ := hlt_chrom
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
    exact MixPiLambda.Step.add_right ⟨Finsupp.single g 1, hg1_mem⟩ hmut'
  · change Z'.1 + Finsupp.single g 1 ≤ Y.1.1
    rw [← sub_single_add_single_eq hgY, le_iff_dominates]
    intro k
    have h := (le_iff_dominates.mp hle') k
    simp only [iterate_map_add, map_add, add_le_add_iff_right]
    exact h

end MixPiLambda
