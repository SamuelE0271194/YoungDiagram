import YoungDiagram.Theorem6.Pi
import YoungDiagram.Theorem6.MixVarietyJoint
import YoungDiagram.Theorem6.Mix2LambdaPi
import YoungDiagram.Theorem6.MixPi2Lambda

open Variety hiding prime prime_def
open Chromosome

section Finalize

private lemma rank_prime_iterate_mono {A B : Chromosome} (h : A ≤ B) (k : ℕ) :
    (prime^[k] A).rank ≤ (prime^[k] B).rank := by
  obtain ⟨h1, h2⟩ := Prod.le_def.1 (le_iff_dominates.mp h k)
  have hcast : ((prime^[k] A).rank : ℚ) ≤ ((prime^[k] B).rank : ℚ) := by
    rw [← signature_sum_eq_rank, ← signature_sum_eq_rank]; linarith
  exact_mod_cast hcast

/-- A strict dominance is witnessed by a strict rank increase at some level. -/
private lemma exists_rank_prime_lt {A B : Chromosome} (h : A < B) :
    ∃ k, (prime^[k] A).rank < (prime^[k] B).rank := by
  have hnle : ¬ (B ≤ A) := h.2
  rw [le_iff_dominates] at hnle
  obtain ⟨k, hk⟩ := not_forall.mp hnle
  refine ⟨k, ?_⟩
  obtain ⟨h1, h2⟩ := Prod.le_def.1 (le_iff_dominates.mp h.1 k)
  have hne : (prime^[k] A).signature ≠ (prime^[k] B).signature :=
    fun heq => hk (le_of_eq heq.symm)
  have hsum_lt : (prime^[k] A).signature.1 + (prime^[k] A).signature.2 <
      (prime^[k] B).signature.1 + (prime^[k] B).signature.2 := by
    rcases lt_or_eq_of_le h1 with h1' | h1'
    · linarith
    · rcases lt_or_eq_of_le h2 with h2' | h2'
      · linarith
      · exact absurd (Prod.ext h1' h2') hne
  rw [signature_sum_eq_rank, signature_sum_eq_rank] at hsum_lt
  exact_mod_cast hsum_lt

/-- If a prime-iterate is nonzero, the iteration count is below the max rank. -/
private lemma prime_iterate_ne_zero_lt_maxRank {Y : Chromosome} {k : ℕ}
    (h : prime^[k] Y ≠ 0) : k < Y.maxRank := by
  by_contra hge
  exact h (prime_iterate_eq_zero_rank_le.mp
    fun g hg => (le_maxRank g hg).trans (not_lt.mp hge))

/-- The well-founded measure for the decomposition: total rank gap of the
prime-tower between `A` and `B`. -/
private noncomputable def primeDist (A B : Chromosome) : ℕ :=
  ∑ k ∈ Finset.range (B.maxRank + 1), ((prime^[k] B).rank - (prime^[k] A).rank)

/-- A strict step `X < Z` below `Y` strictly decreases the measure. -/
private lemma primeDist_lt {X Z Y : Chromosome} (hXZ : X < Z) (hZY : Z ≤ Y) :
    primeDist Z Y < primeDist X Y := by
  unfold primeDist
  apply Finset.sum_lt_sum
  · intro k _
    have := rank_prime_iterate_mono hXZ.le k
    omega
  · obtain ⟨k, hk⟩ := exists_rank_prime_lt hXZ
    have hZYk := rank_prime_iterate_mono hZY k
    refine ⟨k, Finset.mem_range.mpr ?_, by omega⟩
    have hYk_ne : prime^[k] Y ≠ 0 := by
      intro h0; rw [h0, map_zero] at hZYk; omega
    have := prime_iterate_ne_zero_lt_maxRank hYk_ne
    omega

namespace Pi

/-! ## Decomposition of Π-mutations into primitive steps

Every Π-mutation `X → Y` decomposes as a finite chain of primitive `Pi.Step`s,
and conversely.  The forward direction iterates `exists_mutation_le` along a
well-founded measure; the converse is composition of mutations. -/

/-- Every Π-mutation decomposes as a finite sequence of primitive steps.
Proven by iterating `exists_mutation_le` along the `primeDist` measure. -/
lemma isMutation_imp_transGen_step {X Y : Pi} (h : IsMutation X Y) :
    Relation.TransGen Step X Y := by
  have hrank : Y.1.rank = X.1.rank := by
    have hq : ((X : Chromosome).rank : ℚ) = ((Y : Chromosome).rank : ℚ) := by
      rw [← signature_sum_eq_rank, ← signature_sum_eq_rank, h.signature_eq]
    exact_mod_cast hq.symm
  have hne_n : (⟨X, rfl⟩ : nPi X.1.rank) ≠ ⟨Y, hrank⟩ :=
    fun heq => h.ne (congrArg (fun w : nPi X.1.rank => (w.1 : Chromosome)) heq)
  have hXltY : (⟨X, rfl⟩ : nPi X.1.rank) < ⟨Y, hrank⟩ := lt_of_le_of_ne h.le hne_n
  obtain ⟨Z, hstep, hZY⟩ := exists_mutation_le ⟨X, rfl⟩ ⟨Y, hrank⟩ hXltY
  by_cases hZeqY : Z = Y
  · exact Relation.TransGen.single (hZeqY ▸ hstep)
  · have hZmut : IsMutation Z Y :=
      { le := hZY
        ne := fun heq => hZeqY (Subtype.val_injective heq)
        signature_eq := hstep.isMutation.signature_eq.symm.trans h.signature_eq }
    exact Relation.TransGen.head hstep (isMutation_imp_transGen_step hZmut)
termination_by primeDist (X : Chromosome) (Y : Chromosome)
decreasing_by
  -- Build the dominance `<` by hand: `lt_of_le_of_ne` would grab the unrelated
  -- `Finsupp.partialOrder`, since dominance is only a `Preorder` on `Chromosome`.
  refine primeDist_lt ⟨hstep.isMutation.le, fun hd => ?_⟩ hZY
  exact hstep.isMutation.ne
    (sigmaUnique_Pi X.2 Z.2
      (fun k => le_antisymm (le_iff_dominates.mp hstep.isMutation.le k) (hd k)))

/-- Converse: any finite chain of primitive steps is a mutation.  Elementary —
each step is a mutation and mutations compose, using antisymmetry on `Pi`. -/
lemma transGen_step_imp_isMutation {X Y : Pi} (h : Relation.TransGen Step X Y) :
    IsMutation X Y := by
  induction h with
  | single hstep => exact hstep.isMutation
  | @tail a b hpath hstep ih => exact ih.trans hstep.isMutation

/-- Mutation and reachability by primitive steps coincide on `Pi`. -/
lemma isMutation_iff_transGen_step {X Y : Pi} :
    IsMutation X Y ↔ Relation.TransGen Step X Y :=
  ⟨isMutation_imp_transGen_step, transGen_step_imp_isMutation⟩

end Pi

end Finalize
