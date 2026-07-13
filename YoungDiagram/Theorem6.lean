import YoungDiagram.Theorem6.Pi
import YoungDiagram.Theorem6.MixVarietyJoint
import YoungDiagram.Theorem6.Mix2LambdaPi
import YoungDiagram.Theorem6.MixPi2Lambda

open Variety hiding prime prime_def
open Chromosome
open Pointwise

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

/-! ## Decomposition on the four mixed varieties

The well-founded decomposition argument is independent of the primitive list.
The only variety-specific inputs are the one-step theorem, the fact that each
step is a mutation, and sigma-uniqueness for antisymmetry. -/

private lemma mutation_trans_of_bile {V : Variety} {X Y Z : V}
    (eq_of_bile : ∀ A B : V, (A : Chromosome) ≤ B → (B : Chromosome) ≤ A → A = B)
    (h₁ : IsMutation X Y) (h₂ : IsMutation Y Z) : IsMutation X Z where
  le := h₁.le.trans h₂.le
  ne := by
    intro hXZ
    apply h₁.ne
    exact congrArg Subtype.val (eq_of_bile X Y h₁.le (by
      show (Y : Chromosome) ≤ X
      rw [hXZ]
      exact h₂.le))
  signature_eq := h₁.signature_eq.trans h₂.signature_eq

private lemma isMutation_imp_transGen_step_of_exists {V : Variety}
    (StepV : V → V → Prop)
    (eq_of_bile : ∀ A B : V, (A : Chromosome) ≤ B → (B : Chromosome) ≤ A → A = B)
    (step_isMutation : ∀ {A B : V}, StepV A B → IsMutation A B)
    (existsStep : ∀ {n : ℕ} (A B : {T : V // T.1.rank = n}), A < B →
      ∃ Z : V, StepV A.1 Z ∧ Z ≤ B.1)
    {X Y : V} (h : IsMutation X Y) : Relation.TransGen StepV X Y := by
  have hrank : Y.1.rank = X.1.rank := by
    have hq : ((X : Chromosome).rank : ℚ) = ((Y : Chromosome).rank : ℚ) := by
      rw [← signature_sum_eq_rank, ← signature_sum_eq_rank, h.signature_eq]
    exact_mod_cast hq.symm
  have hXltY : (⟨X, rfl⟩ : {T : V // T.1.rank = X.1.rank}) < ⟨Y, hrank⟩ := by
    refine ⟨h.le, fun hYX => h.ne ?_⟩
    exact congrArg Subtype.val (eq_of_bile X Y h.le hYX)
  obtain ⟨Z, hstep, hZY⟩ := existsStep ⟨X, rfl⟩ ⟨Y, hrank⟩ hXltY
  by_cases hZeqY : Z = Y
  · exact Relation.TransGen.single (hZeqY ▸ hstep)
  · have hZmut : IsMutation Z Y :=
      { le := hZY
        ne := fun heq => hZeqY (Subtype.val_injective heq)
        signature_eq := (step_isMutation hstep).signature_eq.symm.trans h.signature_eq }
    exact Relation.TransGen.head hstep
      (isMutation_imp_transGen_step_of_exists StepV eq_of_bile step_isMutation existsStep hZmut)
termination_by primeDist (X : Chromosome) (Y : Chromosome)
decreasing_by
  have hstepMut := step_isMutation hstep
  refine primeDist_lt ⟨hstepMut.le, fun hZX => hstepMut.ne ?_⟩ hZY
  exact congrArg Subtype.val (eq_of_bile X Z hstepMut.le hZX)

private lemma transGen_step_imp_isMutation_of_step {V : Variety}
    (StepV : V → V → Prop)
    (eq_of_bile : ∀ A B : V, (A : Chromosome) ≤ B → (B : Chromosome) ≤ A → A = B)
    (step_isMutation : ∀ {A B : V}, StepV A B → IsMutation A B)
    {X Y : V} (h : Relation.TransGen StepV X Y) : IsMutation X Y := by
  induction h with
  | single hstep => exact step_isMutation hstep
  | @tail A B hpath hstep ih =>
      exact mutation_trans_of_bile eq_of_bile ih (step_isMutation hstep)

namespace MixLambdaPi

lemma isMutation_imp_transGen_step {X Y : Mix (Lambda, Pi)} (h : IsMutation X Y) :
    Relation.TransGen Step X Y :=
  isMutation_imp_transGen_step_of_exists Step
    (fun A B hAB hBA => le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA))
    Step.isMutation exists_mutation_le h

lemma transGen_step_imp_isMutation {X Y : Mix (Lambda, Pi)}
    (h : Relation.TransGen Step X Y) : IsMutation X Y :=
  transGen_step_imp_isMutation_of_step Step
    (fun A B hAB hBA => le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA))
    Step.isMutation h

lemma isMutation_iff_transGen_step {X Y : Mix (Lambda, Pi)} :
    IsMutation X Y ↔ Relation.TransGen Step X Y :=
  ⟨isMutation_imp_transGen_step, transGen_step_imp_isMutation⟩

end MixLambdaPi

namespace MixPiLambda

lemma isMutation_imp_transGen_step {X Y : Mix (Pi, Lambda)} (h : IsMutation X Y) :
    Relation.TransGen Step X Y :=
  isMutation_imp_transGen_step_of_exists Step
    (fun A B hAB hBA => le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA))
    Step.isMutation exists_mutation_le h

lemma transGen_step_imp_isMutation {X Y : Mix (Pi, Lambda)}
    (h : Relation.TransGen Step X Y) : IsMutation X Y :=
  transGen_step_imp_isMutation_of_step Step
    (fun A B hAB hBA => le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA))
    Step.isMutation h

lemma isMutation_iff_transGen_step {X Y : Mix (Pi, Lambda)} :
    IsMutation X Y ↔ Relation.TransGen Step X Y :=
  ⟨isMutation_imp_transGen_step, transGen_step_imp_isMutation⟩

end MixPiLambda

namespace Mix2LambdaPi

lemma isMutation_imp_transGen_step {X Y : Mix (2 • Lambda, Pi)} (h : IsMutation X Y) :
    Relation.TransGen Step X Y :=
  isMutation_imp_transGen_step_of_exists Step
    (fun A B hAB hBA => le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA))
    Step.isMutation exists_mutation_le h

lemma transGen_step_imp_isMutation {X Y : Mix (2 • Lambda, Pi)}
    (h : Relation.TransGen Step X Y) : IsMutation X Y :=
  transGen_step_imp_isMutation_of_step Step
    (fun A B hAB hBA => le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA))
    Step.isMutation h

lemma isMutation_iff_transGen_step {X Y : Mix (2 • Lambda, Pi)} :
    IsMutation X Y ↔ Relation.TransGen Step X Y :=
  ⟨isMutation_imp_transGen_step, transGen_step_imp_isMutation⟩

end Mix2LambdaPi

namespace MixPi2Lambda

lemma isMutation_imp_transGen_step {X Y : Mix (Pi, 2 • Lambda)} (h : IsMutation X Y) :
    Relation.TransGen Step X Y :=
  isMutation_imp_transGen_step_of_exists Step
    (fun A B hAB hBA => le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA))
    Step.isMutation exists_mutation_le h

lemma transGen_step_imp_isMutation {X Y : Mix (Pi, 2 • Lambda)}
    (h : Relation.TransGen Step X Y) : IsMutation X Y :=
  transGen_step_imp_isMutation_of_step Step
    (fun A B hAB hBA => le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA))
    Step.isMutation h

lemma isMutation_iff_transGen_step {X Y : Mix (Pi, 2 • Lambda)} :
    IsMutation X Y ↔ Relation.TransGen Step X Y :=
  ⟨isMutation_imp_transGen_step, transGen_step_imp_isMutation⟩

end MixPi2Lambda

end Finalize
