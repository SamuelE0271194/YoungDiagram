import Mathlib
import YoungDiagram.Mutations

open Chromosome

variable (idx : Fin 5) (k : ℕ)

noncomputable abbrev φ := VarietyLabel idx
noncomputable abbrev φk := VarietyLabel (VarietyLabel.prime^[k] idx)

variable {X U : Chromosome} (hX : X ∈ φ idx) (hU : U ∈ φk idx k)

noncomputable abbrev LiftingMutationStep :=
  MutationStep (VarietyLabel.prime^[k] idx)
    (VarietyLabel.of_mem_prime_iter hX) ⟨U, hU⟩

variable (hMu : LiftingMutationStep idx k hX hU)

include hU hMu in
lemma lifting_property : ∃ Z : Chromosome, (hZ : Z ∈ φ idx) →
    MutationStep idx ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
    prime^[k] Z = U ∧
    ∀ i ≤ k, signature (prime^[k] X) = signature (prime^[k] Z) := sorry
