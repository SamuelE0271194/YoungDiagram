import Mathlib
import YoungDiagram.Mutations

open Chromosome

variable {idx : Fin 5} {k : ℕ}

local notation "φ"  => VarietyLabel idx
local notation "φᵏ" => VarietyLabel <| VarietyLabel.prime^[k] idx

section lifting_property

variable {X U : Chromosome} (hX : X ∈ φ) (hU : U ∈ φᵏ)
variable (hMu : MutationStep (VarietyLabel.prime^[k] idx)
    (VarietyLabel.of_mem_prime_iter hX) ⟨U, hU⟩)

lemma lifting_property : ∃ Z : Chromosome, (hZ : Z ∈ φ) →
    MutationStep idx ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
    prime^[k] Z = U ∧
    ∀ i ≤ k, signature (prime^[k] X) = signature (prime^[k] Z) := sorry

end lifting_property
