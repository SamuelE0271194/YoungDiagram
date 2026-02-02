import YoungDiagram.Mutations

open Chromosome

noncomputable section

variable (idx : Fin 5) (k : ℕ)

abbrev φ := VarietyLabel idx
abbrev ψ := VarietyLabel (VarietyLabel.prime^[k] idx)

variable {X U : Chromosome} (hX : X ∈ φ idx) (hU : U ∈ ψ idx k)

variable (hMu : MutationStep (VarietyLabel.prime^[k] idx)
    (VarietyLabel.of_mem_prime_iter hX) ⟨U, hU⟩)

include hU hMu in
lemma lifting_property : ∃ Z : Chromosome, (hZ : Z ∈ φ idx) →
    MutationStep idx ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
    prime^[k] Z = U ∧
    ∀ i ≤ k, signature (prime^[k] X) = signature (prime^[k] Z) := sorry

end
