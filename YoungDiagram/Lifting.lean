import YoungDiagram.Mutations

open Chromosome Variety Mutation

noncomputable section

variable (idx : Fin 5) (k : ℕ)

private abbrev φ := Label idx
private abbrev ψ := Label (Label.prime^[k] idx)

variable {X U : Chromosome} (hX : X ∈ φ idx) (hU : U ∈ ψ idx k)

variable (hMu : Step (Label.prime^[k] idx) (Label.of_mem_prime_iterate hX) ⟨U, hU⟩)

include hU hMu in
lemma mutation_lifting : ∃ (Z : Chromosome) (hZ : Z ∈ φ idx),
    Step idx ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
    Chromosome.prime^[k] Z = U ∧
    ∀ i ≤ k, signature (Chromosome.prime^[i] X) = signature (Chromosome.prime^[i] Z) := by
  
  sorry

end
