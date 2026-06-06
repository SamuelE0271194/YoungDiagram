import YoungDiagram.Mutations
import YoungDiagram.Lifting.Pi

open Variety hiding prime
open Chromosome Mutation

noncomputable section

variable (idx : Fin 5) (k : ℕ)

private abbrev φ := Label idx
private abbrev ψ := Label (Label.prime^[k] idx)

variable {X U : Chromosome} (hX : X ∈ φ idx) (hU : U ∈ ψ idx k)

variable (hMu : Step (Label.prime^[k] idx) (Label.of_mem_prime_iterate hX) ⟨U, hU⟩)

include hU hMu in
lemma mutation_lifting : ∃ (Z : Chromosome) (hZ : Z ∈ φ idx),
    Step idx ⟨X, hX⟩ ⟨Z, hZ⟩ ∧
    prime^[k] Z = U ∧
    ∀ i ≤ k, signature (prime^[i] X) = signature (prime^[i] Z) := by
  match idx with
  | 0 =>
    refine Pi.mutation_lifting hX ?_ ?_
    · exact congrArg (U ∈ ·)
        (congrArg Label Label.prime_iterate_zero).symm |>.mpr hU
    · change Step 0 ⟨prime^[k] X, prime_mem_Pi_iterate hX⟩ ⟨U, _⟩
      convert hMu
      · exact Label.prime_iterate_zero.symm
      · rfl
  | 1 => sorry
  | 2 => sorry
  | 3 => sorry
  | 4 => sorry

end
