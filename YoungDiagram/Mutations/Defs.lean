import YoungDiagram.Mutations.Pi

open Variety

namespace Mutation

def Step : (i : Fin 5) → (Label i) → (Label i) → Prop
  | 0 => Pi.Step
  | 1 => sorry
  | 2 => sorry
  | 3 => sorry
  | 4 => sorry

end Mutation
