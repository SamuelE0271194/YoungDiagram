import YoungDiagram.Chromosome

open Chromosome

structure IsMutation (X Y : Chromosome) : Prop where
  le : X ≤ Y
  ne : X ≠ Y
  signature_eq : signature X = signature Y

lemma IsMutation.add_right {X Y : Chromosome} (Z : Chromosome)
    (h : IsMutation X Y) : IsMutation (X + Z) (Y + Z) where
  le := add_le_add_left h.le Z
  ne := by simp [h.ne]
  signature_eq := by simp [h.signature_eq]

lemma IsMutation.of_add_right {X Y Z : Chromosome}
    (h : IsMutation (X + Z) (Y + Z)) : IsMutation X Y where
  le := le_of_add_le_add_right h.le
  ne := by simpa using h.ne
  signature_eq := by simpa using h.signature_eq

lemma IsMutation.iff_add_right {X Y Z : Chromosome} :
    IsMutation (X + Z) (Y + Z) ↔ IsMutation X Y :=
  ⟨.of_add_right, .add_right Z⟩
