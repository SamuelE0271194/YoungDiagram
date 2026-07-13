import YoungDiagram

#eval [true].IsAlt
#eval [true, true].IsAlt
#eval [true, false].IsAlt
#eval [true, false, true].IsAlt
#eval [false, true, false].IsAlt

#eval [true].toGene
#eval [true, false].toGene
#eval [true, false, true].toGene
#eval [false, true, false].toGene

#eval [true].toGene.toList
#eval [true, false].toGene.toList
#eval [true, false, true].toGene.toList
#eval [false, true, false].toGene.toList

#eval [true].toGene.signature
#eval [true, false].toGene.signature
#eval [true, false, true].toGene.signature
#eval [false, true, false].toGene.signature

open Pointwise Variety Mutation

#check Pi
#check Mix (Lambda, Pi)
#check Mix (Pi, Lambda)
#check Mix (2 • Lambda, Pi)
#check Mix (Pi, 2 • Lambda)

#synth SMul ℕ Variety

noncomputable section example_of_mutation

abbrev X := Gene.ofRank 5 .Positive +
  Gene.ofRank 4 .Positive + Gene.ofRank 1 .Negative

abbrev Y₁ := Gene.ofRank 6 .Negative +
  Gene.ofRank 4 .Positive

example : IsMutation X Y₁ := by
  rw [X, Y₁, add_comm, ← add_assoc, IsMutation.iff_add_right]
  have primMut := @Pi.Primitive.type1 .Negative (by decide) 1 5 NeZero.one_le NeZero.one_le
  have := Pi.Primitive.isMutation primMut
  simpa [Pi.Y1, Pi.X1] using this

end example_of_mutation

section check

/--
info: 'Pi.exists_mutation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Pi.exists_mutation_le

/--
info: Pi.exists_mutation_le {n : ℕ} (X Y : nPi n) : X < Y → ∃ Z, Pi.Step (↑X) Z ∧ Z ≤ ↑Y
-/
#guard_msgs in
#check Pi.exists_mutation_le

/--
info: 'MixPiLambda.exists_mutation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MixPiLambda.exists_mutation_le

/--
info: MixPiLambda.exists_mutation_le {n : ℕ} (X Y : nMixPiLambda n) (hXY : ↑X < ↑Y) : ∃ Z, MixPiLambda.Step (↑X) Z ∧ Z ≤ ↑Y
-/
#guard_msgs in
#check MixPiLambda.exists_mutation_le

/--
info: 'MixLambdaPi.exists_mutation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MixLambdaPi.exists_mutation_le

/--
info: MixLambdaPi.exists_mutation_le {n : ℕ} (X Y : nMixLambdaPi n) (hXY : ↑X < ↑Y) : ∃ Z, MixLambdaPi.Step (↑X) Z ∧ Z ≤ ↑Y
-/
#guard_msgs in
#check MixLambdaPi.exists_mutation_le

/--
info: 'Mix2LambdaPi.exists_mutation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mix2LambdaPi.exists_mutation_le

/--
info: Mix2LambdaPi.exists_mutation_le {n : ℕ} (X Y : nMix2LambdaPi n) (hXY : X < Y) : ∃ Z, Mix2LambdaPi.Step (↑X) Z ∧ Z ≤ ↑Y
-/
#guard_msgs in
#check Mix2LambdaPi.exists_mutation_le

/--
info: 'MixPi2Lambda.exists_mutation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MixPi2Lambda.exists_mutation_le

/--
info: MixPi2Lambda.exists_mutation_le {n : ℕ} (X Y : nMixPi2Lambda n) (hXY : X < Y) : ∃ Z, MixPi2Lambda.Step (↑X) Z ∧ Z ≤ ↑Y
-/
#guard_msgs in
#check MixPi2Lambda.exists_mutation_le

end check
