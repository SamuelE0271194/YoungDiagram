import YoungDiagram.Mutations.Pi
import YoungDiagram.Chromosome.Dual

open Variety hiding prime prime_def
open Chromosome

namespace Pi

/-- The sign-dual of a polarized chromosome. -/
noncomputable def dual (X : Pi) : Pi :=
  ⟨Chromosome.dual X.val, by
    rw [mem_Pi_iff, IsPolarized_def']
    intro g hg
    have hg_dual : X.val g.dual ≠ 0 := by
      simpa [Chromosome.dual_apply] using Finsupp.mem_support_iff.mp hg
    have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp X.2) g.dual
      (Finsupp.mem_support_iff.mpr hg_dual)
    exact GeneType.neg_ne_nonPolarized_iff.2 hpol⟩

@[simp] lemma dual_val (X : Pi) : (dual X).val = Chromosome.dual X.val := rfl

@[simp] lemma dual_dual (X : Pi) : dual (dual X) = X :=
  Subtype.val_injective (Chromosome.dual_dual X.val)

@[simp] lemma dual_add (X Y : Pi) : dual (X + Y) = dual X + dual Y :=
  Subtype.val_injective (Chromosome.dual_add X.val Y.val)

lemma dual_le_dual_iff {X Y : Pi} : dual X ≤ dual Y ↔ X ≤ Y :=
  Chromosome.dual_le_dual_iff

lemma dual_lt_dual_iff {X Y : Pi} : dual X < dual Y ↔ X < Y :=
  lt_iff_lt_of_le_iff_le' dual_le_dual_iff dual_le_dual_iff

@[simp] lemma dual_X1 {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
    dual (X1 hε hle hm) =
      X1 ((GeneType.neg_ne_nonPolarized_iff.1 hε)) hle hm := by
  ext g
  simp [X1_eq]

@[simp] lemma dual_Y1 {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
    dual (Y1 hε hle hm) =
      Y1 ((GeneType.neg_ne_nonPolarized_iff.1 hε)) hle hm := by
  ext g
  simp [Y1_eq, add_comm]

@[simp] lemma dual_X2 {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 < m) :
    dual (X2 hε hle hm) =
      X2 ((GeneType.neg_ne_nonPolarized_iff.1 hε)) hle hm := by
  ext g
  simp [X2_eq]

@[simp] lemma dual_Y2 {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 < m) :
    dual (Y2 hε hle hm) =
      Y2 ((GeneType.neg_ne_nonPolarized_iff.1 hε)) hle hm := by
  ext g
  simp [Y2_eq]

@[simp] lemma dual_X3 {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
    dual (X3 hε hle hm) =
      X3 ((GeneType.neg_ne_nonPolarized_iff.1 hε)) hle hm := by
  apply Subtype.val_injective
  simp only [dual_val, X3_eq, Chromosome.dual_add,
    Chromosome.dual_ofRankAlt, neg_neg]

@[simp] lemma dual_Y3 {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
    dual (Y3 hε hle hm) =
      Y3 ((GeneType.neg_ne_nonPolarized_iff.1 hε)) hle hm := by
  apply Subtype.val_injective
  simp only [dual_val, Y3_eq, Chromosome.dual_add,
    Chromosome.dual_ofRankAlt, neg_neg]

lemma Primitive.dual {X Y : Pi} (h : Primitive X Y) :
    Primitive (dual X) (dual Y) := by
  cases h with
  | type1 ε hε hle hm =>
      simpa using Primitive.type1 (-ε) (GeneType.neg_ne_nonPolarized_iff.1 hε) hle hm
  | type2 ε hε hle hm =>
      simpa using Primitive.type2 (-ε) (GeneType.neg_ne_nonPolarized_iff.1 hε) hle hm
  | type3 ε hε hle hm =>
      simpa using Primitive.type3 (-ε) (GeneType.neg_ne_nonPolarized_iff.1 hε) hle hm

lemma Step.dual {X Y : Pi} (h : Step X Y) : Step (dual X) (dual Y) := by
  cases h with
  | mk X Y Z hPrim =>
    rw [dual_add, dual_add]
    exact Step.mk (Pi.dual X) (Pi.dual Y) (Pi.dual Z) (Primitive.dual hPrim)

lemma Step.of_dual {X Y : Pi} (h : Step (Pi.dual X) (Pi.dual Y)) : Step X Y := by
  simpa using h.dual

end Pi
