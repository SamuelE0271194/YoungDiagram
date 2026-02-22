import YoungDiagram.MutationsAux
import YoungDiagram.Variety

open Chromosome Variety

namespace Variety

namespace Pi

variable {m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)

noncomputable section type1

variable (hle : m ≤ n) (hm : 1 ≤ m)

def X1 : Pi := by
  use Gene.ofRank m ε + Gene.ofRank n (- ε)
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRank hm],
    by rwa [IsPolarized_ofRank (hm.trans hle),
      ← GeneType.neg_ne_nonPolarized_iff]⟩

lemma X1_eq : X1 hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n (- ε) := rfl

def Y1 : Pi := by
  use Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRank (Nat.le_add_left 1 n)]⟩
  match m with
  | 1 =>
    rw [← mem_Pi_iff, Nat.sub_self, Gene.ofRank_zero]
    exact zero_mem _
  | m + 2 =>
    rwa [IsPolarized_ofRank (Nat.le_of_ble_eq_true rfl),
      ← GeneType.neg_ne_nonPolarized_iff]

lemma Y1_eq : Y1 hε hle hm =
  Gene.ofRank (m - 1) (- ε) + Gene.ofRank (n + 1) ε := rfl

end type1

noncomputable section type2

variable (hle : m ≤ n) (hm : 1 < m)

def X2 : Pi := by
  use Gene.ofRank m ε + Gene.ofRank n ε
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRank (le_of_lt hm)],
    by rwa [IsPolarized_ofRank ((le_of_lt hm).trans hle)]⟩

lemma X2_eq : X2 hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n ε := rfl

def Y2 : Pi := by
  use Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRank (Nat.le_add_left 1 (n + 1))]⟩
  match m with
  | 2 =>
    rw [← mem_Pi_iff, Nat.sub_self, Gene.ofRank_zero]
    exact zero_mem _
  | m + 3 => rwa [IsPolarized_ofRank (by omega)]

lemma Y2_eq : Y2 hε hle hm =
  Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε := rfl

end type2

noncomputable section type3

variable (hle : m ≤ n) (hm : 1 ≤ m)

def X3 : Pi := by
  use Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε)
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRankAlt hm], by
    rwa [IsPolarized_ofRankAlt (hm.trans hle),
      ← GeneType.neg_ne_nonPolarized_iff]⟩

lemma X3_eq : X3 hε hle hm =
  Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε) := rfl

def Y3 : Pi := by
  use Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε
  rw [mem_Pi_iff, IsPolarized_iff_add]
  refine ⟨?_, by rwa [IsPolarized_ofRankAlt (by omega)]⟩
  match m with
  | 1 =>
    rw [Nat.sub_self, Gene.ofRankAlt_def, Gene.ofRank_zero, ← mem_Pi_iff]
    exact zero_mem _
  | m + 2 => rwa [IsPolarized_ofRankAlt (by omega),
    GeneType.neg_ne_nonPolarized_iff, neg_neg]

lemma Y3_eq : Y3 hε hle hm =
  Gene.ofRankAlt (m - 1) (- ε) + Gene.ofRankAlt (n + 1) ε := rfl

end type3

inductive Primitive : Pi → Pi → Prop
  | type1 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      Primitive (X1 hε hle hm) (Y1 hε hle hm)
  | type2 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 < m) :
      Primitive (X2 hε hle hm) (Y2 hε hle hm)
  | type3 (ε : GeneType) (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (hle : m ≤ n) (hm : 1 ≤ m) :
      Primitive (X3 hε hle hm) (Y3 hε hle hm)

inductive Step : Pi → Pi → Prop
  | mk (X Y Z : Pi) (h : Primitive X Y) :
      Step (X + Z) (Y + Z)

end Pi

end Variety

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

lemma Pi.Primitive.isMutation {X Y : Pi} (h : Variety.Pi.Primitive X Y) :
    IsMutation X Y := by
  cases h with
  | type1 ε hε hle hm =>
    exact ⟨mutation_type1_le hε hle,
      mutation_type1_ne hle hm, mutation_type1_signature_eq hε hle hm⟩
  | type2 ε hε hle hm =>
    exact ⟨mutation_type2_le hε hle hm,
      mutation_type2_ne hle hm, mutation_type2_signature_eq hε hle hm⟩
  | type3 ε hε hle hm =>
    exact ⟨mutation_type3_le hε hle hm,
      mutation_type3_ne hle hm, mutation_type3_signature_eq hε hle hm⟩

lemma Pi.Step.isMutation {X Y : Pi} (h : Variety.Pi.Step X Y) :
    IsMutation X Y := by
  cases h with
  | mk X Y Z h =>
    exact .add_right _ (Pi.Primitive.isMutation h)

def Mutation.Step : (i : Fin 5) → (Label i) → (Label i) → Prop
  | 0 => Pi.Step
  | 1 => sorry
  | 2 => sorry
  | 3 => sorry
  | 4 => sorry
