import YoungDiagram

open Chromosome

variable {ε : GeneType} {m n : ℕ}

local notation "type4X" => Gene.ofRank m GeneType.NonPolarized + Gene.ofRank n GeneType.NonPolarized
local notation "type4Y" => Gene.ofRank (m - 1) ε + Gene.ofRank (n + 1) (- ε)

local notation "type5X" => Gene.ofRank m GeneType.NonPolarized + Gene.ofRank n ε
local notation "type5Y" => Gene.ofRank (m - 1) ε + Gene.ofRank (n + 1) GeneType.NonPolarized

local notation "type6X" => Gene.ofRank m ε + Gene.ofRank n GeneType.NonPolarized
local notation "type6Y" => Gene.ofRank (m - 1) GeneType.NonPolarized + Gene.ofRank (n + 1) ε

local notation "type7X" => Gene.ofRank m ε + Gene.ofRank n (- ε)
local notation "type7Y" => Gene.ofRank (m - 1) GeneType.NonPolarized +
  Gene.ofRank (n + 1) GeneType.NonPolarized

local notation "type8X" => Gene.ofRank m ε + Gene.ofRank n ε
local notation "type8Y" => Gene.ofRank (m - 2) ε + Gene.ofRank (n + 2) ε

#exit

section Aux

section type4_isMutation

lemma mutation_type4_ne (h_le : m ≤ n) (hm : 1 ≤ m) : type4X ≠ type4Y := by
  sorry

lemma mutation_type4_iterate_signature_eq (hε : ε ≠ .NonPolarized)
  (h_le : m ≤ n) (hm : 1 ≤ m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (m + k) .NonPolarized + Gene.ofRank (n + k) .NonPolarized)).signature =
    (prime^[i] (Gene.ofRank (m + k - 1) ε + Gene.ofRank (n + k + 1) (- ε))).signature := by
  sorry

lemma mutation_type4_signature_eq (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) (hm : 1 ≤ m) :
    signature type4X = signature type4Y := by
  sorry

lemma mutation_type4_le (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) : type4X ≤ type4Y := by
  sorry

end type4_isMutation

section type5_isMutation

lemma mutation_type5_ne (h_le : m < n) (hm : 1 ≤ m) : type5X ≠ type5Y := by
  sorry

lemma mutation_type5_iterate_signature_eq (hε : ε ≠ .NonPolarized)
  (h_le : m < n) (hm : 1 ≤ m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (m + k) .NonPolarized + Gene.ofRank (n + k) ε)).signature =
    (prime^[i] (Gene.ofRank (m + k - 1) ε + Gene.ofRank (n + k + 1) .NonPolarized)).signature := by
  sorry

lemma mutation_type5_signature_eq (hε : ε ≠ .NonPolarized) (h_le : m < n) (hm : 1 ≤ m) :
    signature type5X = signature type5Y := by
  sorry

lemma mutation_type5_le (hε : ε ≠ .NonPolarized) (h_le : m < n) : type5X ≤ type5Y := by
  sorry

end type5_isMutation

section type6_isMutation

lemma mutation_type6_ne (h_le : m < n) (hm : 1 ≤ m) : type6X ≠ type6Y := by
  sorry

lemma mutation_type6_iterate_signature_eq (hε : ε ≠ .NonPolarized)
  (h_le : m < n) (hm : 1 ≤ m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (m + k) ε + Gene.ofRank (n + k) .NonPolarized)).signature =
    (prime^[i] (Gene.ofRank (m + k - 1) .NonPolarized + Gene.ofRank (n + k + 1) ε)).signature := by
  sorry

lemma mutation_type6_signature_eq (hε : ε ≠ .NonPolarized) (h_le : m < n) (hm : 1 ≤ m) :
    signature type6X = signature type6Y := by
  sorry

lemma mutation_type6_le (hε : ε ≠ .NonPolarized) (h_le : m < n) : type6X ≤ type6Y := by
  sorry

end type6_isMutation

section type7_isMutation

lemma mutation_type7_ne (h_le : m ≤ n) (hm : 1 ≤ m) : type7X ≠ type7Y := by
  sorry

lemma mutation_type7_iterate_signature_eq (hε : ε ≠ .NonPolarized)
  (h_le : m ≤ n) (hm : 1 ≤ m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (m + k) ε + Gene.ofRank (n + k) (- ε))).signature =
    (prime^[i] (Gene.ofRank (m + k - 1) .NonPolarized +
      Gene.ofRank (n + k + 1) .NonPolarized)).signature := by
  sorry

lemma mutation_type7_signature_eq (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) (hm : 1 ≤ m) :
    signature type7X = signature type7Y := by
  sorry

lemma mutation_type7_le (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) : type7X ≤ type7Y := by
  sorry

end type7_isMutation

section type8_isMutation

lemma mutation_type8_ne (h_le : m ≤ n) (hm : 1 < m) : type8X ≠ type8Y := by
  sorry

lemma mutation_type8_iterate_signature_eq (hε : ε ≠ .NonPolarized)
  (h_le : m ≤ n) (hm : 1 < m) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (m + k) ε + Gene.ofRank (n + k) ε)).signature =
    (prime^[i] (Gene.ofRank (m + k - 2) ε + Gene.ofRank (n + k + 2) ε)).signature := by
  sorry

lemma mutation_type8_signature_eq (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) (hm : 1 < m) :
    signature type8X = signature type8Y := by
  sorry

lemma mutation_type8_le (hε : ε ≠ .NonPolarized) (h_le : m ≤ n) (hm : 1 < m) :
    type8X ≤ type8Y := by
  sorry

end type8_isMutation

end Aux

open Variety

namespace MixA

variable (hε : ε ≠ .NonPolarized)

noncomputable section type4

variable (hle : m ≤ n) (hm : 1 ≤ m)

def X4 : Mix (Pi, Lambda) := by
  use type4X
  have hle := hle
  have hm := hm
  have hε := hε
  sorry

def X4' : Mix (Lambda, Pi) := by
  use type4X
  have hle := hle
  have hm := hm
  have hε := hε
  sorry

lemma X4_eq : X4 hε hle hm =
  Gene.ofRank m .NonPolarized + Gene.ofRank n .NonPolarized := rfl

lemma X4'_eq : X4' hε hle hm =
  Gene.ofRank m .NonPolarized + Gene.ofRank n .NonPolarized := rfl

def Y4 : Mix (Pi, Lambda) := by
  use type4Y
  have hle := hle
  have hm := hm
  have hε := hε
  sorry

def Y4 : Mix (Pi, Lambda) := by
  use type4Y
  have hle := hle
  have hm := hm
  have hε := hε
  sorry

#exit

lemma X1_eq : X1 hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n (- ε) := rfl

def Y1 : Pi := by
  use type1Y
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
  use type2X
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRank (le_of_lt hm)],
    by rwa [IsPolarized_ofRank ((le_of_lt hm).trans hle)]⟩

lemma X2_eq : X2 hε hle hm =
  Gene.ofRank m ε + Gene.ofRank n ε := rfl

def Y2 : Pi := by
  use type2Y
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
  use type3X
  rw [mem_Pi_iff, IsPolarized_iff_add]
  exact ⟨by rwa [IsPolarized_ofRankAlt hm], by
    rwa [IsPolarized_ofRankAlt (hm.trans hle),
      ← GeneType.neg_ne_nonPolarized_iff]⟩

lemma X3_eq : X3 hε hle hm =
  Gene.ofRankAlt m ε + Gene.ofRankAlt n (- ε) := rfl

def Y3 : Pi := by
  use type3Y
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

lemma Primitive.isMutation {X Y : Pi} (h : Pi.Primitive X Y) :
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

lemma Step.isMutation {X Y : Pi} (h : Pi.Step X Y) :
    IsMutation X Y := by
  cases h with
  | mk X Y Z h =>
    exact .add_right _ (Pi.Primitive.isMutation h)

lemma Step.add_right_pi (W : Variety.Pi) {A B : Variety.Pi}
    (h : Pi.Step A B) : Pi.Step (A + W) (B + W) := by
  cases h with
  | mk X Y Z hPrim =>
    rw [add_assoc, add_assoc]
    exact Pi.Step.mk X Y (Z + W) hPrim

end Pi
