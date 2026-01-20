import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise
import YoungDiagram.Chromosome

inductive VarietyLabel
  | pi
  | lambda
  | mix_lambda_pi
  | mix_pi_lambda
  | mix_2lambda_pi
  | mix_pi_2lambda
deriving DecidableEq, Repr

def VarietyLabel.prime : VarietyLabel → VarietyLabel
  | pi => pi
  | lambda => lambda
  | mix_lambda_pi => mix_pi_lambda
  | mix_pi_lambda => mix_lambda_pi
  | mix_2lambda_pi => mix_pi_2lambda
  | mix_pi_2lambda => mix_2lambda_pi

abbrev variety := AddSubmonoid Chromosome

open Finsupp

namespace Chromosome

abbrev o (X : Chromosome) : Chromosome := X.filter (Odd  ·.rank)
abbrev e (X : Chromosome) : Chromosome := X.filter (Even ·.rank)

def IsOdd (X : Chromosome) : Prop  := X.o = X

@[simp] lemma IsOdd_def {X : Chromosome} :
  X.IsOdd ↔ X.filter (Odd  ·.rank) = X := .rfl

def IsEven (X : Chromosome) : Prop := X.e = X

@[simp] lemma IsEven_def {X : Chromosome} :
  X.IsEven ↔ X.filter (Even ·.rank) = X := .rfl

lemma parityDecomposition (X : Chromosome) : X = X.o + X.e := by
  simp [o, e]
  conv =>
    enter [2, 2, 1, a]
    rw [← Nat.not_odd_iff_even]
  rw [filter_pos_add_filter_neg]

def IsPolarized (X : Chromosome) : Prop :=
  X.filter (·.type ≠ .NonPolarized) = X

@[simp] lemma IsPolarized_def {X : Chromosome} :
  X.IsPolarized ↔ X.filter (·.type ≠ .NonPolarized) = X := .rfl

def IsNonPolarized (X : Chromosome) : Prop :=
  X.filter (·.type = .NonPolarized) = X

@[simp] lemma IsNonPolarized_def {X : Chromosome} :
  X.IsNonPolarized ↔ X.filter (·.type = .NonPolarized) = X := .rfl

lemma IsPolarized_add {X Y : Chromosome} (hX : X.IsPolarized)
    (hY : Y.IsPolarized) : (X + Y).IsPolarized := by
  simp at *
  rw [hX, hY]

lemma IsNonPolarized_add {X Y : Chromosome} (hX : X.IsNonPolarized)
    (hY : Y.IsNonPolarized) : (X + Y).IsNonPolarized := by
  simp at *
  rw [hX, hY]

lemma IsPolarized_single {g : Gene} :
    IsPolarized (single g 1) ↔ g.type ≠ .NonPolarized := by
  simp
  by_cases hg : g.type = .NonPolarized
  · constructor <;> intro h
    · symm at h
      rw [filter_single_of_neg _ (fun a ↦ a hg), single_eq_zero] at h
      tauto
    · tauto
  · exact ⟨fun _ ↦ hg, fun _ ↦ filter_single_of_pos _ hg⟩

lemma IsNonPolarized_single {g : Gene} :
    IsNonPolarized (single g 1) ↔ g.type = .NonPolarized := by
  simp
  by_cases hg : g.type = .NonPolarized
  · exact ⟨fun _ ↦ hg, fun _ ↦ filter_single_of_pos _ hg⟩
  · constructor <;> intro h
    · symm at h
      rw [filter_single_of_neg, single_eq_zero] at h <;> tauto
    · tauto

lemma IsPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank_def]
  split_ifs
  · omega
  · rw [IsPolarized_single]

lemma IsPolarized_ofRank' {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank' k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank'_def, IsPolarized_ofRank hk,
    GeneType.neg_one_pow_smul]
  split_ifs
  · rfl
  · exact GeneType.nonpolarized_iff_neg_non.symm


lemma IsNonPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsNonPolarized ↔ ε = .NonPolarized := by
  rw [Gene.ofRank_def]
  split_ifs
  · omega
  · rw [IsNonPolarized_single]

def Pi : variety where
  carrier := {X : Chromosome | IsPolarized X}
  add_mem' ha hb := by
    simp at *
    rw [ha, hb]
  zero_mem' := by simp [filter_zero]

lemma mem_Pi_iff {X : Chromosome} : X ∈ Pi ↔ X.IsPolarized := .rfl

def Lambda : variety where
  carrier := {X : Chromosome | IsNonPolarized X}
  add_mem' ha hb := by
    simp at *
    rw [ha, hb]
  zero_mem' := by simp [filter_zero]

lemma mem_Lambda_iff {X : Chromosome} : X ∈ Lambda ↔ X.IsNonPolarized := .rfl

def Mix (v : variety × variety) : variety where
  carrier := {X : Chromosome | X.e ∈ v.1 ∧ X.o ∈ v.2}
  add_mem' ha hb := by
    simp at *
    exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := by simp [filter_zero]

lemma mem_Mix_iff {X : Chromosome} {v : variety × variety} :
  X ∈ Mix v ↔ X.e ∈ v.1 ∧ X.o ∈ v.2 := .rfl

end Chromosome

open Chromosome Pointwise

noncomputable def VarietyLabel.carrier : VarietyLabel → variety
  | pi => Pi
  | lambda => Lambda
  | mix_lambda_pi => Mix (Lambda, Pi)
  | mix_pi_lambda => Mix (Pi, Lambda)
  | mix_2lambda_pi => Mix (2 • Lambda, Pi)
  | mix_pi_2lambda => Mix (Pi, 2 • Lambda)

instance : Membership Chromosome VarietyLabel := ⟨fun x v ↦ v ∈ x.carrier⟩
