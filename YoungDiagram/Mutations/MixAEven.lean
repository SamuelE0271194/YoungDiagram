import YoungDiagram

open Chromosome

variable {ε : GeneType} {m n : ℕ}

-- Φ = (Λ, Π): g ranks even, g^ε ranks odd.

local notation "type4X" =>
  Gene.ofRank (2 * m + 2) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized
local notation "type4Y" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 3) (- ε)

local notation "type5X" =>
  Gene.ofRank (2 * m + 2) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) ε
local notation "type5Y" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 4) GeneType.NonPolarized

local notation "type6X" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized
local notation "type6Y" =>
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 3) ε

local notation "type7X" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 1) (- ε)
local notation "type7Y" =>
  Gene.ofRank (2 * m) GeneType.NonPolarized +
  Gene.ofRank (2 * n + 2) GeneType.NonPolarized

local notation "type8X" =>
  Gene.ofRank (2 * m + 3) ε +
  Gene.ofRank (2 * n + 3) ε
local notation "type8Y" =>
  Gene.ofRank (2 * m + 1) ε +
  Gene.ofRank (2 * n + 5) ε

variable (h_le : m ≤ n)

include h_le

section Aux

section type4_isMutation

lemma mutation_type4_ne : type4X ≠ type4Y := by
  intro h
  replace h := congr_arg (· ⟨2 * m + 2, .NonPolarized, by omega⟩) h
  have h_n : 2 * n + 2 ≠ 0 := by omega
  have h_m : 2 * m + 2 ≠ 0 := by omega
  simp only [Gene.ofRank_def, h_m, ↓reduceDIte, h_n, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_eq_same, Nat.add_eq_zero_iff, one_ne_zero, and_false] at h
  rw [dif_neg (by omega), Finsupp.single_apply] at h
  split_ifs at h <;> (simp [Finsupp.single_apply] at h; grind)

lemma mutation_type4_iterate_signature_eq (hε : ε ≠ .NonPolarized) (i k : ℕ) (hi : i ≤ k) :
    (prime^[i] (Gene.ofRank (2 * m + 2 + k) .NonPolarized +
      Gene.ofRank (2 * n + 2 + k) .NonPolarized)).signature =
    (prime^[i] (Gene.ofRank (2 * m + 1 + k) ε + Gene.ofRank (2 * n + 3 + k) (- ε))).signature := by
  rw [iterate_map_add, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    prime_iterate_ofRank, prime_iterate_ofRank, map_add, map_add,
    signature_ofRank_nonPolarized, signature_ofRank_nonPolarized,
    signature_ofRank_eq₂ (k := 2 * n + 3 + k - i) (by omega) (GeneType.neg_ne_nonPolarized_iff.1 hε)]
  sorry

lemma mutation_type4_signature_eq (hε : ε ≠ .NonPolarized) :
    signature type4X = signature type4Y := by
  sorry

lemma mutation_type4_le (hε : ε ≠ .NonPolarized) : type4X ≤ type4Y := by
  sorry

end type4_isMutation

end Aux
