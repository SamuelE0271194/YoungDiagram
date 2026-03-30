import YoungDiagram.Variety.Basic

open Finsupp

namespace Chromosome

section nonpolarized

def IsNonPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type = .NonPolarized)

lemma IsNonPolarized_def {X : Chromosome} :
  X.IsNonPolarized ↔ X.filter (·.type = .NonPolarized) = X := IsFiltered_def

lemma IsNonPolarized_def' {X : Chromosome} :
  X.IsNonPolarized ↔ ∀ g ∈ X.support, g.type = .NonPolarized := IsFiltered_def'

lemma IsNonPolarized_zero : IsNonPolarized 0 := IsFiltered_zero

lemma IsNonPolarized_single {g : Gene} {n : ℕ} (hn : n ≠ 0) :
  IsNonPolarized (single g n) ↔ g.type = .NonPolarized := IsFiltered_single hn

lemma IsNonPolarized_filter {X : Chromosome} {q : Gene → Prop} [DecidablePred q]
  (h : X.IsNonPolarized) : IsNonPolarized (X.filter q) := IsFiltered_filter h

lemma IsNonPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsNonPolarized ↔ ε = .NonPolarized := by
  rw [Gene.ofRank_def, dif_neg (by omega)]
  exact IsNonPolarized_single Nat.one_ne_zero

lemma IsNonPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsNonPolarized ↔ X.IsNonPolarized ∧ Y.IsNonPolarized := IsFiltered_iff_add

lemma IsNonPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_nsmul hn

lemma IsNonPolarized_iff_lift {X : Chromosome} :
  X.lift.IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

lemma IsNonPolarized_iff_iterate_lift {X : Chromosome} {k : ℕ} :
  (lift^[k] X).IsNonPolarized ↔ X.IsNonPolarized :=
    IsFiltered_iff_iterate_lift (fun _ ↦ .rfl)

end nonpolarized

end Chromosome

namespace Variety

open Chromosome Pointwise

section Lambda

def Lambda : Variety := varietyOfFilter (·.type = .NonPolarized)

lemma mem_Lambda_iff {X : Chromosome} :
  X ∈ Lambda ↔ IsNonPolarized X := mem_varietyOfFilter_iff

lemma mem_Lambda_iff_add {X Y : Chromosome} :
  (X + Y) ∈ Lambda ↔ X ∈ Lambda ∧ Y ∈ Lambda := IsNonPolarized_iff_add

lemma prime_Lambda : Lambda.prime = Lambda := prime_varietyOfFilter (fun _ ↦ .rfl)

lemma parityDecomp_mem_smul_Lambda {X : Chromosome} {n : ℕ} (h : X ∈ n • Lambda) :
  oddPart X ∈ n • Lambda ∧ evenPart X ∈ n • Lambda :=
  ⟨filter_mem_smul_varietyOfFilter (Odd ·.rank) h,
    filter_mem_smul_varietyOfFilter (Even ·.rank) h⟩

lemma parityDecomp_mem_Lambda {X : Chromosome} (h : X ∈ Lambda) :
    oddPart X ∈ Lambda ∧ evenPart X ∈ Lambda :=
  ⟨IsFiltered_filter h, IsFiltered_filter h⟩

lemma prime_mem_Lambda {X : Chromosome} (hX : X ∈ Lambda) : X.prime ∈ Lambda :=
  prime_mem_varietyOfFilter (fun _ ↦ .rfl) hX

noncomputable def prime_on_Lambda (X : Lambda) : Lambda := ⟨X.1.prime, prime_mem_Lambda X.2⟩

lemma prime_on_Lambda_iterate (X : Lambda) (k : ℕ) :
    (prime_on_Lambda^[k] X).1 = Chromosome.prime^[k] X :=
  prime_on_varietyOfFilter_iterate (fun _ ↦ .rfl) X k

lemma prime_mem_Lambda_iterate {X : Chromosome} (hX : X ∈ Lambda) {k : ℕ} :
    Chromosome.prime^[k] X ∈ Lambda :=
  prime_mem_varietyOfFilter_iterate (fun _ ↦ .rfl) hX

end Lambda

end Variety
