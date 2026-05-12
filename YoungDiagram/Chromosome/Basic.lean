import Mathlib.Algebra.Order.Monoid.Prod
import YoungDiagram.Gene

open Finsupp

lemma Finsupp.support_add_eq' {α M : Type*} [AddCommMonoid α] [PartialOrder α]
  [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α] [AddLeftMono α]
  {N₁ N₂ : M →₀ α} [DecidableEq M] :
    (N₁ + N₂).support = (N₁.support ∪ N₂.support : Finset M) := by
  refine le_antisymm support_add (Finset.le_iff_subset.2 (Finset.union_subset ?_ ?_))
  · exact support_mono le_self_add
  · exact support_mono <| CanonicallyOrderedAdd.le_add_self ..

/--
A chromosome is a non-negative integral linear combination of genes.
It forms a free commutative monoid on the set of genes.
Formalized as `Finsupp` (finite support functions) from `Gene` to `ℕ`.
-/
abbrev Chromosome := Gene →₀ ℕ

noncomputable abbrev Gene.ofRank (n : ℕ) (ε : GeneType) : Chromosome :=
  if h : n = 0 then 0
  else single ⟨n, ε, Nat.pos_of_ne_zero h⟩ 1

noncomputable abbrev Gene.ofRankAlt (n : ℕ) (ε : GeneType) : Chromosome :=
  Gene.ofRank n (Int.negOnePow (n - 1) • ε)

lemma Gene.ofRank_is_gene {n : ℕ} (hn : n ≠ 0) (ε : GeneType) :
    Gene.ofRank n ε = Finsupp.single ⟨n, ε, Nat.pos_of_ne_zero hn⟩ 1 := by
  rw [Gene.ofRank, dif_neg hn]

lemma Gene.ofRank_def {n : ℕ} {ε : GeneType} :
  Gene.ofRank n ε = if h : n = 0 then 0
    else single ⟨n, ε, Nat.pos_of_ne_zero h⟩ 1 := rfl

lemma Gene.ofRankAlt_def {n : ℕ} {ε : GeneType} :
  Gene.ofRankAlt n ε = Gene.ofRank n (Int.negOnePow (n - 1) • ε) := rfl

@[simp] lemma Gene.ofRank_zero {ε : GeneType} : Gene.ofRank 0 ε = 0 := rfl

@[simp] lemma Gene.ofRankAlt_zero {ε : GeneType} : Gene.ofRankAlt 0 ε = 0 := rfl

lemma Gene.ofRankAlt_def' {n : ℕ} {ε : GeneType} :
    Gene.ofRankAlt n ε = if Even n then Gene.ofRank n (-ε) else Gene.ofRank n ε := by
  obtain (h1 | h1) := Nat.even_or_odd n
  · simp [h1, Int.negOnePow_odd, Gene.ofRankAlt_def]
  · replace h1 := Nat.not_even_iff_odd.2 h1
    rw [Gene.ofRankAlt_def, Int.negOnePow_even,
      ite_cond_eq_false _ _ (eq_false h1), one_smul]
    simp only [Int.even_coe_nat, h1, not_false_eq_true, Int.even_sub_one]

lemma Gene.ofRankAlt_positive {k : ℕ} :
  Gene.ofRankAlt k GeneType.Positive = if Even k then
    Gene.ofRank k GeneType.Negative else Gene.ofRank k GeneType.Positive :=
  Gene.ofRankAlt_def'

lemma Gene.ofRankAlt_negative {k : ℕ} :
  Gene.ofRankAlt k GeneType.Negative = if Even k then
    Gene.ofRank k GeneType.Positive else Gene.ofRank k GeneType.Negative :=
  Gene.ofRankAlt_def'

lemma Gene.ofRank_eq_gene {g : Gene} :
    Gene.ofRank g.rank g.type = single g 1 := by
  rw [Gene.ofRank_def]
  split_ifs with h
  · absurd h; exact Nat.ne_zero_of_lt g.rank_pos
  · rfl

lemma Gene.ofRank_eq_gene_smul {g : Gene} {m : ℕ} :
    m • Gene.ofRank g.rank g.type = single g m := by
  rw [← smul_single_one, ofRank_eq_gene]

lemma Gene.ofRankAlt_eq_gene {n : ℕ} (hn : 1 ≤ n) {ε : GeneType} :
    Gene.ofRankAlt n ε = single ⟨n, Int.negOnePow (n - 1) • ε, hn⟩ 1 := by
  simp only [dif_neg (by omega : n ≠ 0)]

lemma Gene.ofRankAlt_shift_negOnePow_smul {n k : ℕ} {ε : GeneType} :
  Gene.ofRankAlt (n + k) (Int.negOnePow k • ε) =
    Gene.ofRank (n + k) (Int.negOnePow (n - 1) • ε) := by
  unfold Gene.ofRankAlt
  congr 1
  rw [GeneType.negOnePow_smul_smul, Nat.cast_add, sub_add_eq_add_sub,
    add_assoc, ← two_mul, add_comm, add_sub_assoc, Int.negOnePow_add,
    Int.negOnePow_two_mul, one_mul]

namespace Chromosome

lemma sub_single_add_single_eq {X : Chromosome} {g : Gene} (hg : 0 < X g) :
    X - Finsupp.single g 1 + Finsupp.single g 1 = X :=
  Finsupp.sub_add_single_one_cancel (Nat.ne_zero_of_lt hg)

end Chromosome
