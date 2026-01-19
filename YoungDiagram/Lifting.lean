import Mathlib
import YoungDiagram.Mutations

open Finsupp

noncomputable def liftGene (g : Gene) : Chromosome :=
  Gene.ofRank (g.rank + 1) g.type

namespace Chromosome

noncomputable def lift : Chromosome →+ Chromosome where
  toFun c := c.sum (fun g count ↦ count • liftGene g)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ zero_nsmul _)
    fun _ _ _ ↦ add_nsmul ..

abbrev below (c : Chromosome) (k : ℕ) : Chromosome := c.filter (·.rank ≤ k)

abbrev above (c : Chromosome) (k : ℕ) : Chromosome := c.filter (k < ·.rank)

lemma rankDecomposition (c : Chromosome) (k : ℕ) :
    c = c.below k + c.above k := by
  simp [below, above]
  conv =>
    enter [2, 2, 1, a]
    rw [lt_iff_not_ge]
  rw [filter_pos_add_filter_neg]

lemma prime_elim (c : Chromosome) (k : ℕ) :
    prime^[k] c = prime^[k] (c.above k) := by
  nth_rw 1 [rankDecomposition c k]
  simp only [iterate_map_add, add_eq_right]
  induction c using Finsupp.induction with
  | zero => simp [below, filter_zero]
  | single_add g n f hg hn hf =>
    simp [below]
    by_cases hg_rank : g.rank ≤ k
    · rw [filter_single_of_pos, ← Gene.ofRank_eq_gene', iterate_map_nsmul]
      · refine ⟨?_, hf⟩
        rw [IsAddTorsionFree.nsmul_eq_zero_iff, prime_ofRank_it,
          Nat.sub_eq_zero_of_le hg_rank, Gene.ofRank_zero]
        exact Or.inl rfl
      exact hg_rank
    rw [filter_single_of_neg, iterate_map_zero]
    · exact ⟨rfl, hf⟩
    exact hg_rank

lemma prime_lift_LeftInverse : Function.LeftInverse prime lift := by
  intro x
  induction x using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add a m f ha hm hf =>
    rw [map_add, map_add, hf, add_left_inj]
    simp [prime, lift, liftGene, primeGene]
    split_ifs with h
    · rw [← Gene.ofRank_eq_gene', h, Gene.ofRank_zero, smul_zero]
    · rfl

lemma prime_lift_LeftInverse_it (k : ℕ) :
    Function.LeftInverse prime^[k] lift^[k] :=
  Function.LeftInverse.iterate prime_lift_LeftInverse k

end Chromosome

namespace Lifting

open Chromosome

lemma IsMutation_lift (X Y : Chromosome) (h : IsMutation X Y) :
    IsMutation X.lift Y.lift where
  le := by
    intro k
    have hle := h.le k
    by_cases hk : k = 0
    · subst hk
      rw [Function.iterate_zero, id_eq, id_eq] at hle ⊢
      sorry
    sorry
  ne := sorry
  sign_eq := sorry

lemma IsMutation_lifting (X Y : Chromosome) (k : ℕ) (h : IsMutation X Y) :
    IsMutation (lift^[k] X) (lift^[k] Y) := by
  induction k with
  | zero =>
    rwa [Function.iterate_zero, id_eq, id_eq]
  | succ n hn =>
    rw [add_comm, Function.iterate_add_apply, Function.iterate_add_apply,
      Function.iterate_one]
    set A := lift^[n] X
    set B := lift^[n] Y
    sorry

variable {X U : Chromosome} {k : ℕ} (h : IsMutation (prime^[k] X) U)

local notation "Z" => X.below k + lift^[k] U

lemma Z_isMutation : IsMutation X Z := by
  nth_rw 1 [rankDecomposition X k, add_comm (X.below k),
    add_comm (X.below k), IsMutation_iff_add]
  sorry


theorem lifting_property :
  IsMutation X Z ∧ prime^[k] Z = U ∧
    ∀ i ≤ k, (prime^[i] X).signature = (prime^[i] Z).signature := sorry

end Lifting
