import YoungDiagram.Chromosome.Rank

open Finsupp

namespace Chromosome

section lift

noncomputable def liftGene (g : Gene) : Chromosome :=
  Gene.ofRank (g.rank + 1) g.type

noncomputable def lift : Chromosome →+ Chromosome := weight liftGene

lemma lift_def {X : Chromosome} : X.lift = X.sum (fun g count ↦ count • liftGene g) := rfl

lemma lift_ofRank {n : ℕ} {ε : GeneType} (hn : n ≠ 0) :
    (Gene.ofRank n ε).lift = Gene.ofRank (n + 1) ε := by
  rw [lift_def, Gene.ofRank_def]
  simp only [hn, ↓reduceDIte, zero_nsmul, sum_single_index, one_smul]; rfl

lemma lift_iterate_ofRank {k n : ℕ} {ε : GeneType} (hn : n ≠ 0) :
    lift^[k] (Gene.ofRank n ε) = Gene.ofRank (n + k) ε := by
  induction k with
  | zero => rfl
  | succ k hk => rw [Function.iterate_succ_apply', hk,
    lift_ofRank (by omega), add_assoc]

lemma lift_prime_iterate_ofRank {k n : ℕ} {ε : GeneType} (h : k < n) :
    lift^[k] (prime^[k] (Gene.ofRank n ε)) = Gene.ofRank n ε := by
  rw [prime_iterate_ofRank, lift_iterate_ofRank (Nat.sub_ne_zero_iff_lt.2 h),
    Nat.sub_add_cancel h.le]

def below (k : ℕ) : Chromosome →+ Chromosome where
  toFun c := c.filter (·.rank ≤ k)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

lemma below_def {k : ℕ} {X : Chromosome} :
  X.below k = X.filter (·.rank ≤ k) := rfl

lemma support_of_below_one {X : Chromosome} {g : Gene}
    (hg : g ∈ (X.below 1).support) : g.rank = 1 := by
  by_contra!
  rw [mem_support_iff, below_def, filter_apply_neg] at hg
  · exact false_of_ne hg
  · exact Nat.lt_le_asymm <| Nat.lt_of_le_of_ne g.rank_pos this.symm

lemma below_maxRank {X : Chromosome} : X.below X.maxRank = X := by
  rw [below_def, filter_eq_self_iff]
  exact fun _ hg ↦ Finset.le_sup <| mem_support_iff.2 hg

def above (k : ℕ) : Chromosome →+ Chromosome where
  toFun c := c.filter (k < ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

lemma above_def {k : ℕ} {X : Chromosome} :
  X.above k = X.filter (k < ·.rank) := rfl

lemma above_below_eq_zero {k : ℕ} {X : Chromosome} :
    (X.above k).below k = 0 := by
  rw [above_def, below_def, filter_eq_zero_iff]
  intro _ hx
  rw [filter_apply, if_neg (Nat.not_lt.2 hx)]

lemma rank_decomposition (X : Chromosome) (k : ℕ) :
    X = X.below k + X.above k := by
  simp only [below, AddMonoidHom.coe_mk, ZeroHom.coe_mk, above]
  conv =>
    enter [2, 2, 1, a]
    rw [lt_iff_not_ge]
  rw [filter_add_filter_not]

lemma prime_iterate_eq_prime_iterate_above (X : Chromosome) (k : ℕ) :
    prime^[k] X = prime^[k] (X.above k) := by
  nth_rw 1 [rank_decomposition X k]
  simp only [iterate_map_add, add_eq_right]
  induction X using Finsupp.induction with
  | zero => simp [below, filter_zero]
  | single_add g n f hg hn hf =>
    simp only [below, AddMonoidHom.coe_mk, ZeroHom.coe_mk, filter_add, iterate_map_add, add_eq_zero]
    by_cases hg_rank : g.rank ≤ k
    · rw [filter_single_of_pos, ← Gene.ofRank_eq_gene_smul, iterate_map_nsmul]
      · refine ⟨?_, hf⟩
        rw [nsmul_eq_zero_iff, prime_iterate_ofRank,
          Nat.sub_eq_zero_of_le hg_rank, Gene.ofRank_zero]
        exact Or.inl rfl
      exact hg_rank
    · rw [filter_single_of_neg, iterate_map_zero]
      · exact ⟨rfl, hf⟩
      exact hg_rank

lemma prime_lift_leftInverse : Function.LeftInverse prime lift := by
  intro x
  induction x using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add a m f ha hm hf =>
    rw [map_add, map_add, hf, add_left_inj, ← Gene.ofRank_eq_gene_smul,
      map_nsmul, map_nsmul]
    by_cases ha : a.rank = 0
    · rw [ha, Gene.ofRank_zero, map_zero, map_zero]
    · rw [lift_ofRank ha, prime_ofRank, Nat.succ_sub_one]

lemma prime_lift_leftInverse_iterate (k : ℕ) :
    Function.LeftInverse prime^[k] lift^[k] :=
  Function.LeftInverse.iterate prime_lift_leftInverse k

lemma prime_below {k n : ℕ} {X : Chromosome} (h : n ≤ k) :
    prime^[k] (X.below n) = 0 := by
  induction X using Finsupp.induction with
  | zero => rw [map_zero, iterate_map_zero]
  | single_add a m f ha hm hf =>
    rw [map_add, iterate_map_add, hf, add_zero, below_def]
    by_cases ha : a.rank ≤ n
    · have eq : a.rank - k = 0 := by omega
      rwa [filter_single_of_pos, ← Gene.ofRank_eq_gene_smul, iterate_map_nsmul,
        prime_iterate_ofRank, nsmul_eq_zero_iff_right hm, eq,
        Gene.ofRank_zero]
    · rwa [filter_single_of_neg, iterate_map_zero]

lemma lift_prime {k : ℕ} {X Y : Chromosome} :
    prime^[k] X = Y ↔ X = lift^[k] Y + X.below k := by
  constructor <;> intro h
  · induction X using Finsupp.induction generalizing Y
    · rw [iterate_map_zero] at h
      rw [← h, iterate_map_zero, map_zero, add_zero]
    · expose_names
      rw [iterate_map_add] at h
      nth_rw 1 [@h_3 (prime^[k] f) rfl, ← h, add_comm, add_comm _ (prime^[k] f),
        iterate_map_add, add_assoc, add_assoc, add_right_inj, map_add,
        ← add_assoc, add_comm _ ((below k) f), add_right_inj, below_def]
      by_cases ha : a.rank ≤ k
      · have eq : a.rank - k = 0 := by omega
        rwa [filter_single_of_pos, ← Gene.ofRank_eq_gene_smul,
          iterate_map_nsmul, iterate_map_nsmul, prime_iterate_ofRank, eq,
          Gene.ofRank_zero, iterate_map_zero, nsmul_zero, zero_add]
      · rwa [filter_single_of_neg, add_zero, ← Gene.ofRank_eq_gene_smul,
          iterate_map_nsmul, iterate_map_nsmul, prime_iterate_ofRank,
          lift_iterate_ofRank (Nat.sub_ne_zero_of_lt <| Nat.lt_of_not_le ha),
          Nat.sub_add_cancel (Nat.le_of_not_ge ha)]
  · rw [h, iterate_map_add, prime_lift_leftInverse_iterate k,
      prime_below le_rfl, add_zero]

lemma above_eq_lift_prime {X : Chromosome} :
    X.above 1 = lift X.prime := by
  have h1 : (X.above 1).prime = X.prime :=
    (prime_iterate_eq_prime_iterate_above X 1).symm
  have h2 := lift_prime.1 (Function.iterate_one prime ▸ h1)
  simpa only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    above_below_eq_zero, add_zero] using h2

lemma above_one_eq_of_prime_eq {X Y : Chromosome}
    (hprime : X.prime = Y.prime) : X.above 1 = Y.above 1 := by
  rw [above_eq_lift_prime, above_eq_lift_prime, hprime]

end lift

end Chromosome
