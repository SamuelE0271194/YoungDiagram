import YoungDiagram.Mutations

open Chromosome Variety Finsupp

lemma cond_15_6_ofRank (k : ℕ) {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).prime.signature - (Gene.ofRank k ε).prime.prime.signature ≤
    ((Gene.ofRank k ε).signature - (Gene.ofRank k ε).prime.signature).swap := by
  rw [prime_ofRank, prime_ofRank]
  by_cases hk : 1 ≤ k - 1
  · rw [signature_ofRank_eq' hk hε, add_sub_cancel_left]
    replace hk : 2 ≤ k := by omega
    rw [signature_ofRank_eq₂ hk hε, show k - 1 - 1 = k - 2 by rfl, add_comm,
      add_sub_assoc, sub_add_cancel_left, Prod.swap_add, Prod.swap_prod_mk,
      Prod.swap_neg, le_add_neg_iff_add_le]
    split_ifs
    · rw [← signature_ofRank_swap, neg_neg, signature_ofRank, signature_ofRank,
        dif_neg Nat.one_ne_zero, dif_neg Nat.one_ne_zero, add_comm, Gene.signature_sum_le_rank]
      rfl
    · rw [← signature_ofRank_swap, signature_ofRank, signature_ofRank,
        dif_neg Nat.one_ne_zero, dif_neg Nat.one_ne_zero, Gene.signature_sum_le_rank]
      rfl
  · obtain (hk | hk) : k = 1 ∨ k = 0 := by omega
    all_goals subst hk
    · simp only [tsub_self, Gene.ofRank_zero, map_zero, zero_tsub, sub_self, sub_zero]
      exact Prod.mk_le_swap.2 (signature_nonneg _)
    · simp only [zero_le, Nat.sub_eq_zero_of_le, Gene.ofRank_zero, map_zero, sub_self,
        Prod.swap_zero, Std.le_refl]

lemma cond_15_6_Pi {Y : Chromosome} (hY : Y ∈ Pi) :
    Y.prime.signature - Y.prime.prime.signature ≤
    (Y.signature - Y.prime.signature).swap := by
  induction Y using Finsupp.induction with
  | zero => simp only [map_zero, sub_self, Prod.swap_zero, Std.le_refl]
  | single_add a b f ha hb hf => calc
    _ = (prime f).signature - (prime f).prime.signature +
        ((prime (single a b)).signature - (prime (single a b)).prime.signature) := by
      simp_rw [map_add, sub_add_eq_sub_sub]; ring
    _ ≤ (signature f - signature (Chromosome.prime f)).swap +
        ((prime (single a b)).signature - (prime (single a b)).prime.signature) :=
      add_le_add_left (hf (mem_Pi_iff_add.1 hY).2) _
    _ ≤ _ := by
      simp_rw [Prod.swap_sub, map_add, Prod.swap_add]
      rw [sub_eq_add_neg, add_comm (signature (single a b)).swap, add_sub_assoc, add_assoc]
      refine add_le_add_right ?_ (signature f).swap
      rw [sub_add_eq_sub_sub, sub_eq_add_neg _ (signature (Chromosome.prime f)).swap,
        add_comm]
      refine add_le_add_left ?_ (-(signature (Chromosome.prime f)).swap)
      simp_rw [← Gene.ofRank_eq_gene_smul, map_nsmul, Prod.smul_swap, ← smul_sub]
      have := (IsFiltered_single hb).1 <| mem_Pi_iff.1 (mem_Pi_iff_add.1 hY).1
      refine nsmul_le_nsmul_right ((cond_15_6_ofRank a.rank this).trans ?_) b
      rw [Prod.swap_sub]
