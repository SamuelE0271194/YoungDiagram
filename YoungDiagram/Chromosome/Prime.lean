import YoungDiagram.Chromosome.Signature

open Finsupp

namespace Chromosome

section prime

/--
The "prime" operation on a single gene $g$, denoted $g'$ in [Djoković 1980, (8.2)].
* If $g$ has rank $> 1$, $g'$ is a gene of the same type with rank $n-1$.
* If $g$ has rank $1$, $g'$ is the zero chromosome.
-/
noncomputable def primeGene (g : Gene) : Chromosome :=
  Gene.ofRank (g.rank - 1) g.type

lemma primeGene_def {g : Gene} :
  primeGene g = Gene.ofRank (g.rank - 1) g.type := rfl

/--
The "prime" operation extended linearly to all chromosomes: $X' = \sum m_i g_i'$.
This operation corresponds to taking the derivative of the chromosome.
-/
noncomputable def prime : Chromosome →+ Chromosome := weight primeGene

lemma prime_def {X : Chromosome} : X.prime = X.sum (fun g m ↦ m • primeGene g) := rfl

lemma prime_ofRank {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n ε).prime = Gene.ofRank (n - 1) ε := by
  by_cases hn : n = 0
  · simp only [hn, Gene.ofRank_zero, map_zero, zero_le, Nat.sub_eq_zero_of_le]
  rw [prime_def, Gene.ofRank_def]
  simp only [hn, ↓reduceDIte, zero_nsmul, sum_single_index, one_smul]
  rfl

lemma prime_ofRankAlt {n : ℕ} {ε : GeneType} :
    (Gene.ofRankAlt n ε).prime = Gene.ofRankAlt (n - 1) (-ε) := by
  by_cases hn : n = 0
  · simp only [hn, Gene.ofRank_zero, map_zero, zero_tsub]
  rw [Gene.ofRankAlt_def, Gene.ofRankAlt_def, prime_ofRank, GeneType.negOnePow_smul_neg,
    sub_add_cancel, Nat.cast_sub (by omega), Nat.cast_one]

lemma prime_ofRankAlt_positive {k : ℕ} : (Gene.ofRankAlt k GeneType.Positive).prime =
  Gene.ofRankAlt (k - 1) GeneType.Negative := prime_ofRankAlt

lemma prime_ofRankAlt_negative {k : ℕ} : (Gene.ofRankAlt k GeneType.Negative).prime =
  Gene.ofRankAlt (k - 1) GeneType.Positive := prime_ofRankAlt

lemma signature_prime_ofRankAlt_positive {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRankAlt k GeneType.Positive).signature -
    (Gene.ofRankAlt k GeneType.Positive).prime.signature = (1, 0) := by
  rw [prime_ofRankAlt_positive, signature_ofRankAlt_general hk (by decide)]
  simp only [GeneType.neg_positive, signature_ofRank_one_positive, add_sub_cancel_left]

lemma signature_prime_ofRankAlt_negative {k : ℕ} (hk : 1 ≤ k) :
    signature (Gene.ofRankAlt k GeneType.Negative) -
    signature (prime (Gene.ofRankAlt k GeneType.Negative)) = (0, 1) := by
  rw [prime_ofRankAlt_negative, signature_ofRankAlt_general hk (by decide)]
  simp only [GeneType.neg_negative, signature_ofRank_one_negative, add_sub_cancel_left]

lemma prime_single {n : ℕ} {g : Gene} :
    prime (single g n) = n • Gene.ofRank (g.rank - 1) g.type := by
  rw [← Gene.ofRank_eq_gene_smul, map_nsmul, prime_ofRank]

lemma prime_iterate_ofRank {k n : ℕ} {ε : GeneType} :
    prime^[k] (Gene.ofRank n ε) = Gene.ofRank (n - k) ε := by
  induction hk : k using Nat.twoStepInduction generalizing k with
  | zero => rfl
  | one => simp only [Function.iterate_one, prime_ofRank]
  | more w h1 h2 =>
    change prime^[w + 1 + 1] (Gene.ofRank n ε) = _
    rw [add_comm, Function.iterate_add_apply, Function.iterate_one, h2 rfl, prime_ofRank]
    ac_rfl

lemma prime_iterate_ofRankAlt {k n : ℕ} {ε : GeneType} :
    prime^[k] (Gene.ofRankAlt n ε) = Gene.ofRankAlt (n - k) ((k : ℤ).negOnePow • ε) := by
  rw [Gene.ofRankAlt_def, Gene.ofRankAlt_def, prime_iterate_ofRank, smul_smul,
    ← Int.negOnePow_add]
  by_cases hnk : k ≤ n
  · congr 2
    refine (Int.negOnePow_eq_iff ..).2 ?_
    ring_nf
    simp only [hnk, Nat.cast_sub, sub_sub_cancel, sub_self, Even.zero]
  · simp only [show n - k = 0 by omega, Gene.ofRank_zero, CharP.cast_eq_zero, zero_sub,
    Int.reduceNeg]

lemma prime_iterate_ofRank_eq_zero {k n : ℕ} {ε : GeneType} (h : n ≤ k) :
    prime^[k] (Gene.ofRank n ε) = 0 := by
  rw [prime_iterate_ofRank, Nat.sub_eq_zero_of_le h, Gene.ofRank_zero]

lemma signature_prime {X : Chromosome} :
    (signature X.prime) = X.sum (fun g m ↦ m • (primeGene g).signature) := by
  simp_rw [← map_nsmul]
  exact map_finsuppSum signature ..

lemma signature_prime_iterate {X : Chromosome} {k : ℕ} :
    (signature (prime^[k + 1] X)) =
    X.sum (fun g m ↦ m • (prime^[k] (primeGene g)).signature) := by
  induction k generalizing X with
  | zero => rw [zero_add, Function.iterate_one, signature_prime]; rfl
  | succ k hk =>
    have hz (i : Gene) : 0 • signature (prime^[k] (primeGene i)) = 0 := zero_nsmul _
    rw [Function.iterate_succ_apply, hk, prime_def, Finsupp.sum_sum_index hz]
    · refine Finsupp.sum_congr (fun _ _ ↦ ?_)
      rw [hk, Finsupp.sum_smul_index' hz]
      simp_rw [Finsupp.sum, ← Finset.sum_nsmul, smul_assoc]
    · intros; exact add_nsmul ..

lemma signature_prime_fst {X : Chromosome} :
    (signature X.prime).1 = X.sum (fun g m ↦ (m : ℚ) • (primeGene g).signature.1) :=
  signature_prime ▸ map_finsuppSum (AddMonoidHom.fst ..) ..

lemma signature_prime_snd {X : Chromosome} :
    (signature X.prime).2 = X.sum (fun g m ↦ (m : ℚ) • (primeGene g).signature.2) :=
  signature_prime ▸ map_finsuppSum (AddMonoidHom.snd ..) ..

lemma signature_prime_fst₂ {X : Chromosome} :
    (signature X.prime.prime).1 =
    X.sum (fun g m ↦ (m : ℚ) • (primeGene g).prime.signature.1) :=
  (@signature_prime_iterate X 1) ▸ map_finsuppSum (AddMonoidHom.fst ..) ..

lemma signature_prime_snd₂ {X : Chromosome} :
    (signature X.prime.prime).2 =
    X.sum (fun g m ↦ (m : ℚ) • (primeGene g).prime.signature.2) :=
  (@signature_prime_iterate X 1) ▸ map_finsuppSum (AddMonoidHom.snd ..) ..

lemma signature_ofRank_prime_le (g : Gene) :
    signature (Gene.ofRank g.rank g.type).prime ≤ (signature (Gene.ofRank g.rank g.type)) ⊓
      (signature (Gene.ofRank g.rank g.type)).swap := by
  rw [signature_ofRank, prime_ofRank, signature_ofRank, dif_neg (Nat.ne_zero_of_lt g.rank_pos)]
  split_ifs
  · refine le_inf ?_ (Prod.mk_le_swap.2 ?_) <;> exact (Gene.signature_pos _).le
  · cases g.type
    · simp [Gene.signature_of_nonPolarized, Nat.cast_sub g.rank_pos, Nat.cast_one]
      linarith
    · simp_rw [Gene.signature_of_positive, Nat.cast_sub g.rank_pos, Nat.cast_one,
        Nat.even_sub_one g.rank_pos]
      split_ifs <;> (simp; linarith)
    · simp_rw [Gene.signature_of_negative, Nat.cast_sub g.rank_pos, Nat.cast_one,
        sub_add_cancel, Nat.even_sub_one g.rank_pos]
      split_ifs <;> (simp; linarith)

lemma signature_prime_le (X : Chromosome) :
    (signature X.prime) ≤ (signature X) ⊓ (signature X).swap := by
  induction X using Finsupp.induction with
  | zero => rfl
  | single_add a _ _ _ _ hle =>
    rw [map_add, map_add, map_add, ← Gene.ofRank_eq_gene_smul, map_nsmul,
      map_nsmul, map_nsmul]
    refine le_inf ?_ ?_
    · refine add_le_add (nsmul_le_nsmul ?_ (signature_nonneg _) .refl) (hle.trans inf_le_left)
      exact (signature_ofRank_prime_le a).trans inf_le_left
    · rw [Prod.swap_add, Prod.smul_swap]
      refine add_le_add (nsmul_le_nsmul ?_ ?_ .refl) (hle.trans inf_le_right)
      · exact (signature_ofRank_prime_le a).trans inf_le_right
      · exact (Prod.mk_le_swap.2 (signature_nonneg _))

lemma prime_coeff {X : Chromosome} {g : Gene} :
    X.prime g = X ⟨g.rank + 1, g.type, Nat.le_add_right_of_le g.rank_pos⟩ := by
  induction X using Finsupp.induction with
  | zero => rw [map_zero, zero_apply, zero_apply]
  | single_add b n X hb hn hX =>
    simp only [map_add, prime_single, smul_dite, nsmul_zero, smul_single,
      smul_eq_mul, mul_one, coe_add, Pi.add_apply, single_apply, ← hX,
      Nat.add_right_cancel_iff]
    split_ifs with h1 h2 h3
    · rw [congrArg Gene.rank h2, Nat.add_sub_cancel] at h1
      grind only [g.rank_pos]
    · rfl
    · rw [single_apply, if_pos]
      ext <;> grind only
    · rw [single_apply_eq_zero]
      intro h; grind only [Gene.neq_iff.1 h3]

lemma prime_iterate_coeff (k : ℕ) (X : Chromosome) (g : Gene) :
  (prime^[k] X) g = X ⟨g.rank + k, g.type,
    Nat.le_add_right_of_le g.rank_pos⟩ := by
  induction k generalizing X with
  | zero => rfl
  | succ n hn => rw [Function.iterate_succ_apply, hn X.prime, prime_coeff]; rfl

lemma prime_iterate_eq_zero_rank_le {X : Chromosome} {k : ℕ} :
    (∀ g ∈ X.support, g.rank ≤ k) ↔ prime^[k] X = 0 := by
  constructor
  · intro hk; ext g
    rw [zero_apply, prime_iterate_coeff, ← notMem_support_iff]
    intro h; specialize hk _ h
    rw [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at hk
    absurd g.rank_pos
    exact Std.Rxc.size_eq_zero_iff_not_le.1 hk
  · intro hk g hg
    by_contra! h
    have hpos : 1 ≤ g.rank - k := by omega
    have heq : ⟨g.rank - k + k, g.type, Nat.le_add_right_of_le hpos⟩ = g :=
      Gene.ext (Nat.sub_add_cancel h.le) rfl
    have h_coeff := prime_iterate_coeff k X ⟨g.rank - k, g.type, hpos⟩
    rw [heq, hk, zero_apply] at h_coeff
    exact (mem_support_iff.1 hg) h_coeff.symm

lemma rank_one_of_prime_eq_zero {X : Chromosome} (hprime : X.prime = 0)
    {g : Gene} (hg : g ∈ X.support) : g.rank = 1 :=
  (Nat.le_antisymm g.rank_pos ((@prime_iterate_eq_zero_rank_le X 1).2 hprime g hg)).symm

lemma prime_ne_zero_of_rank_ge_two {X : Chromosome} (hne : X ≠ 0)
    (hrank : ∀ g ∈ X.support, 2 ≤ g.rank) : X.prime ≠ 0 := by
  by_contra!
  obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.2 hne
  grind only [hrank g hg, rank_one_of_prime_eq_zero this hg]

lemma prime_iterate_ne_zero_if_prime_ne {X : Chromosome} {j k : ℕ} (hle : j ≤ k)
    (hne : prime^[k] X ≠ 0) : prime^[j] X ≠ 0 := by
  intro h
  rw [(Nat.sub_add_cancel hle).symm, Function.iterate_add_apply, h] at hne
  exact hne <| Function.iterate_fixed (map_zero prime) _

end prime

end Chromosome
