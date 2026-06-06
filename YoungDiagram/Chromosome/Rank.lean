import YoungDiagram.Chromosome.Prime

open Finsupp

namespace Chromosome

section rank

def maxRank (c : Chromosome) : ℕ := c.support.sup Gene.rank

lemma maxRank_def {X : Chromosome} : X.maxRank = X.support.sup Gene.rank := rfl

lemma maxRank_zero : maxRank 0 = 0 := by
  rw [maxRank_def, support_zero, Finset.sup_empty, Nat.bot_eq_zero]

lemma le_maxRank {X : Chromosome} : ∀ g ∈ X.support, g.rank ≤ X.maxRank :=
  fun _ hg ↦ Finset.le_sup hg

lemma add_maxRank {X Y : Chromosome} :
    (X + Y).maxRank = X.maxRank ⊔ Y.maxRank := by
  rw [maxRank_def, support_add_eq_union, Finset.sup_union, maxRank_def, maxRank_def]

lemma smul_maxRank {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
    (n • X).maxRank = X.maxRank := by
  rw [maxRank_def, support_smul_eq hn, maxRank_def]

lemma maxRank_ofRank {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n ε).maxRank = n := by
  rw [maxRank_def, Gene.ofRank_def]
  split_ifs with hn
  · rw [hn, support_zero, Finset.sup_empty, Nat.bot_eq_zero]
  · rw [support_single _ Nat.one_ne_zero, Finset.sup_singleton]

lemma maxRank_eq_zero {X : Chromosome} (h : X.maxRank = 0) : X = 0 := by
  ext g
  by_contra hg
  have : g.rank = 0 := Nat.eq_zero_of_le_zero <|
    h ▸ Finset.le_sup (Finsupp.mem_support_iff.2 hg)
  exact Nat.not_succ_le_zero 0 (this ▸ g.rank_pos : 1 ≤ 0)

lemma maxRank_neg {X : Chromosome} : (- X).maxRank = X.maxRank := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le fun b hb ↦ ?_
    rw [← Gene.neg_rank]
    exact Finset.le_sup <| neg_neg X ▸ mem_neg_support.1 hb
  · refine Finset.sup_le fun b hb ↦ ?_
    rw [← Gene.neg_rank]
    exact Finset.le_sup <| mem_neg_support.1 hb

lemma maxRank_prime_lt {X : Chromosome} (hX : X ≠ 0) :
    X.prime.maxRank < X.maxRank := by
  induction X using induction' with
  | zero => exact False.elim (false_of_ne hX)
  | @ofRank_add n hn ε k X hk h =>
    by_cases hzero : X = 0
    · rw [hzero, add_zero, map_nsmul, smul_maxRank hk, smul_maxRank hk,
        prime_ofRank, maxRank_ofRank, maxRank_ofRank]
      exact Nat.sub_one_lt_of_lt hn
    · rw [map_add, add_maxRank, Nat.max_lt]; constructor
      · rw [map_nsmul, smul_maxRank hk, prime_ofRank, maxRank_ofRank,
          add_maxRank, smul_maxRank hk, maxRank_ofRank]; omega
      · rw [add_maxRank]
        specialize h hzero; omega

noncomputable def rank : Chromosome →+ ℕ := weight Gene.rank

lemma rank_def {X : Chromosome} : X.rank = X.sum (fun g count ↦ count • g.rank) := rfl

lemma rank_zero {X : Chromosome} (h : X.rank = 0) : X = 0 :=
  (weight_eq_zero_iff_eq_zero _).1 h

lemma rank_zero_iff {X : Chromosome} : X.rank = 0 ↔ X = 0 :=
  ⟨rank_zero, by intro h; rw [h, map_zero]⟩

lemma rank_single {n : ℕ} {g : Gene} :
  rank (single g n) = n • g.rank := weight_single ..

lemma rank_sub_single {X : Chromosome} {g : Gene} (hg : 0 < X g) :
    (X - Finsupp.single g 1).rank = X.rank - g.rank := by
  rw [rank, ← weight_sub_single_add (Nat.ne_zero_of_lt hg), Nat.add_sub_cancel]

lemma rank_ofRank {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n ε).rank = n := by
  rw [Gene.ofRank_def]
  split_ifs with hn
  · rw [hn, map_zero]
  · rw [rank_single, one_smul]

lemma rank_neg {X : Chromosome} : (- X).rank = X.rank := by
  induction X using induction' with
  | zero => rw [neg_zero]
  | ofRank_add _ _ _ ih =>
    rw [map_add, map_nsmul, neg_add, map_add, neg_smul, map_nsmul, neg_ofRank,
      rank_ofRank, rank_ofRank, ih]

lemma signature_sum_neg_eq_rank {X : Chromosome} : X.signature + (- X).signature = X.rank := by
  induction X using induction' with
  | zero =>
    rw [neg_zero, map_zero, map_zero, Nat.cast_zero, zero_add]
  | ofRank_add _ _ _ ih =>
    expose_names
    rw [map_add, neg_add, map_add, map_nsmul, signature_neg,
      map_nsmul, Prod.smul_swap, ← add_assoc, add_comm _ (-Y).signature,
      ← add_assoc, ← add_assoc, add_comm (-Y).signature, add_comm, ← add_assoc,
      ← add_assoc, ← smul_add, ← signature_ofRank_swap,
      add_comm (Gene.ofRank k (-ε)).signature, signature_sum_ofRank_neg_eq_rank,
      map_add, map_nsmul, Nat.cast_add, ← ih, rank_ofRank, nsmul_eq_mul, smul_eq_mul,
      Nat.cast_mul, mul_comm]
    ac_rfl

lemma rank_one {X : Chromosome} (hrank : X.rank = 1) :
    ∃ ε : GeneType, X = Gene.ofRank 1 ε := by
  have hzero : X ≠ 0 := fun h ↦ by simp [h] at hrank
  obtain ⟨a, (ha : X a ≠ 0)⟩ := ne_iff.1 hzero
  refine ⟨a.type, ?_⟩
  rw [rank, ← weight_sub_single_add ha, Nat.add_eq_one_iff,
    weight_eq_zero_iff_eq_zero] at hrank
  simp only [Nat.ne_zero_of_lt a.rank_pos, and_false, or_false] at hrank
  rw [← hrank.2, Gene.ofRank_eq_gene]
  apply le_antisymm
  · exact fun g ↦ Nat.le_of_sub_eq_zero <| Finsupp.ext_iff.1 hrank.1 g
  · rw [Finsupp.single_le_iff]; omega

lemma rank_of_prime {X : Chromosome} :
    X.prime.rank = X.sum (fun g m ↦ m * (g.rank - 1)) := by
  simp_rw [prime_def, map_finsuppSum, map_nsmul, nsmul_eq_mul, primeGene, rank_ofRank]
  rfl

lemma prime_rank_lt {X : Chromosome} (hne : X ≠ 0) :
    X.prime.rank < X.rank := by
  rw [rank_of_prime, rank_def, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · exact support_nonempty_iff.mpr hne
  · intro i hi
    rw [smul_eq_mul, Nat.mul_lt_mul_left]
    · grind only [i.rank_pos]
    · exact Nat.pos_of_ne_zero <| mem_support_iff.1 hi

lemma prime_iterate_rank_lt_of_ne_zero {X : Chromosome} {k : ℕ} (hk : 0 < k)
    (hne : prime^[k] X ≠ 0) : (prime^[k] X).rank < X.rank := by
  induction k using Nat.twoStepInduction with
  | zero => omega
  | one => exact prime_rank_lt <| prime_iterate_ne_zero_if_prime_ne (Nat.zero_le 1) hne
  | more n h1 h2 =>
    have := (prime_iterate_ne_zero_if_prime_ne (Nat.le_succ _) hne)
    rw [Function.iterate_succ_apply']
    exact (prime_rank_lt this).trans (h2 (Nat.zero_lt_succ n) this)

lemma signature_sum_eq_rank {X : Chromosome} :
    X.signature.1 + X.signature.2 = X.rank := by
  simp_rw [signature_fst, signature_snd, Finsupp.sum,
    ← Finset.sum_add_distrib, ← smul_add, Gene.signature_sum_eq_rank]
  simp only [rank_def, sum, Nat.cast_sum, Nat.cast_mul, smul_eq_mul]

lemma signature_eq_zero {X : Chromosome}
    (h : X.signature = 0) : X = 0 := by
  apply rank_zero
  have := (@signature_sum_eq_rank X).symm
  rwa [h, Prod.fst_zero, Prod.snd_zero, zero_add, Nat.cast_eq_zero] at this

lemma maxRank_le_rank (X : Chromosome) : X.maxRank ≤ X.rank :=
  Finset.sup_le fun _ hg ↦
    le_weight_of_ne_zero' Gene.rank (mem_support_iff.1 hg)

lemma rank_eq_maxRank_single {X : Chromosome}
    (h : X.rank = X.maxRank) (hpos : 0 < X.maxRank) :
    ∃ g : Gene, g.rank = X.maxRank ∧ X = Finsupp.single g 1 := by
  induction X using induction' with
  | zero => simp only [maxRank_zero, lt_self_iff_false] at hpos
  | @ofRank_add a ha ε b f hb hf =>
    rw [add_maxRank, smul_maxRank hb, maxRank_ofRank,
      map_add, map_nsmul, rank_ofRank] at *
    by_cases hle : a ≤ maxRank f
    · rw [Nat.max_eq_right hle] at *
      have := nonpos_iff_eq_zero.1 <| add_le_iff_nonpos_left.1 <| h ▸ maxRank_le_rank f
      rw [this, zero_add] at h
      specialize hf h hpos
      obtain (h0 | h0) := nsmul_eq_zero_iff.1 this
      · rwa [h0, Gene.ofRank_zero, nsmul_zero, zero_add]
      · rwa [h0, zero_smul, zero_add]
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)] at *
      have := le_self_nsmul (Nat.zero_le a) hb
      nth_rw 1 [← h, smul_eq_mul, smul_eq_mul, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, rank_zero_iff] at this
      rw [this, map_zero, add_zero, smul_eq_mul,
        mul_eq_right₀ (Nat.ne_zero_of_lt hpos)] at h
      rw [this, add_zero, h, one_nsmul]
      refine ⟨⟨a, ε, ha⟩, rfl, (Gene.ofRank_eq_gene' (Nat.ne_zero_of_lt ha))⟩

lemma prime_iterate_zero_of_maxRank_le {X : Chromosome} {k : ℕ} (h : X.maxRank ≤ k) :
    prime^[k] X = 0 :=
  prime_iterate_eq_zero_rank_le.1 fun _ hg ↦ (le_trans (le_maxRank _ hg) h)

end rank

end Chromosome
