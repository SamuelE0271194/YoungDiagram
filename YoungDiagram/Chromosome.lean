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

lemma Gene.ofRank_def {n : ℕ} {ε : GeneType} :
  Gene.ofRank n ε = if h : n = 0 then 0
    else single ⟨n, ε, Nat.pos_of_ne_zero h⟩ 1 := rfl

lemma Gene.ofRankAlt_def {n : ℕ} {ε : GeneType} :
  Gene.ofRankAlt n ε = Gene.ofRank n (Int.negOnePow (n - 1) • ε) := rfl

@[simp] lemma Gene.ofRank_zero {ε : GeneType} : Gene.ofRank 0 ε = 0 := rfl

@[simp] lemma Gene.ofRankAlt_zero {ε : GeneType} : Gene.ofRankAlt 0 ε = 0 := rfl

/-- `g_+(k)` equals `Gene.ofRank k .Negative` when `k` is even, and `Gene.ofRank k .Positive`
when `k` is odd. -/
lemma Gene.ofRankAlt_positive {k : ℕ} (hk : 1 ≤ k) :
    Gene.ofRankAlt k GeneType.Positive =
      if Even k then Gene.ofRank k GeneType.Negative
                else Gene.ofRank k GeneType.Positive := by
  have htype : Int.negOnePow ((k : ℤ) - 1) • GeneType.Positive =
      if Even k then GeneType.Negative else GeneType.Positive := by
    rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) from by omega, GeneType.negOnePow_smul']
    simp only [GeneType.neg_positive]
    split_ifs with h1 h2
    · exact absurd h1 ((Nat.even_sub_one hk).mp h2)
    · rfl
    · rfl
    · have h2 : ¬Even k := by assumption
      exact absurd ((Nat.even_sub_one hk).mpr h1) h2
  simp only [Gene.ofRankAlt_def, htype]
  split_ifs <;> rfl

/-- `g_-(k)` equals `Gene.ofRank k .Positive` when `k` is even, and `Gene.ofRank k .Negative`
when `k` is odd. -/
lemma Gene.ofRankAlt_negative {k : ℕ} (hk : 1 ≤ k) :
    Gene.ofRankAlt k GeneType.Negative =
      if Even k then Gene.ofRank k GeneType.Positive
                else Gene.ofRank k GeneType.Negative := by
  have htype : Int.negOnePow ((k : ℤ) - 1) • GeneType.Negative =
      if Even k then GeneType.Positive else GeneType.Negative := by
    rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) from by omega, GeneType.negOnePow_smul']
    simp only [GeneType.neg_negative]
    split_ifs with h1 h2
    · exact absurd h1 ((Nat.even_sub_one hk).mp h2)
    · rfl
    · rfl
    · have h2 : ¬Even k := by assumption
      exact absurd ((Nat.even_sub_one hk).mpr h1) h2
  simp only [Gene.ofRankAlt_def, htype]
  split_ifs <;> rfl

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

section signature

/--
The signature of a chromosome is the weighted sum of the signatures of its constituent genes.
-/
noncomputable def signature : Chromosome →+ ℚ × ℚ := weight Gene.signature

lemma signature_def {X : Chromosome} : X.signature =
  X.sum (fun g count ↦ (count : ℚ) • g.signature) := rfl

lemma signature_nonneg (X : Chromosome) : 0 ≤ X.signature := by
  dsimp [signature_def]
  exact sum_nonneg' fun g ↦
    smul_nonneg Rat.natCast_nonneg g.signature_pos.le

@[simp] lemma signature_ofRank_zero {ε : GeneType} :
    (Gene.ofRank 0 ε).signature = 0 := rfl

lemma signature_ofRank {n : ℕ} {ε : GeneType} :
  (Gene.ofRank n ε).signature =
    if h : n = 0 then 0
    else (⟨n, ε, Nat.pos_of_ne_zero h⟩ : Gene).signature := by
  dsimp [signature_def]
  split_ifs
  · rfl
  · rw [sum_single_index, Nat.cast_one, one_smul]
    · exact smul_eq_zero_of_left rfl _

@[simp] lemma signature_ofRank_one_positive :
    (Gene.ofRank 1 .Positive).signature = (1, 0) := by
  simp only [signature_ofRank, one_ne_zero, ↓reduceDIte, Gene.signature_of_positive,
    Nat.not_even_one, ↓reduceIte, Nat.cast_one, add_self_div_two, sub_self, zero_div]

@[simp] lemma signature_ofRank_one_negative :
    (Gene.ofRank 1 .Negative).signature = (0, 1) := by
  simp only [signature_ofRank, one_ne_zero, ↓reduceDIte, Gene.signature_of_negative,
    Nat.not_even_one, ↓reduceIte, Nat.cast_one, sub_self, zero_div, add_self_div_two]

@[simp] lemma signature_single {k : ℕ} {n : ℕ} (hk : 1 ≤ k) {ε : GeneType} :
    signature (single (⟨k, ε, hk⟩ : Gene) n) =
    n * (⟨k, ε, hk⟩ : Gene).signature :=
  sum_single_index <| smul_eq_zero_of_left rfl _

lemma signature_ofRank_nonPolarized {n : ℕ} :
    (Gene.ofRank n .NonPolarized).signature =
    (Gene.ofRank n .NonPolarized).signature.swap := by
  simp only [signature_ofRank]
  split_ifs
  · rfl
  · rw [Gene.signature_of_nonPolarized rfl]; rfl

lemma signature_ofRank_swap {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n (- ε)).signature = (Gene.ofRank n ε).signature.swap := by
  cases ε
  · exact signature_ofRank_nonPolarized
  all_goals
    simp only [GeneType.neg_positive, signature_ofRank]; split_ifs
    · rfl
    · first | rw [Gene.signature_of_negative rfl, Gene.signature_of_positive rfl] |
        rw [Gene.signature_of_positive rfl, Gene.signature_of_negative rfl]
      simp only; split_ifs <;> rfl

lemma signature_ofRank_positive {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 1) .Negative).signature + (1, 0) := by
  have hk' : k ≠ 0 := by omega
  simp only [signature_ofRank, hk', ↓reduceDIte]
  split_ifs with h
  · replace hk : k = 1 := by omega
    simp [Gene.signature_of_positive, hk]
  · simp [Gene.signature_of_positive]
    split_ifs with h1
    · have : ¬ Even (k - 1) := (Nat.even_sub_one hk).1 h1
      simp [Gene.signature_of_negative, this, Nat.cast_pred hk]; ring
    · have : Even (k - 1) := (iff_not_comm.1 (Nat.even_sub_one hk)).2 h1
      simp [Gene.signature_of_negative, this, Nat.cast_pred hk]; ring

lemma signature_ofRank_negative {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Negative).signature =
    (Gene.ofRank (k - 1) .Positive).signature + (0, 1) := by
  rw [← GeneType.neg_positive, signature_ofRank_swap,
    signature_ofRank_positive hk, Prod.swap_add, ← signature_ofRank_swap]; simp

lemma signature_ofRank_general {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 1) (-ε)).signature + (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp [signature_ofRank_positive hk]
  | .Negative, _ => simp [signature_ofRank_negative hk]

lemma signature_ofRank_eq {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 1) (- ε)).signature + (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp [signature_ofRank_positive hk]
  | .Negative, _ =>
    rw [← GeneType.neg_positive, signature_ofRank_swap,
      signature_ofRank_positive hk, Prod.swap_add, ← signature_ofRank_swap]; simp

lemma signature_ofRank_positive' {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 1) .Positive).signature + if Even k then (0, 1) else (1, 0) := by
  have hk' : k ≠ 0 := by omega
  by_cases hk'' : k = 1
  · subst hk''
    simp only [signature_ofRank_one_positive, tsub_self, Gene.ofRank_zero, map_zero,
      Nat.not_even_one, ↓reduceIte, zero_add]
  · simp only [signature_ofRank, hk', ↓reduceDIte]
    replace hk'' : k - 1 ≠ 0 := Nat.sub_ne_zero_of_lt <|
      Nat.lt_of_le_of_ne hk fun a ↦ hk'' a.symm
    simp only [Gene.signature_of_positive, Nat.even_sub_one hk, ite_not, hk'', ↓reduceDIte]
    split_ifs <;> (simp [hk]; ring)

lemma signature_ofRank_eq' {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature = (Gene.ofRank (k - 1) ε).signature +
    if Even k then (Gene.ofRank 1 (- ε)).signature else (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp [signature_ofRank_positive' hk]
  | .Negative, _ =>
    rw [← GeneType.neg_positive, neg_neg, signature_ofRank_swap, signature_ofRank_swap,
      signature_ofRank_positive' hk, Prod.swap_add, add_right_inj]
    split_ifs <;> simp

lemma signature_ofRank_positive₂ {k : ℕ} (hk : 2 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 2) .Positive).signature + (1, 1) := by
  change _ = (Gene.ofRank (k - 1 - 1) .Positive).signature + _
  rw [signature_ofRank_positive (Nat.one_le_of_lt hk),
    signature_ofRank_eq (Nat.le_sub_one_of_lt hk) (by decide), add_assoc]; simp

lemma signature_ofRank_eq₂ {k : ℕ} {ε : GeneType} (hk : 2 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 2) ε).signature + (1, 1) := by
  match ε, hε with
  | .Positive, _ => exact signature_ofRank_positive₂ hk
  | .Negative, _ =>
    rw [← GeneType.neg_positive, signature_ofRank_swap,
      signature_ofRank_positive₂ hk, Prod.swap_add, ← signature_ofRank_swap]
    rfl

lemma signature_fst {X : Chromosome} :
    (Chromosome.signature X).1 = X.sum (fun g n ↦ (n : ℚ) • g.signature.1) :=
  map_sum (AddMonoidHom.fst ..) ..

lemma signature_snd {X : Chromosome} :
    (Chromosome.signature X).2 = X.sum (fun g n ↦ (n : ℚ) • g.signature.2) :=
  map_sum (AddMonoidHom.snd ..) ..

lemma signature_ofRankAlt_general {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRankAlt k ε).signature =
    (Gene.ofRankAlt (k - 1) (-ε)).signature + (Gene.ofRank 1 ε).signature := by
  by_cases hk1 : k = 1
  · subst hk1
    simp [Gene.ofRankAlt_def]
  · have hk_pred : 1 ≤ k - 1 := by omega
    match ε, hε with
    | .Positive, _ =>
      rw [Gene.ofRankAlt_positive hk, GeneType.neg_positive,
          Gene.ofRankAlt_negative hk_pred]
      split_ifs with hek hek1
      · -- Even k, Even (k-1): impossible
        exact absurd hek1 ((Nat.even_sub_one hk).mp hek)
      · -- Even k, ¬Even (k-1)
        rw [signature_ofRank_eq' hk (by decide : GeneType.Negative ≠ .NonPolarized)]
        simp [if_pos hek, signature_ofRank_one_positive]
      · -- ¬Even k, Even (k-1)
        rw [signature_ofRank_eq' hk (by decide : GeneType.Positive ≠ .NonPolarized)]
        simp [if_neg hek, signature_ofRank_one_positive]
      · -- ¬Even k, ¬Even (k-1): impossible
        exact absurd ((Nat.even_sub_one hk).mpr (by omega)) hek
    | .Negative, _ =>
      rw [Gene.ofRankAlt_negative hk, GeneType.neg_negative,
          Gene.ofRankAlt_positive hk_pred]
      split_ifs with hek hek1
      · -- Even k, Even (k-1): impossible
        exact absurd hek1 ((Nat.even_sub_one hk).mp hek)
      · -- Even k, ¬Even (k-1)
        rw [signature_ofRank_eq' hk (by decide : GeneType.Positive ≠ .NonPolarized)]
        simp [if_pos hek, signature_ofRank_one_negative]
      · -- ¬Even k, Even (k-1)
        rw [signature_ofRank_eq' hk (by decide : GeneType.Negative ≠ .NonPolarized)]
        simp [if_neg hek, signature_ofRank_one_negative]
      · -- ¬Even k, ¬Even (k-1): impossible
        exact absurd ((Nat.even_sub_one hk).mpr (by omega)) hek

lemma signature_ofRankAlt_general_b {k : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRankAlt (k + 1) ε).signature =
    (Gene.ofRankAlt k (-ε)).signature + (Gene.ofRank 1 ε).signature := by
    have hk' : 1 ≤ k + 1 := by simp
    rw [signature_ofRankAlt_general hk' hε]
    simp_all

end signature

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

lemma rank_one_of_prime_eq_zero {X : Chromosome} (hprime : X.prime = 0) :
    ∀ g ∈ X.support, g.rank = 1 := by
  by_contra!
  rcases this with ⟨g, ⟨h1, h2⟩⟩
  have hpos : 1 ≤ g.rank - 1 := by grind only [g.rank_pos]
  refine (Finsupp.mem_support_iff.1 h1) ?_
  convert (hprime ▸ @prime_coeff X ⟨g.rank - 1, g.type, hpos⟩).symm
  simp only; omega

lemma prime_ne_zero_of_rank_ge_two {X : Chromosome} (hne : X ≠ 0)
    (hrank : ∀ g ∈ X.support, 2 ≤ g.rank) : X.prime ≠ 0 := by
  by_contra!
  obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.2 hne
  grind only [hrank g hg, rank_one_of_prime_eq_zero this g hg]

lemma prime_iterate_ne_zero_if_prime_ne {X : Chromosome} {j k : ℕ} (hle : j ≤ k)
    (hne : prime^[k] X ≠ 0) : prime^[j] X ≠ 0 := by
  intro h
  rw [(Nat.sub_add_cancel hle).symm, Function.iterate_add_apply, h] at hne
  exact hne <| Function.iterate_fixed (map_zero prime) _

/-- Priming `g_+(k)` decreases the first signature component by 1. -/
lemma signature_prime_ofRankAlt_positive {k : ℕ} (hk : 1 ≤ k) :
    signature (Gene.ofRankAlt k GeneType.Positive) -
    signature (prime (Gene.ofRankAlt k GeneType.Positive)) = (1, 0) := by
  simp only [Gene.ofRankAlt_positive hk]
  split_ifs with h
  · -- k even: gene is Gene.ofRank k .Negative
    rw [prime_ofRank]
    have heq := signature_ofRank_eq' hk (show GeneType.Negative ≠ .NonPolarized by decide)
    simp only [if_pos h, GeneType.neg_negative, signature_ofRank_one_positive] at heq
    rw [heq]; abel
  · -- k odd: gene is Gene.ofRank k .Positive
    rw [prime_ofRank]
    have heq := signature_ofRank_eq' hk (show GeneType.Positive ≠ .NonPolarized by decide)
    simp only [if_neg h] at heq
    rw [heq, signature_ofRank_one_positive]; abel

/-- Priming `g_-(k)` decreases the second signature component by 1. -/
lemma signature_prime_ofRankAlt_negative {k : ℕ} (hk : 1 ≤ k) :
    signature (Gene.ofRankAlt k GeneType.Negative) -
    signature (prime (Gene.ofRankAlt k GeneType.Negative)) = (0, 1) := by
  simp only [Gene.ofRankAlt_negative hk]
  split_ifs with h
  · -- k even: gene is Gene.ofRank k .Positive
    rw [prime_ofRank]
    have heq := signature_ofRank_eq' hk (show GeneType.Positive ≠ .NonPolarized by decide)
    simp only [if_pos h, GeneType.neg_positive, signature_ofRank_one_negative] at heq
    rw [heq]; abel
  · -- k odd: gene is Gene.ofRank k .Negative
    rw [prime_ofRank]
    have heq := signature_ofRank_eq' hk (show GeneType.Negative ≠ .NonPolarized by decide)
    simp only [if_neg h] at heq
    rw [heq, signature_ofRank_one_negative]; abel

lemma prime_ofRankAlt_positive {k : ℕ} :
    prime (Gene.ofRankAlt k GeneType.Positive) = Gene.ofRankAlt (k - 1) GeneType.Negative := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [Gene.ofRankAlt_def, prime_ofRank, Nat.succ_sub_one]
    congr 1
    rw [show (Nat.succ k : ℤ) - 1 = ↑k from by push_cast; ring,
        ← GeneType.neg_positive, GeneType.negOnePow_smul_neg,
        show (↑k : ℤ) - 1 + 1 = ↑k from by ring]

lemma prime_ofRankAlt_negative {k : ℕ} :
    prime (Gene.ofRankAlt k GeneType.Negative) = Gene.ofRankAlt (k - 1) GeneType.Positive := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [Gene.ofRankAlt_def, prime_ofRank, Nat.succ_sub_one]
    congr 1
    rw [show (Nat.succ k : ℤ) - 1 = ↑k from by push_cast; ring,
        ← GeneType.neg_negative, GeneType.negOnePow_smul_neg,
        show (↑k : ℤ) - 1 + 1 = ↑k from by ring]

lemma prime_ofRankAlt {k : ℕ} {ε : GeneType} (hε : ε ≠ GeneType.NonPolarized) :
    prime (Gene.ofRankAlt k ε) = Gene.ofRankAlt (k - 1) (-ε) := by
  cases ε with
  | NonPolarized => exact absurd rfl hε
  | Positive => exact prime_ofRankAlt_positive
  | Negative => exact prime_ofRankAlt_negative

lemma prime_iterate_ofRankAlt {k n : ℕ} {ε : GeneType} (hε : ε ≠ GeneType.NonPolarized) :
    prime^[n] (Gene.ofRankAlt k ε) = Gene.ofRankAlt (k - n) ((n : ℤ).negOnePow • ε) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
        prime_ofRankAlt (GeneType.smul_ne_nonPolarized_iff.mp hε),
        Nat.sub_sub]
    congr 1
    push_cast
    exact GeneType.neg_negOnePow_smul

end prime

section rank

def maxRank (c : Chromosome) : ℕ := c.support.sup Gene.rank

lemma maxRank_def {X : Chromosome} : X.maxRank = X.support.sup Gene.rank := rfl

lemma add_maxRank {X Y : Chromosome} :
    (X + Y).maxRank = X.maxRank ⊔ Y.maxRank := by
  rw [maxRank_def, support_add_eq', Finset.sup_union, maxRank_def, maxRank_def]

lemma smul_maxRank {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
    (n • X).maxRank = X.maxRank := by
  rw [maxRank_def, support_smul_eq hn, maxRank_def]

lemma maxRank_ofRank {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n ε).maxRank = n := by
  rw [maxRank_def, Gene.ofRank_def]
  split_ifs with hn
  · rw [hn, support_zero, Finset.sup_empty, Nat.bot_eq_zero]
  · rw [support_single_ne_zero _ Nat.one_ne_zero, Finset.sup_singleton]

lemma maxRank_eq_zero {X : Chromosome} (h : X.maxRank = 0) : X = 0 := by
  ext g
  by_contra hg
  have : g.rank = 0 := Nat.eq_zero_of_le_zero <|
    h ▸ Finset.le_sup (Finsupp.mem_support_iff.2 hg)
  exact Nat.not_succ_le_zero 0 (this ▸ g.rank_pos : 1 ≤ 0)

lemma maxRank_prime_lt {X : Chromosome} (hX : X ≠ 0) :
    X.prime.maxRank < X.maxRank := by
  induction X using Finsupp.induction with
  | zero => exact False.elim (false_of_ne hX)
  | single_add g n X hg hn h =>
    by_cases hzero : X = 0
    · rw [hzero, add_zero, ← Gene.ofRank_eq_gene_smul, map_nsmul, smul_maxRank hn,
        smul_maxRank hn, maxRank_ofRank, prime_ofRank, maxRank_ofRank]
      exact Nat.sub_one_lt_of_lt g.rank_pos
    · rw [map_add, add_maxRank, Nat.max_lt]; constructor
      · rw [← Gene.ofRank_eq_gene_smul, map_nsmul, smul_maxRank hn, prime_ofRank,
          maxRank_ofRank, add_maxRank, smul_maxRank hn, maxRank_ofRank]
        have := g.rank_pos; omega
      · rw [add_maxRank]
        specialize h hzero; omega

noncomputable def rank : Chromosome →+ ℕ := weight Gene.rank

lemma rank_def {X : Chromosome} : X.rank = X.sum (fun g count ↦ count • g.rank) := rfl

lemma rank_zero {X : Chromosome} (h : X.rank = 0) : X = 0 :=
  (weight_eq_zero_iff_eq_zero _).1 h

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

end rank

section order

/--
The dominance relation defined in [Djoković 1980, p. 73].
$X$ dominates $Y$ ($X \ge Y$) if the signature of $X^{(k)}$ is
component-wise greater than or equal to
the signature of $Y^{(k)}$ for all $k \ge 0$.
-/
def Dominates (X Y : Chromosome) : Prop :=
  ∀ k : ℕ, signature (prime^[k] Y) ≤ signature (prime^[k] X)

instance : LE Chromosome where
  le a b := b.Dominates a

/--
The dominance relation forms a preorder on the set of all chromosomes.
-/
instance : Preorder Chromosome where
  le_refl a _ := le_refl _
  lt a b := b.Dominates a ∧ ¬a.Dominates b
  le_trans _ _ _ hab hbc k := le_trans (hab k) (hbc k)

@[simp] lemma le_iff_dominates {X Y : Chromosome} : X ≤ Y ↔
  ∀ k : ℕ, signature (prime^[k] X) ≤ signature (prime^[k] Y) := .rfl

instance : IsOrderedCancelAddMonoid Chromosome where
  add_le_add_left _ _ _ _ := by
    simpa only [le_iff_dominates, iterate_map_add, map_add, add_le_add_iff_right]
  le_of_add_le_add_left _ _ _ h := by
    simpa only [le_iff_dominates, iterate_map_add, map_add, add_le_add_iff_left] using h

lemma sub_single_lt_sub_single {X Y : Chromosome} {g : Gene}
    (hgX : 0 < X g) (hgY : 0 < Y g) (hXY : X < Y) :
    (X - Finsupp.single g 1) < Y - Finsupp.single g 1 := by
  have hX_eq := sub_single_add_single_eq hgX
  have hY_eq := sub_single_add_single_eq hgY
  refine ⟨fun k ↦ ?_, fun hge ↦ lt_irrefl X (lt_of_lt_of_le hXY (fun k ↦ ?_))⟩
  · have h : (prime^[k] X).signature ≤ (prime^[k] Y).signature :=
      (le_iff_dominates.mp hXY.le) k
    nth_rw 1 [← hX_eq, ← hY_eq] at h
    simpa only [iterate_map_add, map_add, add_le_add_iff_right] using h
  · nth_rw 1 [← hY_eq, ← hX_eq]
    simpa only [iterate_map_add, map_add, add_le_add_iff_right] using hge k

end order

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
  rw [filter_pos_add_filter_neg]

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

section parity

def oddPart : Chromosome →+ Chromosome where
  toFun c := c.filter (Odd ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

def evenPart : Chromosome →+ Chromosome where
  toFun c := c.filter (Even ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

lemma evenPart_idempotent {X : Chromosome} : evenPart (evenPart X) = evenPart X := by
  refine (filter_eq_self_iff (Even ·.rank) (filter (Even ·.rank) X)).2 ?_
  intro _ hx
  by_contra!
  exact hx (filter_apply_neg _ X this)

lemma oddPart_idempotent {X : Chromosome} : oddPart (oddPart X) = oddPart X := by
  refine (filter_eq_self_iff (Odd ·.rank) (filter (Odd ·.rank) X)).2 ?_
  intro _ hx
  by_contra!
  exact hx (filter_apply_neg _ X this)

lemma parity_decomposition (X : Chromosome) : X = X.oddPart + X.evenPart := by
  simp only [oddPart, AddMonoidHom.coe_mk, ZeroHom.coe_mk, evenPart]
  conv =>
    enter [2, 2, 1, a]
    rw [← Nat.not_odd_iff_even]
  rw [filter_pos_add_filter_neg]

lemma evenPart_single {g : Gene} : evenPart (single g 1) =
    if Even g.rank then single g 1 else 0 := by
  split_ifs with h
  · exact filter_single_of_pos _ h
  · exact filter_single_of_neg _ h

lemma oddPart_single {g : Gene} : oddPart (single g 1) =
    if Even g.rank then 0 else single g 1 := by
  split_ifs with h
  · exact filter_single_of_neg _ <| Nat.not_odd_iff_even.2 h
  · exact filter_single_of_pos _ <| Nat.not_even_iff_odd.1 h

lemma evenPart_prime {X : Chromosome} : X.prime.evenPart = X.oddPart.prime := by
  induction X using Finsupp.induction
  · repeat rw [map_zero]
  · expose_names
    repeat rw [map_add]
    rw [h_2, add_left_inj, ← smul_single_one, map_nsmul, map_nsmul,
      map_nsmul, map_nsmul, nsmul_right_inj h_1, oddPart_single]
    split_ifs with ha
    · simp only [prime_def, primeGene, smul_dite, nsmul_zero, smul_single, smul_eq_mul, mul_one,
      single_zero, dite_eq_ite, ite_self, sum_single_index, sum_zero_index]
      split_ifs
      · exact map_zero _
      · simp [evenPart_single, Nat.even_add_one.1 ((Nat.sub_add_cancel a.rank_pos) ▸ ha)]
    · simp only [prime_def, primeGene, smul_dite, nsmul_zero, smul_single, smul_eq_mul, mul_one,
      single_zero, dite_eq_ite, ite_self, sum_single_index]
      split_ifs
      · exact map_zero _
      · simp [evenPart_single, (Nat.even_sub a.rank_pos).2 <|
          (iff_false_right Nat.not_even_one).2 ha]

lemma oddPart_prime {X : Chromosome} : X.prime.oddPart = X.evenPart.prime := by
  have := X.prime.parity_decomposition
  nth_rw 1 [X.parity_decomposition, map_add, evenPart_prime, add_comm,
    add_left_inj] at this
  exact this.symm

lemma oddPart_evenPart {X : Chromosome} : oddPart (evenPart X) = 0 := by
  simp only [oddPart, evenPart, AddMonoidHom.coe_mk, ZeroHom.coe_mk, filter_eq_zero_iff,
    filter_apply, ite_eq_right_iff]
  intro _ ho he
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff, ho] at he
  tauto

lemma evenPart_oddPart {X : Chromosome} : evenPart (oddPart X) = 0 := by
  simp only [evenPart, oddPart, AddMonoidHom.coe_mk, ZeroHom.coe_mk, filter_eq_zero_iff,
    filter_apply, ite_eq_right_iff]
  intro _ he ho
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff, ho] at he
  tauto

end parity

end Chromosome
