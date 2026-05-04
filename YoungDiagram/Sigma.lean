import YoungDiagram.Mutations.Pi

open Chromosome Finsupp

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

open Variety in
lemma cond_15_6_Pi {Y : Chromosome} (hY : Y ∈ Pi) :
    Y.prime.signature - Y.prime.prime.signature ≤
    (Y.signature - Y.prime.signature).swap := by
  induction Y using Finsupp.induction with
  | zero => simp only [map_zero, sub_self, Prod.swap_zero, Std.le_refl]
  | single_add a b f ha hb hf => calc
    _ = (prime f).signature - (prime f).prime.signature +
        ((prime (single a b)).signature - (prime (single a b)).prime.signature) := by
      simp_rw [map_add, sub_add_eq_sub_sub]; ring
    _ ≤ (signature f - signature (prime f)).swap +
        ((prime (single a b)).signature - (prime (single a b)).prime.signature) :=
      add_le_add_left (hf (mem_Pi_iff_add.1 hY).2) _
    _ ≤ _ := by
      simp_rw [Prod.swap_sub, map_add, Prod.swap_add]
      rw [sub_eq_add_neg, add_comm (signature (single a b)).swap, add_sub_assoc, add_assoc]
      refine add_le_add_right ?_ (signature f).swap
      rw [sub_add_eq_sub_sub, sub_eq_add_neg _ (signature (prime f)).swap,
        add_comm]
      refine add_le_add_left ?_ (-(signature (prime f)).swap)
      simp_rw [← Gene.ofRank_eq_gene_smul, map_nsmul, Prod.smul_swap, ← smul_sub]
      have := (IsFiltered_single hb).1 <| mem_Pi_iff.1 (mem_Pi_iff_add.1 hY).1
      refine nsmul_le_nsmul_right ((cond_15_6_ofRank a.rank this).trans ?_) b
      rw [Prod.swap_sub]

namespace Sigma

variable (X : Chromosome) (k : ℕ)

/--
For `X ∈ Π`, `σ(X)` is the 2×∞ nonneg integral matrix whose k-th column is
`(aₖ, bₖ) = sig X^(k)`, as defined in [Djoković 1982, (15.1)].

Represented as a function `ℕ → ℚ × ℚ`, where the first component is `aₖ`
and the second is `bₖ`.
-/
noncomputable def sigma : ℕ → ℚ × ℚ :=
  fun k ↦ signature (prime^[k] X)

local notation "a" X:max k:max => Prod.fst (sigma X k)

local notation "b" X:max k:max => Prod.snd (sigma X k)

lemma antitone : Antitone (sigma X) := by
  refine antitone_nat_of_succ_le (fun _ ↦ ?_)
  simp only [sigma, Function.iterate_succ_apply']
  exact (signature_prime_le _).trans inf_le_left

lemma eventually_zero : ∃ K, ∀ k ≥ K, sigma X k = 0 := by
  refine ⟨X.maxRank, fun k hk ↦ ?_⟩
  simp only [sigma]
  have hprime_zero : prime^[X.maxRank] X = 0 := by
    have h : prime^[X.maxRank] (X.below X.maxRank) = 0 := prime_below le_rfl
    rwa [below_maxRank] at h
  rw [← Nat.sub_add_cancel hk, Function.iterate_add_apply,
    hprime_zero, iterate_map_zero, map_zero]

lemma cond_15_2 : (∀ k, a X (k + 1) ≤ a X k) ∧ (∃ K, ∀ k ≥ K, a X k = 0) :=
  ⟨fun k ↦ (Prod.le_def.1 (antitone X (Nat.le_add_right k 1))).1,
    (eventually_zero X).imp fun _ h1 k h2 ↦ congr_arg Prod.fst (h1 k h2)⟩

lemma cond_15_3 : (∀ k, b X (k + 1) ≤ b X k) ∧ (∃ K, ∀ k ≥ K, b X k = 0) :=
  ⟨fun k ↦ (antitone X (Nat.le_add_right k 1)).2,
    (eventually_zero X).imp fun _ h1 k h2 ↦ congr_arg Prod.snd (h1 k h2)⟩

/-- (15.4) a₀ ≥ b₁ ≥ a₂ ≥ b₃ ≥ … -/
lemma cond_15_4 : if Even k then b X (k + 1) ≤ a X k
    else a X (k + 1) ≤ b X k := by
  split_ifs <;> simp only [sigma, Function.iterate_succ_apply']
  · exact ((signature_prime_le _).trans inf_le_right).2
  · exact ((signature_prime_le _).trans inf_le_right).1

/-- (15.5) b₀ ≥ a₁ ≥ b₂ ≥ a₃ ≥ … -/
lemma cond_15_5 : if Even k then a X (k + 1) ≤ b X k
    else b X (k + 1) ≤ a X k := by
  split_ifs <;> simp only [sigma, Function.iterate_succ_apply']
  · exact ((signature_prime_le _).trans inf_le_right).1
  · exact ((signature_prime_le _).trans inf_le_right).2

/-- (15.6) a₀ − a₁ ≥ b₁ − b₂ ≥ a₂ − a₃ ≥ b₃ − b₄ ≥ … -/
lemma cond_15_6 (hX : X ∈ Variety.Pi) :
    if Even k then b X (k + 1) - b X (k + 2) ≤ a X k - a X (k + 1)
              else a X (k + 1) - a X (k + 2) ≤ b X k - b X (k + 1) := by
  have h := cond_15_6_Pi (Variety.prime_mem_Pi_iterate hX (k := k))
  split_ifs with heven <;> simp only [sigma, Function.iterate_succ_apply']
  · exact (Prod.mk_le_swap.1 h).1
  · exact (Prod.mk_le_swap.1 h).2

/-- (15.7) b₀ − b₁ ≥ a₁ − a₂ ≥ b₂ − b₃ ≥ a₃ − a₄ ≥ … -/
lemma cond_15_7 (hX : X ∈ Variety.Pi) :
    if Even k then a X (k + 1) - a X (k + 2) ≤ b X k - b X (k + 1)
              else b X (k + 1) - b X (k + 2) ≤ a X k - a X (k + 1) := by
  have h := cond_15_6_Pi (Variety.prime_mem_Pi_iterate hX (k := k))
  split_ifs with heven <;> simp only [sigma, Function.iterate_succ_apply']
  · exact (Prod.mk_le_swap.1 h).2
  · exact (Prod.mk_le_swap.1 h).1

/-- (15.8) If `X < Y` in `Π` then `aₖ ≤ cₖ` and `bₖ ≤ dₖ` for all `k`,
where `(aₖ, bₖ) = σ(X)ₖ` and `(cₖ, dₖ) = σ(Y)ₖ`. -/
lemma cond_15_8 {X Y : Variety.Pi} (h : X < Y) (k : ℕ) :
    a X k ≤ a Y k ∧ b X k ≤ b Y k := le_iff_dominates.1 h.le k

/-- The drop in the first signature component when going from `σ(X)ₖ` to `σ(X)ₖ₊₁`
equals the total multiplicity of genes in `X^(k)` that are positive in the alternating basis,
i.e. genes `g` with `g.type = (-1)^(g.rank-1) • .Positive`. -/
lemma sigma_fst_diff (hX : X ∈ Variety.Pi) :
    (sigma X k).1 - (sigma X (k + 1)).1 =
    (prime^[k] X).sum (fun g m ↦
      if g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive
      then (m : ℚ) else 0) := by
  -- Step 1: unfold sigma and set Y := prime^[k] X
  simp only [sigma, Function.iterate_succ_apply']
  set Y := prime^[k] X with hY
  -- Step 2: Y is in Pi
  have hYPi : Y ∈ Variety.Pi := Variety.prime_mem_Pi_iterate hX
  -- Step 3: expand both sides by linearity, then combine into one sum
  rw [signature_fst, signature_prime_fst]
  simp only [Finsupp.sum, ← Finset.sum_sub_distrib]
  -- Step 4: per-gene contribution
  refine Finset.sum_congr rfl (fun g hg ↦ ?_)
  have hpol : g.type ≠ GeneType.NonPolarized :=
    (Chromosome.IsPolarized_def'.1 (Variety.mem_Pi_iff.1 hYPi)) g hg
  rw [← smul_sub]
  by_cases hpos : g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive
  · -- Sub-case A: g is ofRankAlt Positive; signature difference is 1
    rw [if_pos hpos]
    have heq : Gene.ofRankAlt g.rank GeneType.Positive = single g 1 := by
      rw [Gene.ofRankAlt_eq_gene g.rank_pos, ← hpos]
    have hsig : g.signature.1 - (Chromosome.signature (primeGene g)).1 = 1 := by
      have h := signature_prime_ofRankAlt_positive g.rank_pos
      rw [heq] at h
      have h1 : signature (single g 1) = g.signature := by
        simp [signature_single g.rank_pos]
      have h2 : prime (single g 1) = primeGene g := by
        rw [prime_single, one_nsmul]; rfl
      rw [h1, h2] at h
      exact congr_arg Prod.fst h
    simp [hsig]
  · -- Sub-case B: g is ofRankAlt Negative; signature difference is 0
    rw [if_neg hpos]
    have hneg : g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Negative := by
      simp only [GeneType.negOnePow_smul] at hpos ⊢
      cases h : g.type
      · exact absurd h hpol
      · rw [h] at hpos
        split_ifs with heven
        · rw [if_pos heven] at hpos; exact absurd rfl hpos
        · simp [GeneType.neg_negative]
      · rw [h] at hpos
        split_ifs with heven
        · rfl
        · rw [if_neg heven, GeneType.neg_positive] at hpos; exact absurd rfl hpos
    have heq_neg : Gene.ofRankAlt g.rank GeneType.Negative = single g 1 := by
      rw [Gene.ofRankAlt_eq_gene g.rank_pos, ← hneg]
    have hsig : g.signature.1 - (Chromosome.signature (primeGene g)).1 = 0 := by
      have h := signature_prime_ofRankAlt_negative g.rank_pos
      rw [heq_neg] at h
      have h1 : signature (single g 1) = g.signature := by
        simp [signature_single g.rank_pos]
      have h2 : prime (single g 1) = primeGene g := by
        rw [prime_single, one_nsmul]; rfl
      rw [h1, h2] at h
      exact congr_arg Prod.fst h
    simp [hsig]

/-- The drop in the second signature component when going from `σ(X)ₖ` to `σ(X)ₖ₊₁`
equals the total multiplicity of genes in `X^(k)` that are negative in the alternating basis,
i.e. genes `g` with `g.type = (-1)^(g.rank-1) • .Negative`. -/
lemma sigma_snd_diff (hX : X ∈ Variety.Pi) :
    (sigma X k).2 - (sigma X (k + 1)).2 =
    (prime^[k] X).sum (fun g m ↦
      if g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Negative
      then (m : ℚ) else 0) := by
  simp only [sigma, Function.iterate_succ_apply']
  set Y := prime^[k] X with hY
  have hYPi : Y ∈ Variety.Pi := Variety.prime_mem_Pi_iterate hX
  rw [signature_snd, signature_prime_snd]
  simp only [Finsupp.sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun g hg ↦ ?_)
  have hpol : g.type ≠ GeneType.NonPolarized :=
    (Chromosome.IsPolarized_def'.1 (Variety.mem_Pi_iff.1 hYPi)) g hg
  rw [← smul_sub]
  by_cases hneg : g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Negative
  · -- Sub-case A: g is ofRankAlt Negative; signature difference is 1
    rw [if_pos hneg]
    have heq : Gene.ofRankAlt g.rank GeneType.Negative = single g 1 := by
      rw [Gene.ofRankAlt_eq_gene g.rank_pos, ← hneg]
    have hsig : g.signature.2 - (Chromosome.signature (primeGene g)).2 = 1 := by
      have h := signature_prime_ofRankAlt_negative g.rank_pos
      rw [heq] at h
      have h1 : signature (single g 1) = g.signature := by
        simp [signature_single g.rank_pos]
      have h2 : prime (single g 1) = primeGene g := by
        rw [prime_single, one_nsmul]; rfl
      rw [h1, h2] at h
      exact congr_arg Prod.snd h
    simp [hsig]
  · -- Sub-case B: g is ofRankAlt Positive; signature difference is 0
    rw [if_neg hneg]
    have hpos : g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive := by
      simp only [GeneType.negOnePow_smul] at hneg ⊢
      cases h : g.type
      · exact absurd h hpol
      · rw [h] at hneg
        split_ifs with heven
        · rfl
        · rw [if_neg heven] at hneg; exact absurd rfl hneg
      · rw [h] at hneg
        split_ifs with heven
        · rw [if_pos heven] at hneg; exact absurd rfl hneg
        · simp [GeneType.neg_positive]
    have heq_pos : Gene.ofRankAlt g.rank GeneType.Positive = single g 1 := by
      rw [Gene.ofRankAlt_eq_gene g.rank_pos, ← hpos]
    have hsig : g.signature.2 - (Chromosome.signature (primeGene g)).2 = 0 := by
      have h := signature_prime_ofRankAlt_positive g.rank_pos
      rw [heq_pos] at h
      have h1 : signature (single g 1) = g.signature := by
        simp [signature_single g.rank_pos]
      have h2 : prime (single g 1) = primeGene g := by
        rw [prime_single, one_nsmul]; rfl
      rw [h1, h2] at h
      exact congr_arg Prod.snd h
    simp [hsig]

/-- When `k` is even, the `Finsupp.sum` over `prime^[k] X` counting genes of type
`(-1)^(rank-1) • Positive` equals the sum over genes of `X` with `rank > k` and the same
type condition (using their rank in `X`).

The parity hypothesis is needed because a gene `g` of rank `r` in `prime^[k] X` corresponds
to a gene of rank `r + k` in `X`, and `negOnePow(r + k - 1) = negOnePow(r - 1)` iff `Even k`. -/
lemma prime_iterate_sum_pos_eq (hk : Even k) :
    (prime^[k] X).sum (fun g m ↦
      if g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive
      then (m : ℚ) else 0) =
    ∑ g ∈ X.support.filter (fun g =>
      k < g.rank ∧ g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
    (X g : ℚ) := by
  -- Step 1: unfold Finsupp.sum and replace each coefficient (prime^[k] X) g
  --         with X ⟨g.rank + k, g.type, _⟩ via prime_iterate_coeff
  simp only [Finsupp.sum]
  conv_lhs => arg 2; ext g; rw [prime_iterate_coeff k X g]
  -- Step 2: absorb the if-then-else into the summation domain
  rw [← Finset.sum_filter]
  -- Parity sub-lemma: negOnePow((r + k : ℤ) - 1) = negOnePow((r : ℤ) - 1) when Even k
  have hpar : ∀ r : ℕ, Int.negOnePow ((r : ℤ) + k - 1) = Int.negOnePow ((r : ℤ) - 1) := by
    have hkeven : Int.negOnePow (↑k : ℤ) = 1 := Int.negOnePow_even _ (by exact_mod_cast hk)
    intro r
    rw [show (↑r + ↑k - 1 : ℤ) = (↑r - 1) + ↑k by ring, Int.negOnePow_add, hkeven, mul_one]
  -- Step 3: change of variables via φ : g ↦ ⟨g.rank + k, g.type, _⟩
  --         with inverse φ⁻¹ : g' ↦ ⟨g'.rank - k, g'.type, _⟩
  refine Finset.sum_bij'
      (fun g _ => (⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
      (fun g' hg' => (⟨g'.rank - k, g'.type, by
        have hlt := (Finset.mem_filter.mp hg').2.1
        omega⟩ : Gene))
      ?_ ?_ ?_ ?_ ?_
  · -- (a) φ(g) ∈ X.support.filter (k < rank ∧ type cond)
    intro g hg
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg ⊢
    obtain ⟨hgsupp, hgtype⟩ := hg
    refine ⟨by rwa [← prime_iterate_coeff], ?_, ?_⟩
    · have := g.rank_pos; omega
    · show g.type = Int.negOnePow ((↑(g.rank + k) : ℤ) - 1) • GeneType.Positive
      push_cast; rw [hpar g.rank]; exact hgtype
  · -- (b) φ⁻¹(g') ∈ (prime^[k] X).support.filter (type cond)
    intro g' hg'
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg' ⊢
    obtain ⟨hgsupp', hlt, hgtype'⟩ := hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt hlt
    refine ⟨?_, ?_⟩
    · rw [prime_iterate_coeff]
      simp only [Nat.sub_add_cancel hle]
      exact hgsupp'
    · show g'.type = Int.negOnePow ((↑(g'.rank - k) : ℤ) - 1) • GeneType.Positive
      have hcast : (↑(g'.rank - k) : ℤ) = ↑g'.rank - ↑k := Nat.cast_sub hle
      have h := hpar (g'.rank - k)
      rw [hcast, show (↑g'.rank - ↑k + ↑k - 1 : ℤ) = ↑g'.rank - 1 by ring] at h
      rw [hcast, ← h]; exact hgtype'
  · -- (c) left inverse: ⟨g.rank + k - k, …⟩ = g
    intro g _
    exact Gene.ext (Nat.add_sub_cancel g.rank k) rfl
  · -- (d) right inverse: ⟨g'.rank - k + k, …⟩ = g'
    intro g' hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt (Finset.mem_filter.mp hg').2.1
    exact Gene.ext (Nat.sub_add_cancel hle) rfl
  · -- (e) value equality: X ⟨g.rank + k, …⟩ = X ⟨g.rank + k, …⟩
    intros; rfl

lemma prime_iterate_sum_neg_eq (hk : ¬Even k) :
    (prime^[k] X).sum (fun g m ↦
      if g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Negative
      then (m : ℚ) else 0) =
    ∑ g ∈ X.support.filter (fun g =>
      k < g.rank ∧ g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
    (X g : ℚ) := by
  simp only [Finsupp.sum]
  conv_lhs => arg 2; ext g; rw [prime_iterate_coeff k X g]
  rw [← Finset.sum_filter]
  have hkodd : Int.negOnePow (↑k : ℤ) = -1 :=
    Int.negOnePow_odd _ (by exact_mod_cast Nat.not_even_iff_odd.mp hk)
  -- Parity sub-lemma: negOnePow(r + k - 1) • Positive = negOnePow(r - 1) • Negative when Odd k
  have hpar : ∀ r : ℕ, Int.negOnePow ((r : ℤ) + k - 1) • GeneType.Positive =
              Int.negOnePow ((r : ℤ) - 1) • GeneType.Negative := by
    intro r
    rw [show (↑r + ↑k - 1 : ℤ) = (↑r - 1) + ↑k by ring, ← GeneType.negOnePow_smul_smul,
        hkodd, GeneType.neg_one_smul, GeneType.neg_positive]
  refine Finset.sum_bij'
      (fun g _ => (⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
      (fun g' hg' => (⟨g'.rank - k, g'.type, by
        have hlt := (Finset.mem_filter.mp hg').2.1
        omega⟩ : Gene))
      ?_ ?_ ?_ ?_ ?_
  · -- (a) φ(g) ∈ X.support.filter (k < rank ∧ type cond Positive)
    intro g hg
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg ⊢
    obtain ⟨hgsupp, hgtype⟩ := hg
    refine ⟨by rwa [← prime_iterate_coeff], ?_, ?_⟩
    · have := g.rank_pos; omega
    · show g.type = Int.negOnePow ((↑(g.rank + k) : ℤ) - 1) • GeneType.Positive
      push_cast; rw [hpar g.rank]; exact hgtype
  · -- (b) φ⁻¹(g') ∈ (prime^[k] X).support.filter (type cond Negative)
    intro g' hg'
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg' ⊢
    obtain ⟨hgsupp', hlt, hgtype'⟩ := hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt hlt
    refine ⟨?_, ?_⟩
    · rw [prime_iterate_coeff]
      simp only [Nat.sub_add_cancel hle]
      exact hgsupp'
    · show g'.type = Int.negOnePow ((↑(g'.rank - k) : ℤ) - 1) • GeneType.Negative
      have hcast : (↑(g'.rank - k) : ℤ) = ↑g'.rank - ↑k := Nat.cast_sub hle
      have h := hpar (g'.rank - k)
      rw [hcast, show (↑g'.rank - ↑k + ↑k - 1 : ℤ) = ↑g'.rank - 1 by ring] at h
      rw [hcast, ← h]; exact hgtype'
  · -- (c) left inverse: ⟨g.rank + k - k, …⟩ = g
    intro g _
    exact Gene.ext (Nat.add_sub_cancel g.rank k) rfl
  · -- (d) right inverse: ⟨g'.rank - k + k, …⟩ = g'
    intro g' hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt (Finset.mem_filter.mp hg').2.1
    exact Gene.ext (Nat.sub_add_cancel hle) rfl
  · -- (e) value equality
    intros; rfl

/-- For `X ∈ Π`, both components of `σ(X)ₖ` are natural numbers (as elements of ℚ). -/
lemma sigma_isNat (hX : X ∈ Variety.Pi) : ∃ n : ℕ × ℕ, sigma X k = (↑n.1, ↑n.2) := by
  simp only [sigma]
  exact signature_pi_isNat (Variety.prime_mem_Pi_iterate hX)

/-- (15.6) a₀ − a₁ ≥ bκ − bκ₊₁ (or a depending on sign of k) -/
lemma cond_15_6_compare_k_to_0 (hX : X ∈ Variety.Pi) :
    if Even k then a X k - a X (k + 1) ≤ a X 0 - a X 1
              else b X k - b X (k + 1) ≤ a X 0 - a X 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h15_6 := cond_15_6 X k hX
    split_ifs with heven
    · -- Even (k+1), so ¬Even k
      have hkodd : ¬Even k := by rwa [Nat.even_add_one] at heven
      simp only [hkodd, ↓reduceIte] at ih h15_6
      exact h15_6.trans ih
    · -- ¬Even (k+1), so Even k
      have hkeven : Even k := by rwa [Nat.even_add_one, not_not] at heven
      simp only [hkeven, ↓reduceIte] at ih h15_6
      exact h15_6.trans ih

end Sigma
