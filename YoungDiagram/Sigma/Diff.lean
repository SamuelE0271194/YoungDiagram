import YoungDiagram.Sigma.Basic

open Chromosome Finsupp

namespace Sigma

variable (X : Chromosome) (k : ℕ)

/-- The alternating-basis type of a rank-`r` gene with sign `ε`. -/
def altType (r : ℕ) (ε : GeneType) : GeneType :=
  Int.negOnePow ((r : ℤ) - 1) • ε

lemma altType_add (r k : ℕ) (ε : GeneType) :
    altType (r + k) ((k : ℤ).negOnePow • ε) = altType r ε := by
  unfold altType
  rw [GeneType.negOnePow_smul_smul]
  congr 1
  refine (Int.negOnePow_eq_iff ..).2 ?_
  ring_nf
  exact ⟨k, by omega⟩

lemma altType_even (r : ℕ) (heven : Even r) (ε : GeneType) : altType r ε = -ε := by
  unfold altType
  simp [GeneType.negOnePow_smul, heven]

lemma altType_odd (r : ℕ) (heven : ¬ Even r) (ε : GeneType) : altType r ε = ε := by
  unfold altType
  simp [GeneType.negOnePow_smul, heven]

lemma altType_positive_ne_negative (r : ℕ) :
    altType r GeneType.Positive ≠ altType r GeneType.Negative := by
  unfold altType
  simp only [GeneType.negOnePow_smul]
  split_ifs <;> decide

lemma type_eq_altType_positive_or_negative (g : Gene) (hpol : g.type ≠ .NonPolarized) :
    g.type = altType g.rank GeneType.Positive ∨
      g.type = altType g.rank GeneType.Negative := by
  unfold altType
  simp only [GeneType.negOnePow_smul]
  split_ifs <;> cases h : g.type
  · exact absurd h hpol
  · left; simp
  · right; simp
  · exact absurd h hpol
  · right; simp
  · left; simp

lemma signature_sub_primeGene_eq_altType_counts (g : Gene) (hpol : g.type ≠ .NonPolarized) :
    g.signature - (primeGene g).signature =
      ((if g.type = altType g.rank GeneType.Positive then 1 else 0),
       (if g.type = altType g.rank GeneType.Negative then 1 else 0)) := by
  rcases type_eq_altType_positive_or_negative g hpol with hpos | hneg
  · have heq : Gene.ofRankAlt g.rank GeneType.Positive = single g 1 := by
      rw [Gene.ofRankAlt_eq_gene g.rank_pos]
      congr 1
      exact Gene.ext rfl (by simpa [altType] using hpos.symm)
    have h := signature_prime_ofRankAlt_positive g.rank_pos
    rw [heq] at h
    have h1 : signature (single g 1) = g.signature := by
      simp [signature_single g.rank_pos]
    have h2 : prime (single g 1) = primeGene g := by
      rw [prime_single, one_nsmul]; rfl
    rw [h1, h2] at h
    rw [h]
    have hneg_ne : g.type ≠ altType g.rank GeneType.Negative := fun hneg =>
      altType_positive_ne_negative g.rank (hpos.symm.trans hneg)
    rw [if_pos hpos, if_neg hneg_ne]
  · have heq : Gene.ofRankAlt g.rank GeneType.Negative = single g 1 := by
      rw [Gene.ofRankAlt_eq_gene g.rank_pos]
      congr 1
      exact Gene.ext rfl (by simpa [altType] using hneg.symm)
    have h := signature_prime_ofRankAlt_negative g.rank_pos
    rw [heq] at h
    have h1 : signature (single g 1) = g.signature := by
      simp [signature_single g.rank_pos]
    have h2 : prime (single g 1) = primeGene g := by
      rw [prime_single, one_nsmul]; rfl
    rw [h1, h2] at h
    rw [h]
    have hpos_ne : g.type ≠ altType g.rank GeneType.Positive := fun hpos =>
      altType_positive_ne_negative g.rank (hpos.symm.trans hneg)
    rw [if_neg hpos_ne, if_pos hneg]

lemma signature_prime_gene_diff (g : Gene) (hpol : g.type ≠ .NonPolarized) :
    g.signature - (primeGene g).signature =
      if Even g.rank then
        ((if g.type = GeneType.Positive then 0 else 1),
         (if g.type = GeneType.Negative then 0 else 1))
      else
        ((if g.type = GeneType.Positive then 1 else 0),
         (if g.type = GeneType.Negative then 1 else 0)) := by
  rw [signature_sub_primeGene_eq_altType_counts g hpol]
  by_cases heven : Even g.rank
  · simp only [if_pos heven]
    -- Even rank: negOnePow (rank - 1) = -1, so altType swaps Positive ↔ Negative
    cases h : g.type with
    | NonPolarized => exact absurd h hpol
    | Positive => simp [altType_even g.rank heven]
    | Negative => simp [altType_even g.rank heven]
  · simp only [if_neg heven]
    -- Odd rank: negOnePow (rank - 1) = 1, so altType preserves Positive and Negative
    cases h : g.type with
    | NonPolarized => exact absurd h hpol
    | Positive => simp [altType_odd g.rank heven]
    | Negative => simp [altType_odd g.rank heven]

lemma signature_rank_diff {n : ℕ} {ε : GeneType} (hn : n ≥ 1) :
    signature (Gene.ofRank n ε) - signature (Gene.ofRank (n - 1) ε) =
      signature (Gene.ofRank n ε) - signature (prime (Gene.ofRank n ε)) := by
  have : n ≠ 0 := by omega
  simp [prime_ofRank]

lemma signature_ofRank_diff {n : ℕ} {ε : GeneType} (hn : 1 ≤ n) (hε : ε ≠ .NonPolarized) :
    signature (Gene.ofRank n ε) - signature (Gene.ofRank (n - 1) ε) =
      if Even n then
        ((if ε = GeneType.Positive then 0 else 1),
         (if ε = GeneType.Negative then 0 else 1))
      else
        ((if ε = GeneType.Positive then 1 else 0),
         (if ε = GeneType.Negative then 1 else 0)) := by
  rw [signature_rank_diff hn]
  have hn' : n ≠ 0 := by omega
  set g : Gene := ⟨n, ε, Nat.pos_of_ne_zero hn'⟩
  have hg_sig : signature (Gene.ofRank n ε) = g.signature := by
    rw [signature_ofRank, dif_neg hn']
  have hprime_eq : prime (Gene.ofRank n ε) = primeGene g := by
    rw [prime_ofRank, primeGene_def]
  rw [hg_sig, hprime_eq]
  exact signature_prime_gene_diff g hε

/-- The drop in the first signature component when going from `σ(X)ₖ` to `σ(X)ₖ₊₁`
equals the total multiplicity of genes in `X^(k)` that are positive in the alternating basis,
i.e. genes `g` with `g.type = (-1)^(g.rank-1) • .Positive`. -/
lemma sigma_fst_diff (hX : X ∈ Variety.Pi) :
    (sigma X k).1 - (sigma X (k + 1)).1 =
    (prime^[k] X).sum (fun g m ↦
      if g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive
      then (m : ℚ) else 0) := by
  simp only [sigma, Function.iterate_succ_apply']
  set Y := prime^[k] X with hY
  have hYPi : Y ∈ Variety.Pi := Variety.prime_mem_Pi_iterate hX
  rw [signature_fst, signature_prime_fst]
  simp only [Finsupp.sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun g hg ↦ ?_)
  have hpol : g.type ≠ GeneType.NonPolarized :=
    (Chromosome.IsPolarized_def'.1 (Variety.mem_Pi_iff.1 hYPi)) g hg
  rw [← smul_sub]
  change (Y g : ℚ) • (g.signature.1 - (primeGene g).signature.1) =
    if g.type = altType g.rank GeneType.Positive then (Y g : ℚ) else 0
  have hsig : g.signature.1 - (primeGene g).signature.1 =
      if g.type = altType g.rank GeneType.Positive then 1 else 0 := by
    simpa using congr_arg Prod.fst (signature_sub_primeGene_eq_altType_counts g hpol)
  rw [hsig]
  by_cases hpos : g.type = altType g.rank GeneType.Positive <;> simp [hpos]

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
  change (Y g : ℚ) • (g.signature.2 - (primeGene g).signature.2) =
    if g.type = altType g.rank GeneType.Negative then (Y g : ℚ) else 0
  have hsig : g.signature.2 - (primeGene g).signature.2 =
      if g.type = altType g.rank GeneType.Negative then 1 else 0 := by
    simpa using congr_arg Prod.snd (signature_sub_primeGene_eq_altType_counts g hpol)
  rw [hsig]
  by_cases hneg : g.type = altType g.rank GeneType.Negative <;> simp [hneg]

lemma prime_iterate_sum_eq (ε : GeneType) :
    (prime^[k] X).sum (fun g m ↦
      if g.type = altType g.rank ε then (m : ℚ) else 0) =
    ∑ g ∈ X.support.filter (fun g =>
      k < g.rank ∧ g.type = altType g.rank ((k : ℤ).negOnePow • ε)),
    (X g : ℚ) := by
  simp only [Finsupp.sum]
  conv_lhs => arg 2; ext g; rw [prime_iterate_coeff k X g]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
      (fun g _ => (⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
      (fun g' hg' => (⟨g'.rank - k, g'.type, by
        have hlt := (Finset.mem_filter.mp hg').2.1
        omega⟩ : Gene))
      ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg ⊢
    obtain ⟨hgsupp, hgtype⟩ := hg
    refine ⟨by rwa [← prime_iterate_coeff], ?_, ?_⟩
    · have := g.rank_pos; omega
    · rw [altType_add]
      exact hgtype
  · intro g' hg'
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg' ⊢
    obtain ⟨hgsupp', hlt, hgtype'⟩ := hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt hlt
    refine ⟨?_, ?_⟩
    · rw [prime_iterate_coeff]
      simp only [Nat.sub_add_cancel hle]
      exact hgsupp'
    · rw [← Nat.sub_add_cancel hle, altType_add] at hgtype'
      exact hgtype'
  · intro g _
    exact Gene.ext (Nat.add_sub_cancel g.rank k) rfl
  · intro g' hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt (Finset.mem_filter.mp hg').2.1
    exact Gene.ext (Nat.sub_add_cancel hle) rfl
  · intros
    rfl

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
  have hkeven : Int.negOnePow (↑k : ℤ) = 1 := Int.negOnePow_even _ (by exact_mod_cast hk)
  simpa [altType, hkeven] using prime_iterate_sum_eq X k GeneType.Positive

lemma prime_iterate_sum_neg_eq (hk : ¬Even k) :
    (prime^[k] X).sum (fun g m ↦
      if g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Negative
      then (m : ℚ) else 0) =
    ∑ g ∈ X.support.filter (fun g =>
      k < g.rank ∧ g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
    (X g : ℚ) := by
  have hkodd : Int.negOnePow (↑k : ℤ) = -1 :=
    Int.negOnePow_odd _ (by exact_mod_cast Nat.not_even_iff_odd.mp hk)
  simpa [altType, hkodd, GeneType.neg_one_smul, GeneType.neg_negative] using
    prime_iterate_sum_eq X k GeneType.Negative

end Sigma
