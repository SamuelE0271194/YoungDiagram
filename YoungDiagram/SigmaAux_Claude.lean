import YoungDiagram.Mutations

open Chromosome
open Variety

open Finsupp Pointwise

-- Sub-lemma for (15.6) when X is a single polarized gene.
-- Even case: drop in .2 from primeGene g to prime(primeGene g) ≤ drop in .1 from g to primeGene g.
-- Odd case: drop in .1 from primeGene g to prime(primeGene g) ≤ drop in .2 from g to primeGene g.
lemma cond_15_6_single_gene (g : Gene) (hg : g.type ≠ .NonPolarized) (k : ℕ) :
    if Even k then
      (primeGene g).signature.2 - (prime (primeGene g)).signature.2 ≤
        g.signature.1 - (primeGene g).signature.1
    else
      (primeGene g).signature.1 - (prime (primeGene g)).signature.1 ≤
        g.signature.2 - (primeGene g).signature.2 := by
  match hg' : g.type with
  | .NonPolarized => exact absurd hg' hg
  | .Positive =>
    by_cases heven : Even k
    · simp only [if_pos heven]
      by_cases heven_r : Even g.rank
      · have hne : g.rank - 1 ≠ 0 := by
          obtain ⟨j, hj⟩ := heven_r; have := g.rank_pos; omega
        have hodd1 : ¬ Even (g.rank - 1) := (Nat.even_sub_one g.rank_pos).mp heven_r
        by_cases hne2 : g.rank - 1 - 1 = 0
        · -- r = 2
          simp only [primeGene, hg', prime_ofRank, hne2, Gene.ofRank_zero, map_zero,
                     Chromosome.signature_ofRank, hne, ↓reduceDIte, Prod.snd_zero, sub_zero]
          rw [Gene.signature_of_positive hg', if_pos heven_r,
              Gene.signature_of_positive rfl, if_neg hodd1]
          simp only [Nat.cast_pred g.rank_pos]
          have hcast : (g.rank : ℚ) = 2 := by exact_mod_cast (show g.rank = 2 by omega)
          linarith
        · -- r ≥ 4
          have heven2 : Even (g.rank - 1 - 1) := by
            obtain ⟨j, hj⟩ := heven_r; exact ⟨j - 1, by omega⟩
          simp only [primeGene, hg', prime_ofRank, Chromosome.signature_ofRank,
                     hne, hne2, ↓reduceDIte]
          rw [Gene.signature_of_positive hg', if_pos heven_r,
              Gene.signature_of_positive rfl, if_neg hodd1,
              Gene.signature_of_positive rfl, if_pos heven2]
          simp only [Nat.cast_pred g.rank_pos, Nat.cast_pred (Nat.pos_of_ne_zero hne)]
          linarith
      · have heven1 : Even (g.rank - 1) := by
          by_contra h; exact heven_r ((Nat.even_sub_one g.rank_pos).mpr h)
        by_cases hne : g.rank - 1 = 0
        · -- r = 1
          have hrank : g.rank = 1 := by have := g.rank_pos; omega
          have hcast : (g.rank : ℚ) = 1 := by exact_mod_cast hrank
          simp only [primeGene, hne, Gene.ofRank_zero, map_zero]
          simp only [Gene.signature_of_positive hg', if_neg heven_r, hcast]
          norm_num
        · -- r ≥ 3
          have hne2 : g.rank - 1 - 1 ≠ 0 := by obtain ⟨j, hj⟩ := heven1; omega
          have hodd2 : ¬ Even (g.rank - 1 - 1) := by
            intro ⟨j, hj⟩; obtain ⟨m, hm⟩ := heven1; omega
          simp only [primeGene, hg', prime_ofRank, Chromosome.signature_ofRank,
                     hne, hne2, ↓reduceDIte]
          rw [Gene.signature_of_positive hg', if_neg heven_r,
              Gene.signature_of_positive rfl, if_pos heven1,
              Gene.signature_of_positive rfl, if_neg hodd2]
          simp only [Nat.cast_pred g.rank_pos, Nat.cast_pred (Nat.pos_of_ne_zero hne)]
          linarith
    · simp only [if_neg heven]
      by_cases heven_r : Even g.rank
      · have hne : g.rank - 1 ≠ 0 := by
          obtain ⟨j, hj⟩ := heven_r; have := g.rank_pos; omega
        have hodd1 : ¬ Even (g.rank - 1) := (Nat.even_sub_one g.rank_pos).mp heven_r
        by_cases hne2 : g.rank - 1 - 1 = 0
        · -- r = 2
          simp only [primeGene, hg', prime_ofRank, hne2, Gene.ofRank_zero, map_zero,
                     Chromosome.signature_ofRank, hne, ↓reduceDIte,
                     Prod.fst_zero, sub_zero]
          rw [Gene.signature_of_positive hg', if_pos heven_r,
              Gene.signature_of_positive rfl, if_neg hodd1]
          simp only [Nat.cast_pred g.rank_pos]
          have hcast : (g.rank : ℚ) = 2 := by exact_mod_cast (show g.rank = 2 by omega)
          linarith
        · -- r ≥ 4
          have heven2 : Even (g.rank - 1 - 1) := by
            obtain ⟨j, hj⟩ := heven_r; exact ⟨j - 1, by omega⟩
          simp only [primeGene, hg', prime_ofRank, Chromosome.signature_ofRank,
                     hne, hne2, ↓reduceDIte]
          rw [Gene.signature_of_positive hg', if_pos heven_r,
              Gene.signature_of_positive rfl, if_neg hodd1,
              Gene.signature_of_positive rfl, if_pos heven2]
          simp only [Nat.cast_pred g.rank_pos, Nat.cast_pred (Nat.pos_of_ne_zero hne)]
          linarith
      · have heven1 : Even (g.rank - 1) := by
          by_contra h; exact heven_r ((Nat.even_sub_one g.rank_pos).mpr h)
        by_cases hne : g.rank - 1 = 0
        · -- r = 1
          have hrank : g.rank = 1 := by have := g.rank_pos; omega
          have hcast : (g.rank : ℚ) = 1 := by exact_mod_cast hrank
          simp only [primeGene, hne, Gene.ofRank_zero, map_zero]
          simp only [Gene.signature_of_positive hg', if_neg heven_r, hcast]
          norm_num
        · -- r ≥ 3
          have hne2 : g.rank - 1 - 1 ≠ 0 := by obtain ⟨j, hj⟩ := heven1; omega
          have hodd2 : ¬ Even (g.rank - 1 - 1) := by
            intro ⟨j, hj⟩; obtain ⟨m, hm⟩ := heven1; omega
          simp only [primeGene, hg', prime_ofRank, Chromosome.signature_ofRank,
                     hne, hne2, ↓reduceDIte]
          rw [Gene.signature_of_positive hg', if_neg heven_r,
              Gene.signature_of_positive rfl, if_pos heven1,
              Gene.signature_of_positive rfl, if_neg hodd2]
          simp only [Nat.cast_pred g.rank_pos, Nat.cast_pred (Nat.pos_of_ne_zero hne)]
          linarith
  | .Negative =>
    by_cases heven : Even k
    · simp only [if_pos heven]
      by_cases heven_r : Even g.rank
      · have hne : g.rank - 1 ≠ 0 := by
          obtain ⟨j, hj⟩ := heven_r; have := g.rank_pos; omega
        have hodd1 : ¬ Even (g.rank - 1) := (Nat.even_sub_one g.rank_pos).mp heven_r
        by_cases hne2 : g.rank - 1 - 1 = 0
        · -- r = 2
          simp only [primeGene, hg', prime_ofRank, hne2, Gene.ofRank_zero, map_zero,
                     Chromosome.signature_ofRank, hne, ↓reduceDIte, Prod.snd_zero, sub_zero]
          rw [Gene.signature_of_negative hg', if_pos heven_r,
              Gene.signature_of_negative rfl, if_neg hodd1]
          simp only [Nat.cast_pred g.rank_pos]
          have hcast : (g.rank : ℚ) = 2 := by exact_mod_cast (show g.rank = 2 by omega)
          linarith
        · -- r ≥ 4
          have heven2 : Even (g.rank - 1 - 1) := by
            obtain ⟨j, hj⟩ := heven_r; exact ⟨j - 1, by omega⟩
          simp only [primeGene, hg', prime_ofRank, Chromosome.signature_ofRank,
                     hne, hne2, ↓reduceDIte]
          rw [Gene.signature_of_negative hg', if_pos heven_r,
              Gene.signature_of_negative rfl, if_neg hodd1,
              Gene.signature_of_negative rfl, if_pos heven2]
          simp only [Nat.cast_pred g.rank_pos, Nat.cast_pred (Nat.pos_of_ne_zero hne)]
          linarith
      · have heven1 : Even (g.rank - 1) := by
          by_contra h; exact heven_r ((Nat.even_sub_one g.rank_pos).mpr h)
        by_cases hne : g.rank - 1 = 0
        · -- r = 1
          have hrank : g.rank = 1 := by have := g.rank_pos; omega
          have hcast : (g.rank : ℚ) = 1 := by exact_mod_cast hrank
          simp only [primeGene, hne, Gene.ofRank_zero, map_zero]
          simp only [Gene.signature_of_negative hg', if_neg heven_r, hcast]
          norm_num
        · -- r ≥ 3
          have hne2 : g.rank - 1 - 1 ≠ 0 := by obtain ⟨j, hj⟩ := heven1; omega
          have hodd2 : ¬ Even (g.rank - 1 - 1) := by
            intro ⟨j, hj⟩; obtain ⟨m, hm⟩ := heven1; omega
          simp only [primeGene, hg', prime_ofRank, Chromosome.signature_ofRank,
                     hne, hne2, ↓reduceDIte]
          rw [Gene.signature_of_negative hg', if_neg heven_r,
              Gene.signature_of_negative rfl, if_pos heven1,
              Gene.signature_of_negative rfl, if_neg hodd2]
          simp only [Nat.cast_pred g.rank_pos, Nat.cast_pred (Nat.pos_of_ne_zero hne)]
          linarith
    · simp only [if_neg heven]
      by_cases heven_r : Even g.rank
      · have hne : g.rank - 1 ≠ 0 := by
          obtain ⟨j, hj⟩ := heven_r; have := g.rank_pos; omega
        have hodd1 : ¬ Even (g.rank - 1) := (Nat.even_sub_one g.rank_pos).mp heven_r
        by_cases hne2 : g.rank - 1 - 1 = 0
        · -- r = 2
          simp only [primeGene, hg', prime_ofRank, hne2, Gene.ofRank_zero, map_zero,
                     Chromosome.signature_ofRank, hne, ↓reduceDIte,
                     Prod.fst_zero, sub_zero]
          rw [Gene.signature_of_negative hg', if_pos heven_r,
              Gene.signature_of_negative rfl, if_neg hodd1]
          simp only [Nat.cast_pred g.rank_pos]
          have hcast : (g.rank : ℚ) = 2 := by exact_mod_cast (show g.rank = 2 by omega)
          linarith
        · -- r ≥ 4
          have heven2 : Even (g.rank - 1 - 1) := by
            obtain ⟨j, hj⟩ := heven_r; exact ⟨j - 1, by omega⟩
          simp only [primeGene, hg', prime_ofRank, Chromosome.signature_ofRank,
                     hne, hne2, ↓reduceDIte]
          rw [Gene.signature_of_negative hg', if_pos heven_r,
              Gene.signature_of_negative rfl, if_neg hodd1,
              Gene.signature_of_negative rfl, if_pos heven2]
          simp only [Nat.cast_pred g.rank_pos, Nat.cast_pred (Nat.pos_of_ne_zero hne)]
          linarith
      · have heven1 : Even (g.rank - 1) := by
          by_contra h; exact heven_r ((Nat.even_sub_one g.rank_pos).mpr h)
        by_cases hne : g.rank - 1 = 0
        · -- r = 1
          have hrank : g.rank = 1 := by have := g.rank_pos; omega
          have hcast : (g.rank : ℚ) = 1 := by exact_mod_cast hrank
          simp only [primeGene, hne, Gene.ofRank_zero, map_zero]
          simp only [Gene.signature_of_negative hg', if_neg heven_r, hcast]
          norm_num
        · -- r ≥ 3
          have hne2 : g.rank - 1 - 1 ≠ 0 := by obtain ⟨j, hj⟩ := heven1; omega
          have hodd2 : ¬ Even (g.rank - 1 - 1) := by
            intro ⟨j, hj⟩; obtain ⟨m, hm⟩ := heven1; omega
          simp only [primeGene, hg', prime_ofRank, Chromosome.signature_ofRank,
                     hne, hne2, ↓reduceDIte]
          rw [Gene.signature_of_negative hg', if_neg heven_r,
              Gene.signature_of_negative rfl, if_pos heven1,
              Gene.signature_of_negative rfl, if_neg hodd2]
          simp only [Nat.cast_pred g.rank_pos, Nat.cast_pred (Nat.pos_of_ne_zero hne)]
          linarith

-- Lift of cond_15_6_single_gene to an arbitrary chromosome Y in Pi.
lemma cond_15_6_Pi (Y : Pi) (k : ℕ) :
    if Even k then
      (signature (prime Y)).2 - (signature (prime (prime Y))).2 ≤
        (signature Y).1 - (signature (prime Y)).1
    else
      (signature (prime Y)).1 - (signature (prime (prime Y))).1 ≤
        (signature Y).2 - (signature (prime Y)).2 := by
  have hpol : ∀ g ∈ (↑Y : Chromosome).support, g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (Variety.mem_Pi_iff.mp Y.property)
  by_cases heven : Even k
  · simp only [if_pos heven]
    -- Rearrange: A - B ≤ C - D iff A + D ≤ C + B
    suffices h : (signature (prime Y)).2 + (signature (prime Y)).1 ≤
                 (signature Y).1 + (signature (prime (prime Y))).2 by linarith
    -- Expand double-prime term first (before signature_prime_snd can match it),
    -- then expand remaining terms, then unfold Finsupp.sum to Finset.sum
    rw [signature_prime_snd₂, signature_prime_snd,
        signature_prime_fst, signature_fst]
    simp only [Finsupp.sum]
    -- Group: sum f + sum g = sum (f + g)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro g hg
    rw [← smul_add, ← smul_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hineq := cond_15_6_single_gene g (hpol g hg) 0
    simp only [show Even 0 from ⟨0, rfl⟩, ↓reduceIte] at hineq
    linarith
  · simp only [if_neg heven]
    -- Rearrange: A - B ≤ C - D iff A + D ≤ C + B
    suffices h : (signature (prime Y)).1 + (signature (prime Y)).2 ≤
                 (signature Y).2 + (signature (prime (prime Y))).1 by linarith
    -- Expand double-prime term first, then remaining terms, then unfold to Finset.sum
    rw [signature_prime_fst₂, signature_prime_fst,
        signature_prime_snd, signature_snd]
    simp only [Finsupp.sum]
    -- Group: sum f + sum g = sum (f + g)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro g hg
    rw [← smul_add, ← smul_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hineq := cond_15_6_single_gene g (hpol g hg) 1
    simp only [show ¬ Even 1 from by decide, ↓reduceIte] at hineq
    linarith

-- Lift of cond_15_6_single_gene, parity-swapped version.
-- Even k: drop in .1 ≤ drop in .2. Odd k: drop in .2 ≤ drop in .1.
lemma cond_15_7_Pi (Y : Pi) (k : ℕ) :
    if Even k then
      (signature (prime Y)).1 - (signature (prime (prime Y))).1 ≤
        (signature Y).2 - (signature (prime Y)).2
    else
      (signature (prime Y)).2 - (signature (prime (prime Y))).2 ≤
        (signature Y).1 - (signature (prime Y)).1 := by
  have hpol : ∀ g ∈ (↑Y : Chromosome).support, g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (Variety.mem_Pi_iff.mp Y.property)
  by_cases heven : Even k
  · simp only [if_pos heven]
    suffices h : (signature (prime Y)).1 + (signature (prime Y)).2 ≤
                 (signature Y).2 + (signature (prime (prime Y))).1 by linarith
    rw [signature_prime_fst₂, signature_prime_fst,
        signature_prime_snd, signature_snd]
    simp only [Finsupp.sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro g hg
    rw [← smul_add, ← smul_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hineq := cond_15_6_single_gene g (hpol g hg) 1
    simp only [show ¬ Even 1 from by decide, ↓reduceIte] at hineq
    linarith
  · simp only [if_neg heven]
    suffices h : (signature (prime Y)).2 + (signature (prime Y)).1 ≤
                 (signature Y).1 + (signature (prime (prime Y))).2 by linarith
    rw [signature_prime_snd₂, signature_prime_snd,
        signature_prime_fst, signature_fst]
    simp only [Finsupp.sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro g hg
    rw [← smul_add, ← smul_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hineq := cond_15_6_single_gene g (hpol g hg) 0
    simp only [show Even 0 from ⟨0, rfl⟩, ↓reduceIte] at hineq
    linarith
