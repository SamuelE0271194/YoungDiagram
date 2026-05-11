import YoungDiagram.Sigma.Basic

open Chromosome Finsupp

namespace Sigma

variable (X : Chromosome)

local notation "a" X:max k:max => Prod.fst (sigma X k)

local notation "b" X:max k:max => Prod.snd (sigma X k)

lemma single_b0_eq_a1_of_positive (g : Gene) (hgt : g.type = .Positive) :
    b(Finsupp.single g 1)0 = a(Finsupp.single g 1)1 := by
  rcases Nat.even_or_odd g.rank with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hk : 1 ≤ g.rank - 1 := by have := g.rank_pos; omega
    have hb₀ : b(Finsupp.single g 1)0 = (g.rank : ℚ) / 2 := by
      simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
      rw [Gene.signature_of_positive hgt, if_pos ⟨j, hj⟩]; simp
    have ha₁ : a(Finsupp.single g 1)1 = ((↑(g.rank - 1) : ℚ) + 1) / 2 := by
      simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
        prime_single, one_nsmul, hgt]
      rw [show Gene.ofRank (g.rank - 1) GeneType.Positive =
            Finsupp.single (⟨g.rank - 1, GeneType.Positive, hk⟩ : Gene) 1 from
            @Gene.ofRank_eq_gene ⟨g.rank - 1, GeneType.Positive, hk⟩,
          signature_single hk, Gene.signature_of_positive rfl,
          if_neg (show ¬Even (g.rank - 1) by rw [Nat.even_iff, hj]; omega)]
      simp
    rw [ha₁, hb₀]
    linarith [show (↑(g.rank - 1) : ℚ) + 1 = g.rank
      by exact_mod_cast Nat.sub_add_cancel g.rank_pos]
  · by_cases h1 : g.rank = 1
    · have hb₀ : b(Finsupp.single g 1)0 = 0 := by
        simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
        rw [Gene.signature_of_positive hgt,
            if_neg (show ¬Even g.rank by rw [Nat.even_iff, hj]; omega)]
        norm_num [h1]
      have ha₁ : a(Finsupp.single g 1)1 = 0 := by
        simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
          prime_single, one_nsmul, hgt, h1, Nat.sub_self, Gene.ofRank_zero, map_zero]
        rfl
      linarith
    · have hk : 1 ≤ g.rank - 1 := by omega
      have hb₀ : b(Finsupp.single g 1)0 = ((g.rank : ℚ) - 1) / 2 := by
        simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
        rw [Gene.signature_of_positive hgt,
            if_neg (show ¬Even g.rank by rw [Nat.even_iff, hj]; omega)]
        simp
      have ha₁ : a(Finsupp.single g 1)1 = (↑(g.rank - 1) : ℚ) / 2 := by
        simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
          prime_single, one_nsmul, hgt]
        rw [show Gene.ofRank (g.rank - 1) GeneType.Positive =
              Finsupp.single (⟨g.rank - 1, GeneType.Positive, hk⟩ : Gene) 1 from
              @Gene.ofRank_eq_gene ⟨g.rank - 1, GeneType.Positive, hk⟩,
            signature_single hk, Gene.signature_of_positive rfl,
            if_pos (show Even (g.rank - 1) by rw [Nat.even_iff, hj]; omega)]
        simp
      rw [ha₁, hb₀]
      linarith [show (↑(g.rank - 1) : ℚ) = g.rank - 1
        by exact_mod_cast Nat.cast_sub g.rank_pos]

lemma single_b0_eq_a1_add_one_of_negative (g : Gene) (hgt : g.type = .Negative) :
    b(Finsupp.single g 1)0 = a(Finsupp.single g 1)1 + 1 := by
  rcases Nat.even_or_odd g.rank with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hk : 1 ≤ g.rank - 1 := by have := g.rank_pos; omega
    have hb₀ : b(Finsupp.single g 1)0 = (g.rank : ℚ) / 2 := by
      simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
      rw [Gene.signature_of_negative hgt, if_pos ⟨j, hj⟩]; simp
    have ha₁ : a(Finsupp.single g 1)1 = ((↑(g.rank - 1) : ℚ) - 1) / 2 := by
      simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
        prime_single, one_nsmul, hgt]
      rw [show Gene.ofRank (g.rank - 1) GeneType.Negative =
            Finsupp.single (⟨g.rank - 1, GeneType.Negative, hk⟩ : Gene) 1 from
            @Gene.ofRank_eq_gene ⟨g.rank - 1, GeneType.Negative, hk⟩,
          signature_single hk, Gene.signature_of_negative rfl,
          if_neg (show ¬Even (g.rank - 1) by rw [Nat.even_iff, hj]; omega)]
      simp
    rw [ha₁, hb₀]
    linarith [show (↑(g.rank - 1) : ℚ) + 1 = g.rank
      by exact_mod_cast Nat.sub_add_cancel g.rank_pos]
  · by_cases h1 : g.rank = 1
    · have hb₀ : b(Finsupp.single g 1)0 = 1 := by
        simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
        rw [Gene.signature_of_negative hgt,
            if_neg (show ¬Even g.rank by rw [Nat.even_iff, hj]; omega)]
        norm_num [h1]
      have ha₁ : a(Finsupp.single g 1)1 = 0 := by
        simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
          prime_single, one_nsmul, hgt, h1, Nat.sub_self, Gene.ofRank_zero, map_zero]
        rfl
      linarith
    · have hk : 1 ≤ g.rank - 1 := by omega
      have hb₀ : b(Finsupp.single g 1)0 = ((g.rank : ℚ) + 1) / 2 := by
        simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
        rw [Gene.signature_of_negative hgt,
            if_neg (show ¬Even g.rank by rw [Nat.even_iff, hj]; omega)]
        simp
      have ha₁ : a(Finsupp.single g 1)1 = (↑(g.rank - 1) : ℚ) / 2 := by
        simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
          prime_single, one_nsmul, hgt]
        rw [show Gene.ofRank (g.rank - 1) GeneType.Negative =
              Finsupp.single (⟨g.rank - 1, GeneType.Negative, hk⟩ : Gene) 1 from
              @Gene.ofRank_eq_gene ⟨g.rank - 1, GeneType.Negative, hk⟩,
            signature_single hk, Gene.signature_of_negative rfl,
            if_pos (show Even (g.rank - 1) by rw [Nat.even_iff, hj]; omega)]
        simp
      rw [ha₁, hb₀]
      linarith [show (↑(g.rank - 1) : ℚ) = g.rank - 1
        by exact_mod_cast Nat.cast_sub g.rank_pos]

lemma neg_type_of_b0_gt_a1_single (g : Gene) (hg : Finsupp.single g 1 ∈ Variety.Pi)
    (h : a(Finsupp.single g 1)1 < b(Finsupp.single g 1)0) :
    g.type = .Negative := by
  have hpol : g.type ≠ .NonPolarized :=
    (Chromosome.IsPolarized_def'.mp (Variety.mem_Pi_iff.mp hg)) g
      (Finsupp.mem_support_iff.mpr (by simp))
  cases hgt : g.type with
  | Negative => rfl
  | Positive =>
    linarith [single_b0_eq_a1_of_positive g hgt]
  | NonPolarized => exact absurd hgt hpol

lemma pos_type_of_b0_le_a1_single (g : Gene) (hg : Finsupp.single g 1 ∈ Variety.Pi)
    (h : a(Finsupp.single g 1)1 ≥ b(Finsupp.single g 1)0) :
    g.type = .Positive := by
  have hpol : g.type ≠ .NonPolarized :=
    (Chromosome.IsPolarized_def'.mp (Variety.mem_Pi_iff.mp hg)) g
      (Finsupp.mem_support_iff.mpr (by simp))
  cases hgt : g.type with
  | Positive => rfl
  | Negative =>
    linarith [single_b0_eq_a1_add_one_of_negative g hgt]
  | NonPolarized => exact absurd hgt hpol

lemma b0_sub_a1_eq_neg_count (hX : X ∈ Variety.Pi) :
    b X 0 - a X 1 = X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
  have hb₀ : b X 0 = X.sum (fun g n => n • b(Finsupp.single g 1)0) := by
    simp [sigma, signature_snd]
  have ha₁ : a X 1 = X.sum (fun g n => n • a(Finsupp.single g 1)1) := by
    simp [sigma, signature_prime_fst]
  rw [hb₀, ha₁]
  simp only [Finsupp.sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  have hpol : g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (Variety.mem_Pi_iff.mp hX) g hg
  cases hgt : g.type with
  | NonPolarized => exact absurd hgt hpol
  | Positive =>
    simp only [reduceCtorEq, ↓reduceIte]
    have hba := single_b0_eq_a1_of_positive g hgt
    rw [hba]
    simp
  | Negative =>
    simp only [↓reduceIte, nsmul_eq_mul]
    have hba := single_b0_eq_a1_add_one_of_negative g hgt
    rw [hba]
    ring

lemma neg_gene_of_b0_gt_a1 (hX : X ∈ Variety.Pi)
    (h : a X 1 < b X 0) :
    ∃ g : Gene, g.type = .Negative ∧ 0 < X g := by
  have hsum : 0 < X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
    have hcount := b0_sub_a1_eq_neg_count X hX
    linarith
  by_contra hnone
  push Not at hnone
  have hzero : X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) = 0 := by
    rw [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro g hg
    by_cases hneg : g.type = .Negative
    · have hg0 : X g = 0 := by
        have := hnone g hneg
        omega
      simp [hneg, hg0]
    · simp [hneg]
  linarith

/-- Sigma invariants of the type2 mutation X2 → Y2 when both genes have the same rank m.
    The source X2 = 2·gene(m,ε) and the target Y2 = gene(m-2,ε) + gene(m+2,ε) agree on sigma
    outside the window [m-1, m+1], and differ by (1,0) (resp. (0,1)) inside
    when m is even (resp. odd). -/
lemma sigma_type2_same_rank {m : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized) (hm : 1 < m) :
    let X : Chromosome := Pi.X2 hε (le_refl m) hm
    let Y : Chromosome := Pi.Y2 hε (le_refl m) hm
    (∀ i, i ≤ m - 2 → sigma X i = sigma Y i) ∧
    (∀ i, m + 2 ≤ i → sigma X i = sigma Y i) ∧
    (∀ i, m - 1 ≤ i → i ≤ m + 1 →
      sigma X i - sigma Y i = if i = m then (1, 1)
                              else if Even m then (1, 0) else (0, 1)) := by
  sorry

end Sigma
