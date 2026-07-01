import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

private lemma exists_mutation_le_no_pair_rank_one_double
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_two : 2 ≤ X.1.1 g) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

private lemma exists_mutation_le_no_pair_rank_one_singleton_second_double
    {m p q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_one : X.1.1 g = 1)
    (hg₂_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g₂)
    (hg₂min : ∀ g' : Gene,
      0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g' →
        g₂.rank ≤ g'.rank)
    (hXg₂ : 0 < X.1.1 g₂)
    (hne_g₂_g : g₂ ≠ g)
    (hne_g₂_neg : g₂ ≠ -g)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hg₂_two : 2 ≤ X.1.1 g₂) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

private lemma exists_mutation_le_no_pair_rank_one_singleton_later_distinct
    {m p q₂ q₃ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ g₃ : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_one : X.1.1 g = 1)
    (hg₂_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g₂)
    (hg₂min : ∀ g' : Gene,
      0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g' →
        g₂.rank ≤ g'.rank)
    (hXg₂ : 0 < X.1.1 g₂)
    (hne_g₂_g : g₂ ≠ g)
    (hne_g₂_neg : g₂ ≠ -g)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hg₂_one : X.1.1 g₂ = 1)
    (restAfterG₂ : Chromosome)
    (hg₃_rest : 0 < restAfterG₂ g₃)
    (hg₃min : ∀ g' : Gene, 0 < restAfterG₂ g' → g₃.rank ≤ g'.rank)
    (hXg₃ : 0 < X.1.1 g₃)
    (hne_g₃_g : g₃ ≠ g)
    (hne_g₃_g₂ : g₃ ≠ g₂)
    (hg₃_pol : g₃.type ≠ GeneType.NonPolarized)
    (hg₂_le_g₃ : g₂.rank ≤ g₃.rank)
    (hg₃_rank_q : g₃.rank = 2 * q₃ + 3)
    (hq₂_le_q₃ : q₂ ≤ q₃) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

private lemma exists_mutation_le_no_pair_rank_one_singleton_multiplicity_boundary
    {m p q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_one : X.1.1 g = 1)
    (hg₂_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g₂)
    (hg₂min : ∀ g' : Gene,
      0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g' →
        g₂.rank ≤ g'.rank)
    (hXg₂ : 0 < X.1.1 g₂)
    (hne_g₂_g : g₂ ≠ g)
    (hne_g₂_neg : g₂ ≠ -g)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hg₂_one : X.1.1 g₂ = 1)
    (restAfterG₂ : Chromosome)
    (hrest₂_empty : ¬ restAfterG₂ ≠ 0) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

private lemma exists_mutation_le_no_pair_rank_one_singleton
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_one : X.1.1 g = 1)
    (g₂ : Gene)
    (hg₂_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g₂)
    (hg₂min : ∀ g' : Gene,
      0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g' →
        g₂.rank ≤ g'.rank) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXg₂ : 0 < X.1.1 g₂ := by
    exact lt_of_lt_of_le hg₂_rest (Nat.sub_le _ _)
  have hne_g₂_g : g₂ ≠ g := by
    intro h
    subst h
    simp [hg_one] at hg₂_rest
  have hne_g₂_neg : g₂ ≠ -g := by
    intro h
    subst h
    rw [hXneg_zero] at hXg₂
    omega
  have hg₂_pol : g₂.type ≠ GeneType.NonPolarized := by
    exact IsPolarized_def'.mp hXpol g₂
      (Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂))
  have hg₂_odd : Odd g₂.rank := by
    exact Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
      X.1.2 hXg₂ hg₂_pol
  have hg₂_rank_ge_three : 3 ≤ g₂.rank := by
    have hmin_le := hgmin g₂ hXg₂
    rw [hg_rank_one] at hmin_le
    obtain ⟨n₂, hg₂_rank_raw⟩ := hg₂_odd
    by_contra hnot
    have hg₂_rank_one : g₂.rank = 1 := by omega
    have hrank_eq : g₂.rank = g.rank := by omega
    cases hg_type : g.type with
    | NonPolarized => exact hg_pol hg_type
    | Positive =>
        cases hg₂_type : g₂.type with
        | NonPolarized => exact hg₂_pol hg₂_type
        | Positive =>
            exact hne_g₂_g (Gene.ext hrank_eq (by rw [hg₂_type, hg_type]))
        | Negative =>
            exact hno_pair ⟨g, g₂, hrank_eq.symm, hg_type, hg₂_type, hgX, hXg₂⟩
    | Negative =>
        cases hg₂_type : g₂.type with
        | NonPolarized => exact hg₂_pol hg₂_type
        | Positive =>
            exact hno_pair ⟨g₂, g, hrank_eq, hg₂_type, hg_type, hXg₂, hgX⟩
        | Negative =>
            exact hne_g₂_g (Gene.ext hrank_eq (by rw [hg₂_type, hg_type]))
  obtain ⟨n₂, hg₂_rank_raw⟩ := hg₂_odd
  have hn₂_pos : 0 < n₂ := by
    rw [hg₂_rank_raw] at hg₂_rank_ge_three
    omega
  let q₂ := n₂ - 1
  have hn₂_eq : n₂ = q₂ + 1 := by omega
  have hg₂_rank_q : g₂.rank = 2 * q₂ + 3 := by omega
  have hXprime1_ne : Chromosome.prime^[1] X.1.1 ≠ 0 := by
    change X.1.1.prime ≠ 0
    intro hprime
    have hall :=
      (Chromosome.prime_iterate_eq_zero_rank_le (X := X.1.1) (k := 1)).2 hprime
    have hg₂_supp : g₂ ∈ X.1.1.support :=
      Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂)
    have hle := hall g₂ hg₂_supp
    omega
  have hYprime1_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
    intro hYzero
    have hle := le_iff_dominates.mp hXY.le 1
    rw [hYzero, map_zero] at hle
    exact hXprime1_ne (signature_eq_zero (le_antisymm hle (signature_nonneg _)))
  have hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank :=
    h17_1 1 (by omega) hYprime1_ne
  have hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2 := by
    exact Mix2LambdaSection17.seed_strict_lt_at_odd
      X.1.2 Y.1.2 (i := 1) (by decide) hr1
  by_cases hg₂_two : 2 ≤ X.1.1 g₂
  · -- There are already two later copies; the type10 source will use
    -- `g₂ + g₂`, with the rank-one gene left in the rest.
    exact exists_mutation_le_no_pair_rank_one_singleton_second_double
      X Y hXY hcommon h17_1 hXpol hno_pair g g₂ hgX hgmin hg_pol hp hp0
      hg_rank_one hXneg_zero hg_one hg₂_rest hg₂min hXg₂ hne_g₂_g
      hne_g₂_neg hg₂_pol hg₂_rank_q hseed1 hg₂_two
  · have hg₂_one : X.1.1 g₂ = 1 := by omega
    let restAfterG₂ : Chromosome :=
      X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1
    by_cases hrest₂_ne : restAfterG₂ ≠ 0
    · obtain ⟨g₃, hg₃_rest, hg₃min⟩ :=
        Mix2LambdaSection17.exists_min_rank_gene hrest₂_ne
      have hXg₃ : 0 < X.1.1 g₃ := by
        dsimp [restAfterG₂] at hg₃_rest
        exact lt_of_lt_of_le hg₃_rest (by
          omega)
      have hne_g₃_g : g₃ ≠ g := by
        intro h
        subst h
        dsimp [restAfterG₂] at hg₃_rest
        simp [hg_one, hne_g₂_g.symm] at hg₃_rest
      have hne_g₃_g₂ : g₃ ≠ g₂ := by
        intro h
        subst h
        dsimp [restAfterG₂] at hg₃_rest
        simp [hg₂_one, hne_g₂_g] at hg₃_rest
      have hg₃_pol : g₃.type ≠ GeneType.NonPolarized := by
        exact IsPolarized_def'.mp hXpol g₃
          (Finsupp.mem_support_iff.mpr (ne_of_gt hXg₃))
      have hg₃_odd : Odd g₃.rank := by
        exact Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
          X.1.2 hXg₃ hg₃_pol
      have hg₂_le_g₃ : g₂.rank ≤ g₃.rank := by
        have hg₃_restAfterG : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g₃ := by
          dsimp [restAfterG₂] at hg₃_rest
          exact lt_of_lt_of_le hg₃_rest (Nat.sub_le _ _)
        exact hg₂min g₃ hg₃_restAfterG
      obtain ⟨n₃, hg₃_rank_raw⟩ := hg₃_odd
      have hn₃_pos : 0 < n₃ := by
        rw [hg₃_rank_raw] at hg₂_le_g₃
        rw [hg₂_rank_q] at hg₂_le_g₃
        omega
      let q₃ := n₃ - 1
      have hn₃_eq : n₃ = q₃ + 1 := by omega
      have hg₃_rank_q : g₃.rank = 2 * q₃ + 3 := by omega
      have hq₂_le_q₃ : q₂ ≤ q₃ := by
        rw [hg₂_rank_q, hg₃_rank_q] at hg₂_le_g₃
        omega
      exact exists_mutation_le_no_pair_rank_one_singleton_later_distinct
        X Y hXY hcommon h17_1 hXpol hno_pair g g₂ g₃ hgX hgmin hg_pol hp hp0
        hg_rank_one hXneg_zero hg_one hg₂_rest hg₂min hXg₂ hne_g₂_g
        hne_g₂_neg hg₂_pol hg₂_rank_q hseed1 hg₂_one restAfterG₂
        hg₃_rest hg₃min hXg₃ hne_g₃_g hne_g₃_g₂ hg₃_pol hg₂_le_g₃
        hg₃_rank_q hq₂_le_q₃
    · -- Boundary: after `g` and one copy of `g₂`, no later source remains.
      -- This is the formal place where the informal proof uses the
      -- `s₁-r₁ ≥ 2` multiplicity gap to rule the case out.
      exact exists_mutation_le_no_pair_rank_one_singleton_multiplicity_boundary
        X Y hXY hcommon h17_1 hXpol hno_pair g g₂ hgX hgmin hg_pol hp hp0
        hg_rank_one hXneg_zero hg_one hg₂_rest hg₂min hXg₂ hne_g₂_g
        hne_g₂_neg hg₂_pol hg₂_rank_q hseed1 hg₂_one restAfterG₂ hrest₂_ne

lemma exists_mutation_le_no_pair_rank_one
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg_rank_one : g.rank = 1 := by omega
  have hXneg_zero : X.1.1 (-g) = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hnegX
    cases htype : g.type with
    | NonPolarized => exact hg_pol htype
    | Positive =>
        exact hno_pair ⟨g, -g, by simp, htype, by simp [htype], hgX, hnegX⟩
    | Negative =>
        exact hno_pair ⟨-g, g, by simp, by simp [htype], htype, hnegX, hgX⟩
  by_cases hg_two : 2 ≤ X.1.1 g
  · exact exists_mutation_le_no_pair_rank_one_double X Y hXY hcommon h17_1
      hXpol hno_pair g hgX hgmin hg_pol hp hp0 hg_rank_one hXneg_zero hg_two
  · have hg_one : X.1.1 g = 1 := by omega
    let restAfterG : Chromosome := X.1.1 - Finsupp.single g 1
    have hrest_ne : restAfterG ≠ 0 := by
      intro hzero
      change X.1.1 - Finsupp.single g 1 = 0 at hzero
      have hXeq : X.1.1 = Finsupp.single g 1 := by
        rw [← sub_single_add_single_eq hgX, hzero]
        simp
      have hrankX : X.1.1.rank = 1 := by
        rw [hXeq, rank_single, one_smul, hg_rank_one]
      rw [X.2] at hrankX
      omega
    obtain ⟨g₂, hg₂_rest, hg₂min⟩ :=
      Mix2LambdaSection17.exists_min_rank_gene hrest_ne
    exact exists_mutation_le_no_pair_rank_one_singleton X Y hXY hcommon h17_1
      hXpol hno_pair g hgX hgmin hg_pol hp hp0 hg_rank_one hXneg_zero
      hg_one g₂ hg₂_rest hg₂min

end Mix2LambdaPi
