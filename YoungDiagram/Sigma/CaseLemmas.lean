import YoungDiagram.Sigma.Basic
import YoungDiagram.Sigma.Diff

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

/-- For a polarized gene of rank ≥ 2, applying prime twice drops the signature by (1, 1). -/
lemma signature_sub_prime2_ofRank (g : Gene) (hε : g.type ≠ .NonPolarized)
    (hrank : 2 ≤ g.rank) :
    (Gene.ofRank g.rank g.type).signature -
      (Gene.ofRank (g.rank - 2) g.type).signature = (1, 1) := by
  cases hgt : g.type with
  | NonPolarized => exact absurd hgt hε
  | Positive =>
    rw [signature_ofRank_positive g.rank_pos,
        signature_ofRank_negative (by omega : 1 ≤ g.rank - 1),
        show g.rank - 1 - 1 = g.rank - 2 from by omega]
    abel_nf
    simp
  | Negative =>
    rw [signature_ofRank_negative g.rank_pos,
        signature_ofRank_positive (by omega : 1 ≤ g.rank - 1),
        show g.rank - 1 - 1 = g.rank - 2 from by omega]
    abel_nf
    simp

lemma b0_minus_b2_pol_gene (g : Gene) (hε : g.type ≠ .NonPolarized)
  (hrank : g.rank ≥ 2) :
  b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 1 := by
  have hb₀ : b (Finsupp.single g 1) 0 = (Gene.ofRank g.rank g.type).signature.2 := by
    simp only [sigma, Function.iterate_zero, id]
    rw [← Gene.ofRank_eq_gene]
  have hb₂ : b (Finsupp.single g 1) 2 = (Gene.ofRank (g.rank - 2) g.type).signature.2 := by
    simp only [sigma]
    rw [← Gene.ofRank_eq_gene, prime_iterate_ofRank]
  rw [hb₀, hb₂]
  have := congr_arg Prod.snd (signature_sub_prime2_ofRank g hε hrank)
  simpa using this

lemma b0_minus_b2 {X : Variety.Pi} (m : ℕ)
    (hm : m ≥ 2) (hmin : ∀ g ∈ X.val.support, m ≤ g.rank) :
    b X 0 - b X 2 = X.val.sum (fun _ n => n) := by
  -- Prove the equivalent statement for any Chromosome, then specialize.
  -- The rank-≥-m hypothesis lifts to rank ≥ 2 via hm.
  suffices h : ∀ (f : Chromosome),
      (∀ g ∈ f.support, g.type ≠ .NonPolarized) →
      (∀ g ∈ f.support, 2 ≤ g.rank) →
      b f 0 - b f 2 = f.sum (fun _ n => (n : ℚ)) by
    have hpol : ∀ g ∈ X.val.support, g.type ≠ .NonPolarized :=
      IsPolarized_def'.mp (Variety.mem_Pi_iff.mp X.2)
    exact_mod_cast h X.val hpol (fun g hg => hm.trans (hmin g hg))
  intro f
  -- Rewrite f as the sum of its individual genes via Finsupp.induction.
  -- At each step, sigma_linearity splits b (single g n + f') k = b (single g n) k + b f' k,
  -- and nsmul linearity gives b (single g n) k = n * b (single g 1) k.
  induction f using Finsupp.induction with
  | zero => simp [sigma, map_zero]
  | single_add g n f' hgf hn ih =>
    -- Finsupp.induction gives the term as (single g n + f')
    intro hpol hrank
    -- Lift hypotheses from (single g n + f').support to {g} and f'.support.
    have hmem_g : g ∈ (Finsupp.single g n + f').support := by
      simp [Finsupp.mem_support_iff, hn]
    have hsupp_mono : ∀ g' ∈ f'.support, g' ∈ (Finsupp.single g n + f').support := by
      intro g' hg'
      have hne : g' ≠ g := fun h => hgf (h ▸ hg')
      simp [Finsupp.mem_support_iff, Finsupp.add_apply, hne,
            Finsupp.mem_support_iff.mp hg']
    -- Conditions on the single gene g
    have hpol_g : g.type ≠ .NonPolarized := hpol g hmem_g
    have hrank_g : 2 ≤ g.rank := hrank g hmem_g
    -- Conditions on f' (for the inductive hypothesis)
    have hpol_f' : ∀ g' ∈ f'.support, g'.type ≠ .NonPolarized :=
      fun g' hg' => hpol g' (hsupp_mono g' hg')
    have hrank_f' : ∀ g' ∈ f'.support, 2 ≤ g'.rank :=
      fun g' hg' => hrank g' (hsupp_mono g' hg')
    -- Additivity: b (single g n + f') k = b (single g n) k + b f' k
    have hadd : ∀ k, b (Finsupp.single g n + f') k = b (Finsupp.single g n) k + b f' k :=
      fun k => congr_arg Prod.snd (sigma_linearity (X := Finsupp.single g n) (Y := f') (i := k))
    -- Nsmul linearity: b (single g n) k = n * b (single g 1) k,
    -- since single g n = n • single g 1 (smul_single_one g n)
    -- and sigma (n • Y) k = n • sigma Y k (iterate_map_nsmul + map_nsmul).
    have hnsmul : ∀ k, b (Finsupp.single g n) k = n * b (Finsupp.single g 1) k := by
      intro k
      have heq : Finsupp.single g n = n • Finsupp.single g 1 := (smul_single_one g n).symm
      simp only [sigma, heq, iterate_map_nsmul, map_nsmul, nsmul_eq_mul]
      simp
    -- The single-gene result: b (single g 1) 0 - b (single g 1) 2 = 1
    have hone : b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 1 :=
      b0_minus_b2_pol_gene g hpol_g hrank_g
    -- Inductive hypothesis applied to f'
    have ih' : b f' 0 - b f' 2 = f'.sum (fun _ k => (k : ℚ)) := ih hpol_f' hrank_f'
    -- Combine: b (single g n + f') 0 - b (single g n + f') 2
    --        = (b f' 0 - b f' 2) + n * (b (single g 1) 0 - b (single g 1) 2)
    --        = f'.sum ... + n * 1
    have key : b (Finsupp.single g n + f') 0 - b (Finsupp.single g n + f') 2 =
               (b f' 0 - b f' 2) + n * (b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2) := by
      simp only [hadd, hnsmul]; ring
    rw [key, ih', hone, mul_one]
    -- Finsupp.sum of (single g n + f') = n + Finsupp.sum f'
    rw [Finsupp.sum_add_index' (fun _ => by norm_cast) (fun _ _ _ => by push_cast; ring),
        Finsupp.sum_single_index (by norm_cast)]
    ring

lemma bk_minus_bk2 {X : Variety.Pi} (k m : ℕ)
    (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    (hk : k + 2 ≤ m) :
    b X k - b X (k + 2) = X.val.sum (fun _ n => n) := by
  -- Step 1: Reduce to b (prime^[k] X) 0 - b (prime^[k] X) 2.
  -- By sigma definition: b X k = (signature (prime^[k] X)).2 = b (prime^[k] X) 0.
  -- Similarly b X (k+2) = b (prime^[k] X) 2 via prime^[k+2] = prime^[2] ∘ prime^[k].
  have hbk : b X k = b (Chromosome.prime^[k] X) 0 := by
    simp [sigma, Function.iterate_zero]
  have hbk2 : b X (k + 2) = b (Chromosome.prime^[k] X) 2 := by
    simp only [sigma]
    rw [show k + 2 = 2 + k from Nat.add_comm k 2, Function.iterate_add_apply]
  rw [hbk, hbk2]
  -- Step 2: Let Y := prime^[k] X as a Variety.Pi element.
  let Y : Variety.Pi := ⟨Chromosome.prime^[k] X, Variety.prime_mem_Pi_iterate X.2⟩
  -- Step 3: All genes in Y have rank ≥ m - k ≥ 2.
  have hmin_Y : ∀ g ∈ Y.val.support, m - k ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff, prime_iterate_coeff] at hg
    have hgX : ⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ ∈ X.val.support :=
      Finsupp.mem_support_iff.mpr hg
    have := hmin _ hgX
    simp
    omega
  have hm_Y : m - k ≥ 2 := by omega
  -- Step 4: Apply b0_minus_b2 to Y.
  rw [show b (Chromosome.prime^[k] X) 0 = b Y 0 from rfl,
      show b (Chromosome.prime^[k] X) 2 = b Y 2 from rfl,
      b0_minus_b2 (m - k) hm_Y hmin_Y]
  -- Step 5: (prime^[k] X).sum (fun _ n => n) = X.val.sum (fun _ n => n).
  -- Via prime_iterate_coeff: g ↦ ⟨g.rank + k, g.type, _⟩ is a bijection
  -- from (prime^[k] X).support to X.val.support (since all ranks in X exceed k).
  simp only [Finsupp.sum, Y]
  -- Goal: ↑(∑ g ∈ (prime^[k] X).support, (prime^[k] X) g) = ↑(∑ g ∈ X.support, X g)
  -- Strip outer ℕ→ℚ casts, then prove ℕ equality via the bijection g ↦ ⟨g.rank+k, g.type, _⟩.
  norm_cast
  refine Finset.sum_bij'
      (fun g _ => (⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
      (fun g' hg' =>
        have hle : k + 2 ≤ g'.rank := by
          have := hmin g' (Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hg'))
          simp only at this; omega
        (⟨g'.rank - k, g'.type, by omega⟩ : Gene))
      ?_ ?_ ?_ ?_ ?_
  · -- forward maps into X.val.support
    intro g hg
    rw [Finsupp.mem_support_iff] at hg ⊢
    rwa [← prime_iterate_coeff]
  · -- backward maps into (prime^[k] X).support
    intro g' hg'
    rw [Finsupp.mem_support_iff] at hg' ⊢
    rw [prime_iterate_coeff]
    have hle : k ≤ g'.rank := by
      have := hmin g' (Finsupp.mem_support_iff.mpr hg'); simp only at this; omega
    simp only [Nat.sub_add_cancel hle]
    exact hg'
  · -- forward then backward = id
    intro g _; exact Gene.ext (Nat.add_sub_cancel g.rank k) rfl
  · -- backward then forward = id
    intro g' hg'
    have hle : k ≤ g'.rank := by
      have := hmin g' (Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hg'))
      simp only at this; omega
    exact Gene.ext (Nat.sub_add_cancel hle) rfl
  · -- coefficient preserved: (prime^[k] X) g = X.val ⟨g.rank + k, g.type, _⟩
    intro g _; rw [prime_iterate_coeff]

-- case 3
/-- If all genes in X have rank ≥ m, and all rank-m genes are positive,
    then for k ≤ m - 2 the b-sequence satisfies b₀ - bₖ = b₂ - b_{k+2}. -/
lemma b0_eq_b2_positive {X : Variety.Pi} (m : ℕ)
    (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    {k : ℕ} (hk : k ≤ m - 2) :
    b X 0 - b X k = b X 2 - b X (k + 2) := by
  by_cases hm : m ≥ 2
  · -- m ≥ 2: both b X 0 - b X 2 and b X k - b X (k+2) equal X.val.sum (fun _ n => n).
    have hk2 : k + 2 ≤ m := by omega
    have h1 := b0_minus_b2 m hm hmin
    have h2 := bk_minus_bk2 k m hmin hk2
    linarith
  · -- m < 2: k = 0 (since k ≤ m - 2 = 0 in ℕ), so both sides are 0.
    have hk0 : k = 0 := by omega
    subst hk0; ring

-- case 2
/-- If all genes in X have rank ≥ m, and all rank-m genes are negative,
    then for k ≤ m - 1 the b-sequence satisfies b₀ - bₖ = b₂ - b_{k+2}. -/
lemma b0_minus_b2_neg_gene (g : Gene) (hε : g.type = .Negative)
  (hrank : g.rank = 1) :
  b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 1 := by
  have hb₀ : b (Finsupp.single g 1) 0 = 1 := by
    simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
    rw [Gene.signature_of_negative hε, if_neg (show ¬Even g.rank by rw [hrank]; decide)]
    norm_num [hrank]
  have hb₂ : b (Finsupp.single g 1) 2 = 0 := by
    simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
               prime_single, one_nsmul, hε, hrank, Nat.sub_self, Gene.ofRank_zero, map_zero]
    rfl
  linarith

lemma b0_minus_b2_pos_gene (g : Gene) (hε : g.type = .Positive)
  (hrank : g.rank = 1) :
  b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 0 := by
  have hb₀ : b (Finsupp.single g 1) 0 = 0 := by
    simp only [sigma, Function.iterate_zero, id, signature_single g.rank_pos]
    rw [Gene.signature_of_positive hε, if_neg (show ¬Even g.rank by rw [hrank]; decide)]
    norm_num [hrank]
  have hb₂ : b (Finsupp.single g 1) 2 = 0 := by
    simp only [sigma, Function.iterate_succ_apply', Function.iterate_zero, id,
               prime_single, one_nsmul, hε, hrank, Nat.sub_self, Gene.ofRank_zero, map_zero]
    rfl
  linarith

lemma b0_minus_b2_min_neg {X : Variety.Pi} (m : ℕ)
    (hm : m ≥ 2) (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    (_hmin_type : ∀ g ∈ X.val.support, g.rank = m → g.type = .Negative) :
    b X 0 - b X 2 = X.val.sum (fun _ n => n) :=
  b0_minus_b2 m hm hmin

--note the bound are less strict
lemma bk_minus_bk2_min_neg {X : Variety.Pi} (k m : ℕ)
    (hk : k + 1 ≤ m) (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    (_hmin_type : ∀ g ∈ X.val.support, g.rank = m → g.type = .Negative) :
    b X k - b X (k + 2) = X.val.sum (fun _ n => n) := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · -- k + 1 = m; reduce to b (prime^[k] X) 0 - b (prime^[k] X) 2
    have hbk : b X k = b (Chromosome.prime^[k] X) 0 := by simp [sigma]
    have hbk2 : b X (k + 2) = b (Chromosome.prime^[k] X) 2 := by
      simp only [sigma]
      rw [show k + 2 = 2 + k from Nat.add_comm k 2, Function.iterate_add_apply]
    rw [hbk, hbk2]
    let Y : Variety.Pi := ⟨Chromosome.prime^[k] X, Variety.prime_mem_Pi_iterate X.2⟩
    -- Rank-1 genes in Y came from rank-(k+1) = rank-m genes in X, so are Negative by hmin_type.
    have hrank1_neg : ∀ g ∈ Y.val.support, g.rank = 1 → g.type = .Negative := by
      intro g hg hgr
      rw [Finsupp.mem_support_iff, prime_iterate_coeff] at hg
      have hgX : ⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ ∈ X.val.support :=
        Finsupp.mem_support_iff.mpr hg
      have hrank_eq : g.rank + k = m := by omega
      exact _hmin_type ⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ hgX hrank_eq
    have hb_Y : b Y 0 - b Y 2 = Y.val.sum (fun _ n => (n : ℚ)) := by
      suffices h : ∀ (f : Chromosome),
          (∀ g ∈ f.support, g.type ≠ .NonPolarized) →
          (∀ g ∈ f.support, g.rank = 1 → g.type = .Negative) →
          b f 0 - b f 2 = f.sum (fun _ n => (n : ℚ)) by
        exact h Y.val (IsPolarized_def'.mp (Variety.mem_Pi_iff.mp Y.2)) hrank1_neg
      intro f
      induction f using Finsupp.induction with
      | zero => simp [sigma, map_zero]
      | single_add g n f' hgf hn ih =>
        intro hpol hrneg
        have hmem_g : g ∈ (Finsupp.single g n + f').support := by
          simp [Finsupp.mem_support_iff, hn]
        have hsupp_mono : ∀ g' ∈ f'.support, g' ∈ (Finsupp.single g n + f').support := by
          intro g' hg'
          have hne : g' ≠ g := fun heq => hgf (heq ▸ hg')
          simp [Finsupp.mem_support_iff, Finsupp.add_apply, hne, Finsupp.mem_support_iff.mp hg']
        have hpol_g := hpol g hmem_g
        have hrneg_g := hrneg g hmem_g
        have hpol_f' : ∀ g' ∈ f'.support, g'.type ≠ .NonPolarized :=
          fun g' hg' => hpol g' (hsupp_mono g' hg')
        have hrneg_f' : ∀ g' ∈ f'.support, g'.rank = 1 → g'.type = .Negative :=
          fun g' hg' => hrneg g' (hsupp_mono g' hg')
        have hadd : ∀ i, b (Finsupp.single g n + f') i = b (Finsupp.single g n) i + b f' i :=
          fun i => congr_arg Prod.snd (sigma_linearity (X := Finsupp.single g n) (Y := f') (i := i))
        have hnsmul : ∀ i, b (Finsupp.single g n) i = n * b (Finsupp.single g 1) i := by
          intro i
          simp only [sigma, (smul_single_one g n).symm, iterate_map_nsmul, map_nsmul, nsmul_eq_mul]
          simp
        have hone : b (Finsupp.single g 1) 0 - b (Finsupp.single g 1) 2 = 1 := by
          by_cases hr : g.rank = 1
          · exact b0_minus_b2_neg_gene g (hrneg_g hr) hr
          · exact b0_minus_b2_pol_gene g hpol_g (by have := g.rank_pos; omega)
        have ih' := ih hpol_f' hrneg_f'
        have key : b (Finsupp.single g n + f') 0 - b (Finsupp.single g n + f') 2 =
                   (b f' 0 - b f' 2) + n * (b (Finsupp.single g 1) 0
                   - b (Finsupp.single g 1) 2) := by
          simp only [hadd, hnsmul]; ring
        rw [key, ih', hone, mul_one,
            Finsupp.sum_add_index' (fun _ => by norm_cast) (fun _ _ _ => by push_cast; ring),
            Finsupp.sum_single_index (by norm_cast)]
        ring
    have hsum : Y.val.sum (fun _ n => (n : ℚ)) = X.val.sum (fun _ n => (n : ℚ)) := by
      simp only [Finsupp.sum, Y]
      norm_cast
      refine Finset.sum_bij'
          (fun g _ => (⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
          (fun g' hg' =>
            have hle : k + 1 ≤ g'.rank := by
              have := hmin g' (Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hg'))
              simp only at this; omega
            (⟨g'.rank - k, g'.type, by omega⟩ : Gene))
          ?_ ?_ ?_ ?_ ?_
      · intro g hg
        rw [Finsupp.mem_support_iff] at hg ⊢
        rwa [← prime_iterate_coeff]
      · intro g' hg'
        rw [Finsupp.mem_support_iff] at hg' ⊢
        rw [prime_iterate_coeff]
        have hle : k ≤ g'.rank := by
          have := hmin g' (Finsupp.mem_support_iff.mpr hg'); simp only at this; omega
        simp only [Nat.sub_add_cancel hle]
        exact hg'
      · intro g _; exact Gene.ext (Nat.add_sub_cancel g.rank k) rfl
      · intro g' hg'
        have hle : k ≤ g'.rank := by
          have := hmin g' (Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hg'))
          simp only at this; omega
        exact Gene.ext (Nat.sub_add_cancel hle) rfl
      · intro g _; rw [prime_iterate_coeff]
    rw [show b (Chromosome.prime^[k] X) 0 = b Y 0 from rfl,
        show b (Chromosome.prime^[k] X) 2 = b Y 2 from rfl, hb_Y, hsum]
    norm_cast
  · -- k + 2 ≤ m
    exact bk_minus_bk2 k m hmin (by omega)

lemma b0_eq_b2_negative {X : Variety.Pi} (m : ℕ) (hm : m ≥ 2)
    (hmin : ∀ g ∈ X.val.support, m ≤ g.rank)
    (hpos : ∀ g ∈ X.val.support, g.rank = m → g.type = .Negative)
    {k : ℕ} (hk : k ≤ m - 1) :
    b X 0 - b X k = b X 2 - b X (k + 2) := by
  have h1 : b X 0 - b X 2 = X.val.sum (fun _ n => n) := b0_minus_b2 m hm hmin
  have h2 : b X k - b X (k + 2) = X.val.sum (fun _ n => n) :=
    bk_minus_bk2_min_neg k m (by omega) hmin hpos
  linarith

lemma bi_sum_ai1_eq_neg_count_1 {i : ℕ} (hX : X ∈ Variety.Pi) :
    b X i - a X (i + 1) =
     (prime^[i] X).sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
  -- b X i = b (prime^[i] X) 0, since sigma X i = signature (prime^[i] X)
  have hbᵢ : b X i = b (prime^[i] X) 0 := by simp [sigma]
  -- a X (i+1) = a (prime^[i] X) 1, since prime^[i+1] X = prime (prime^[i] X)
  have haᵢ : a X (i + 1) = a (prime^[i] X) 1 := by
    simp [sigma, Function.iterate_succ_apply']
  rw [hbᵢ, haᵢ]
  exact b0_sub_a1_eq_neg_count (prime^[i] X) (Variety.prime_mem_Pi_iterate hX)

lemma neg_count_eq_aux (hg : ∀ g ∈ X.support, g.rank = 1 → g.type = .Positive) :
    (prime X).sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
    X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
  rw [prime_def]
  rw [show (X.sum fun g m => m • primeGene g).sum
            (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
      X.sum (fun g m => (m • primeGene g).sum
           (fun g' n => if g'.type = .Negative then (n : ℚ) else 0)) from
    Finsupp.sum_sum_index (fun _ => by simp) (fun g m n => by split_ifs <;> push_cast <;> ring)]
  refine Finsupp.sum_congr (fun g hg_supp => ?_)
  by_cases hrank : g.rank = 1
  · have hpos : g.type = .Positive := hg g hg_supp hrank
    have hrank0 : g.rank - 1 = 0 := by omega
    simp [primeGene_def, hrank0, Gene.ofRank_zero, hpos]
  · have hne : g.rank - 1 ≠ 0 := by have := g.rank_pos; omega
    rw [primeGene_def, Gene.ofRank_is_gene hne]
    simp [Finsupp.sum_single_index]

/-- Iterating prime i times preserves the negative gene count, provided all genes
    of rank ≤ i in X are Positive (so prime^[i] kills no Negative genes). -/
lemma neg_count_eq (i : ℕ) (hg : ∀ g ∈ X.support, g.rank ≤ i → g.type = .Positive) :
    (prime^[i] X).sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
    X.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    -- Reduce prime (prime^[i] X) to prime^[i] X using neg_count_eq_aux,
    -- provided rank-1 genes of prime^[i] X are Positive.
    rw [neg_count_eq_aux (X := prime^[i] X) (fun g' hg'_supp hrank1 => by
      -- g' ∈ (prime^[i] X).support with rank 1 corresponds via prime_iterate_coeff
      -- to gene ⟨g'.rank + i, g'.type, _⟩ of rank i+1 in X.support
      have hcoeff := Finsupp.mem_support_iff.mp hg'_supp
      rw [prime_iterate_coeff] at hcoeff
      set g'' : Gene := ⟨g'.rank + i, g'.type, Nat.le_add_right_of_le g'.rank_pos⟩
      have hXsupp : g'' ∈ X.support := Finsupp.mem_support_iff.mpr hcoeff
      have hrank_le : g''.rank ≤ i + 1 := by change g'.rank + i ≤ i + 1; omega
      exact hg g'' hXsupp hrank_le)]
    -- Now apply the inductive hypothesis with the weakened rank bound
    exact ih (fun g hg_supp hrank_le => hg g hg_supp (Nat.le_succ_of_le hrank_le))

-- This is used in case 3
lemma b0_bi_eq_a1_ai1 (hX : X ∈ Variety.Pi) (i : ℕ)
    (hg : ∀ g ∈ X.support, g.rank ≤ i → g.type = .Positive) :
    b X 0 - b X i = a X 1 - a X (i + 1) := by
  -- b X 0 - a X 1 = neg_count X  (at index 0)
  have h0 := bi_sum_ai1_eq_neg_count_1 X hX (i := 0)
  simp at h0
  -- b X i - a X (i+1) = neg_count (prime^[i] X)  (at index i)
  have hi := bi_sum_ai1_eq_neg_count_1 X hX (i := i)
  -- neg_count (prime^[i] X) = neg_count X  (since rank-≤i genes are Positive)
  have heq := neg_count_eq X i hg
  linarith

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

lemma sigma_0_type2_same_rank {m : ℕ} (hm : 1 < m) :
    ∀ ε : GeneType, (hε : ε ≠ .NonPolarized) →
    let X : Chromosome := Pi.X2 hε (le_refl m) hm
    let Y : Chromosome := Pi.Y2 hε (le_refl m) hm
    sigma X 0 = sigma Y 0 := by
  induction m with
  | zero => omega
  | succ n ihn =>
    cases n with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        intro ε hε
        simp [Pi.X2_eq, Pi.Y2_eq, sigma]
        -- m = 2
        simp_all [signature_ofRank_even_half]
        have sig4 : signature (Gene.ofRank 4 ε) = (2, 2) := by
          rw [signature_ofRank_even_half (show Even 4 from ⟨2, rfl⟩)]; norm_num
        simp [sig4]
        norm_num
      | succ j =>
        intro ε hε
        -- m = j + 3 > 2
        simp [Pi.X2_eq, Pi.Y2_eq, sigma]
        ring_nf at ihn
        have : 1 < 2 + j := by omega
        ring_nf
        have h1 : 1 ≤ 1 + j := by omega
        have h2 : 1 ≤ 3 + j := by omega
        have h3 : 1 ≤ 5 + j := by omega
        simp [signature_ofRank_eq h1 hε,
              signature_ofRank_eq h2 hε,
              signature_ofRank_eq h3 hε]
        ring_nf
        rw [add_comm]
        abel_nf
        simp
        have hε1 : -ε ≠ .NonPolarized := GeneType.neg_ne_nonPolarized_iff.mp hε
        have ihn_neg := ihn this (-ε) hε1
        simp [sigma, Pi.X2_eq, Pi.Y2_eq] at ihn_neg
        ring_nf at ihn_neg
        have : j + 4 = 4 + j := by omega
        simp_all

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
      sigma Y i - sigma X i = if i = m then (1, 1)
                              else if i = m - 1 then
                                if ε = .Positive then (0, 1) else (1, 0)
                              else if ε = .Positive then (1, 0) else (0, 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Range 1: i ≤ m - 2
    intro i ih
    induction i with
    | zero =>
      simp [sigma_0_type2_same_rank hm ε hε]
    | succ n ihn =>
      by_cases hn : n + 1 = m - 2
      · -- n + 1 = m - 2
        simp_all [Pi.X2_eq, Pi.Y2_eq]
        simp [sigma_linearity]
        simp [sigma, prime_iterate_ofRank_eq_zero, prime_iterate_ofRank]
        have h1 : m - (m - 2) = 2 := by omega
        have h2 : m + 2 - (m - 2) = 4 := by omega
        simp [h1, h2]
        simp [signature_ofRank_even_half]
        have sig4 : signature (Gene.ofRank 4 ε) = (2, 2) := by
          rw [signature_ofRank_even_half (show Even 4 from ⟨2, rfl⟩)]; norm_num
        simp [sig4]
        norm_num
      · -- n + 1 ≠ m - 2
        have : n ≤ m - 2 := by omega
        simp_all [Pi.X2_eq, Pi.Y2_eq]
        simp_all [sigma, prime_iterate_ofRank]
        have : m - n ≥ 1 := by omega
        have h1 := signature_ofRank_diff this hε
        have h2 : signature (Gene.ofRank (m - (n + 1)) ε) = signature (Gene.ofRank (m - n) ε) -
            (if Even (m - n) then
              ((if ε = GeneType.Positive then 0 else 1),
               (if ε = GeneType.Negative then 0 else 1))
            else
              ((if ε = GeneType.Positive then 1 else 0),
               (if ε = GeneType.Negative then 1 else 0))) := by
          rw [← h1]; exact (sub_sub_cancel _ _).symm
        have h3 : signature (Gene.ofRank (m - 2 - (n + 1)) ε) =
            signature (Gene.ofRank (m - 2 - n) ε) -
            (if Even (m - 2 - n) then
              ((if ε = GeneType.Positive then 0 else 1),
               (if ε = GeneType.Negative then 0 else 1))
            else
              ((if ε = GeneType.Positive then 1 else 0),
               (if ε = GeneType.Negative then 1 else 0))) := by
          have := signature_ofRank_diff (show m - 2 - n ≥ 1 by omega) hε
          rw [← this]; exact (sub_sub_cancel _ _).symm
        have h4 : signature (Gene.ofRank (m + 1 - n) ε) =
            signature (Gene.ofRank (2 + m - n) ε) -
          (if Even (2 + m - n) then
              ((if ε = GeneType.Positive then 0 else 1),
               (if ε = GeneType.Negative then 0 else 1))
            else
              ((if ε = GeneType.Positive then 1 else 0),
               (if ε = GeneType.Negative then 1 else 0))) := by
          have : m + 1 - n =  2 + m - n - 1 := by omega
          rw [this]
          have := signature_ofRank_diff (show 2 + m - n ≥ 1 by omega) hε
          rw [← this]; exact (sub_sub_cancel _ _).symm
        simp [h2, h3, h4]
        ring_nf
        ring_nf at ihn
        simp [ihn]
        have e1 : Even (m -2 - n) = Even (2 + m - n) := by
          apply propext
          constructor
          · intro ⟨k, hk⟩; exact ⟨k + 2, by omega⟩
          · intro ⟨k, hk⟩; exact ⟨k - 2, by omega⟩
        have e2 : Even (2 + m - n) = Even (m - n) := by
          have : 2 + m - n - 2 = m - n := by omega
          apply propext
          constructor
          · intro ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
          · intro ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
        simp [e1]
        ring_nf
        simp [e2]
  · -- Range 2: m + 2 ≤ i
    intro i ih
    simp [Pi.X2_eq, Pi.Y2_eq, sigma]
    have ih' : i ≥ m := by linarith
    have ih'' : i ≥ (m - 2) := by omega
    simp [prime_iterate_ofRank_eq_zero ih,
      prime_iterate_ofRank_eq_zero ih',
      prime_iterate_ofRank_eq_zero ih'']
  · -- Range 3: m - 1 ≤ i ≤ m + 1
    intro i hi1 hi2
    have hcases : i = m - 1 ∨ i = m ∨ i = m + 1 := by omega
    rcases hcases with rfl | rfl | rfl
    · -- i = m - 1
      simp only [Pi.X2_eq, Pi.Y2_eq, sigma]
      simp only [iterate_map_add, prime_iterate_ofRank, map_add]
      have h1 : m - (m - 1) = 1 := by omega
      have h2 : m - 2 - (m - 1) = 0 := by omega
      have h3 : m + 2 - (m - 1) = 3 := by omega
      simp only [h2, Gene.ofRank_zero, map_zero, h3, zero_add, h1]
      rcases ε with _ | _ | _
      · -- ε = NonPolarized (impossible)
        simp_all
      · -- ε = Positive
        have hsig3 : (Gene.ofRank 3 .Positive).signature = (2, 1) := by
          simp [signature_ofRank, Gene.signature_of_positive, show ¬Even 3 from by decide]; norm_num
        simp_all
        ring_nf
        simp
        omega
      · -- ε = Negative
        have hsig3 : (Gene.ofRank 3 .Negative).signature = (1, 2) := by
          simp [signature_ofRank, Gene.signature_of_negative, show ¬Even 3 from by decide]; norm_num
        simp_all
        ring_nf
        simp
        omega
    · -- i = m
      simp [Pi.X2_eq, Pi.Y2_eq, sigma,
            prime_iterate_ofRank_eq_zero,
            prime_iterate_ofRank,
            signature_ofRank_even_half]
    · -- i = m + 1
      simp only [Pi.X2_eq, Pi.Y2_eq, sigma]
      simp only [iterate_map_add, prime_iterate_ofRank, map_add]
      have h1 : m - (m + 1) = 0 := by omega
      have h2 : (m - 2) - (m + 1) = 0 := by omega
      have h3 : (m + 2) - (m + 1) = 1 := by omega
      simp only [h2, Gene.ofRank_zero, map_zero, h3, zero_add, h1, add_zero, sub_zero,
        Nat.add_eq_left, one_ne_zero, ↓reduceIte]
      rcases ε with _ | _ | _
      · -- ε = NonPolarized (impossible)
        exact absurd rfl hε
      · -- ε = Positive
        simp [signature_ofRank_one_positive]
        omega
      · -- ε = Negative
        simp [signature_ofRank_one_negative]
        omega

lemma sigma_type2_mn_rank {m n : ℕ} (ε : GeneType) (hε : ε ≠ .NonPolarized)
  (hmn : m < n) (hm : 1 < m) :
    let hle : m ≤ n := Nat.le_of_lt hmn
    let X : Chromosome := Pi.X2 hε hle hm
    let Y : Chromosome := Pi.Y2 hε hle hm
    (∀ i, i ≤ m - 2 → sigma X i = sigma Y i) ∧
    (∀ i, n + 2 ≤ i → sigma X i = sigma Y i) ∧
    (∀ i, m - 1 ≤ i → i ≤ n + 1 →
      sigma Y i - sigma X i = if (i > m - 1) ∧ (i < n + 1) then (1, 1)
                              else if i = m - 1 then
                                if ε = .Positive then (0, 1) else (1, 0)
                              else
                                if ε = .Positive then (1, 0) else (0, 1)) := by
  have h1 : ∀ i, i ≤ m - 2 →
      sigma (Pi.X2 hε (Nat.le_of_lt hmn) hm) i =
      sigma (Pi.Y2 hε (Nat.le_of_lt hmn) hm) i := by
    intro i hi
    simp only [Pi.X2_eq, Pi.Y2_eq, sigma, iterate_map_add, prime_iterate_ofRank, map_add]
    rw [signature_ofRank_eq₂ (k := m - i) (by omega) hε,
        signature_ofRank_eq₂ (k := n + 2 - i) (by omega) hε,
        show m - i - 2 = m - 2 - i from by omega,
        show n + 2 - i - 2 = n - i from by omega]
    abel
  have h2 : ∀ i, n + 2 ≤ i →
      sigma (Pi.X2 hε (Nat.le_of_lt hmn) hm) i =
      sigma (Pi.Y2 hε (Nat.le_of_lt hmn) hm) i := by
    intro i ih
    simp only [Pi.X2_eq, Pi.Y2_eq, sigma, iterate_map_add, prime_iterate_ofRank, map_add]
    -- After prime_iterate_ofRank, goal is in terms of Gene.ofRank (k - i) ε.
    -- Since n + 2 ≤ i, all rank subtractions are 0 in Nat.
    simp only [show m - i = 0 from by omega, show n - i = 0 from by omega,
               show m - 2 - i = 0 from by omega, show n + 2 - i = 0 from by omega,
               Gene.ofRank_zero, map_zero, add_zero]
  have h3 : ∀ i, m - 1 ≤ i → i ≤ n + 1 →
      sigma (Pi.Y2 hε (Nat.le_of_lt hmn) hm) i -
      sigma (Pi.X2 hε (Nat.le_of_lt hmn) hm) i =
      if (i > m - 1) ∧ (i < n + 1) then (1, 1)
      else if i = m - 1 then
        if ε = .Positive then (0, 1) else (1, 0)
      else if ε = .Positive then (1, 0) else (0, 1) := by
    intro i hi1 hi2
    rcases (show i = m - 1 ∨ (m - 1 < i ∧ i < n + 1) ∨ i = n + 1 by omega) with
        rfl | ⟨him, hin⟩ | rfl
    · -- i = m - 1
      simp only [show ¬((m - 1 > m - 1) ∧ (m - 1 < n + 1)) from by omega, if_false, if_true]
      simp only [Pi.X2_eq, Pi.Y2_eq, sigma]
      simp only [iterate_map_add, prime_iterate_ofRank, map_add]
      have h1 : m - (m - 1) = 1 := by omega
      have h2 : m - 2 - (m - 1) = 0 := by omega
      simp only [h2, Gene.ofRank_zero, map_zero, zero_add, h1]
      rcases ε with _ | _ | _
      · exact absurd rfl hε
      · have hsig3' : (Gene.ofRank (n + 2 - (m - 1)) .Positive).signature =
            (Gene.ofRank (n - (m - 1)) .Positive).signature + (1, 1) := by
          rw [← show n + 2 - (m - 1) - 2 = n - (m - 1) from by omega]
          exact signature_ofRank_positive₂ (by omega)
        simp only [hsig3', signature_ofRank_one_positive, if_true]
        ring_nf
        simp
      · have hsig3' : (Gene.ofRank (n + 2 - (m - 1)) .Negative).signature =
            (Gene.ofRank (n - (m - 1)) .Negative).signature + (1, 1) := by
          rw [← show n + 2 - (m - 1) - 2 = n - (m - 1) from by omega]
          exact signature_ofRank_eq₂ (by omega) (by decide)
        simp only [hsig3', signature_ofRank_one_negative]
        ring_nf
        simp
    · -- m - 1 < i < n + 1
      simp only [show (i > m - 1) ∧ (i < n + 1) from ⟨him, hin⟩]
      simp
      simp [Pi.X2_eq, Pi.Y2_eq, sigma, prime_iterate_ofRank]
      have h1 : m - 2 - i = 0 := by omega
      have h2 : m - i = 0 := by omega
      simp [h1, h2]
      have h3 : 2 ≤ n + 2 - i := by omega
      simp [signature_ofRank_eq₂ h3 hε]
      have h4 : n + 2 - i - 2 = n - i := by omega
      simp [h4]
    · -- i = n + 1
      simp only [show ¬((n + 1 > m - 1) ∧ (n + 1 < n + 1)) from by omega, if_false,
                 show n + 1 ≠ m - 1 from by omega, if_false]
      simp only [Pi.X2_eq, Pi.Y2_eq, sigma]
      simp only [iterate_map_add, prime_iterate_ofRank, map_add]
      have h1 : n - (n + 1) = 0 := by omega
      have h2 : (m - 2) - (n + 1) = 0 := by omega
      have h3 : (n + 2) - (n + 1) = 1 := by omega
      have h4 : m - (n + 1) = 0 := by omega
      simp only [h2, Gene.ofRank_zero, map_zero, h3, zero_add, h1, add_zero, sub_zero, h4]
      rcases ε with _ | _ | _
      · -- ε = NonPolarized (impossible)
        exact absurd rfl hε
      · -- ε = Positive
        simp [signature_ofRank_one_positive]
      · -- ε = Negative
        simp [signature_ofRank_one_negative]
  exact ⟨h1, h2, h3⟩

end Sigma
