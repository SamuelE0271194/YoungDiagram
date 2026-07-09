import YoungDiagram.Theorem6.MixPi2Lambda.Window
import YoungDiagram.Sigma.Diff

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

lemma fst_add_one_le_of_one_one_add_le {x y : ℚ × ℚ}
    (h : ((1 : ℚ), (1 : ℚ)) + x ≤ y) : x.1 + 1 ≤ y.1 := by
  have hfst : (1 : ℚ) + x.1 ≤ y.1 := h.1
  linarith

lemma snd_add_one_le_of_one_one_add_le {x y : ℚ × ℚ}
    (h : ((1 : ℚ), (1 : ℚ)) + x ≤ y) : x.2 + 1 ≤ y.2 := by
  have hsnd : (1 : ℚ) + x.2 ≤ y.2 := h.2
  linarith

lemma polarized_same_type_of_not_neg {ε δ : GeneType}
    (hε : ε ≠ GeneType.NonPolarized) (hδ : δ ≠ GeneType.NonPolarized)
    (hnot : ¬ δ = -ε) :
    δ = ε := by
  cases ε <;> cases δ <;> simp at hε hδ hnot ⊢

lemma no_pair_neg_gene_zero {X : Chromosome}
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = GeneType.Positive ∧ gneg.type = GeneType.Negative ∧
      0 < X gpos ∧ 0 < X gneg)
    {g : Gene} (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hXg : 0 < X g) :
    X (-g) = 0 := by
  by_contra hne
  have hXneg : 0 < X (-g) := Nat.pos_of_ne_zero hne
  cases hg_type : g.type with
  | NonPolarized => exact hg_pol hg_type
  | Positive =>
      exact hno_pair ⟨g, -g, by simp, hg_type, by rw [Gene.neg_type, hg_type]; rfl,
        hXg, hXneg⟩
  | Negative =>
      exact hno_pair ⟨-g, g, by simp, by rw [Gene.neg_type, hg_type]; rfl, hg_type,
        hXneg, hXg⟩

lemma single_pred_succ_drop_fst_negative {q : ℕ} {g : Gene}
    (hrank : g.rank = 2 * q + 3) (hneg : g.type = GeneType.Negative) :
    (Sigma.sigma (Finsupp.single g 1 : Chromosome) (2 * q + 2)).1 -
        (Sigma.sigma (Finsupp.single g 1 : Chromosome) (2 * q + 4)).1 = 0 := by
  have hsingle : (Finsupp.single g 1 : Chromosome) = Gene.ofRank g.rank g.type :=
    Gene.ofRank_eq_gene.symm
  rw [hsingle, Sigma.sigma, Sigma.sigma, prime_iterate_ofRank, prime_iterate_ofRank]
  have hpred : g.rank - (2 * q + 2) = 1 := by omega
  have hsucc : g.rank - (2 * q + 4) = 0 := by omega
  rw [hpred, hsucc, Gene.ofRank_zero, map_zero, hneg, signature_ofRank_one_negative]
  norm_num

lemma single_pred_succ_drop_snd_positive {q : ℕ} {g : Gene}
    (hrank : g.rank = 2 * q + 3) (hpos : g.type = GeneType.Positive) :
    (Sigma.sigma (Finsupp.single g 1 : Chromosome) (2 * q + 2)).2 -
        (Sigma.sigma (Finsupp.single g 1 : Chromosome) (2 * q + 4)).2 = 0 := by
  have hsingle : (Finsupp.single g 1 : Chromosome) = Gene.ofRank g.rank g.type :=
    Gene.ofRank_eq_gene.symm
  rw [hsingle, Sigma.sigma, Sigma.sigma, prime_iterate_ofRank, prime_iterate_ofRank]
  have hpred : g.rank - (2 * q + 2) = 1 := by omega
  have hsucc : g.rank - (2 * q + 4) = 0 := by omega
  rw [hpred, hsucc, Gene.ofRank_zero, map_zero, hpos, signature_ofRank_one_positive]
  norm_num

lemma sigma_fst_drop_le_totalMult_of_Pi {X : Chromosome}
    (hXPi : X ∈ Pi) (k : ℕ) :
    (Sigma.sigma X k).1 - (Sigma.sigma X (k + 1)).1 ≤
      (Chromosome.prime^[k] X).sum (fun _ m => (m : ℚ)) := by
  rw [Sigma.sigma_fst_diff X k hXPi]
  exact Finsupp.sum_le_sum fun g m => by
    by_cases htype :
        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive
    · simp [htype]
    · simp [htype]

lemma sigma_snd_drop_le_totalMult_of_Pi {X : Chromosome}
    (hXPi : X ∈ Pi) (k : ℕ) :
    (Sigma.sigma X k).2 - (Sigma.sigma X (k + 1)).2 ≤
      (Chromosome.prime^[k] X).sum (fun _ m => (m : ℚ)) := by
  rw [Sigma.sigma_snd_diff X k hXPi]
  exact Finsupp.sum_le_sum fun g m => by
    by_cases htype :
        g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Negative
    · simp [htype]
    · simp [htype]

lemma cond_15_7_even_index {m i : ℕ} (Y : nMixPi2Lambda (m + 2))
    (hi : Even i) :
    (signature (Chromosome.prime^[i + 1] Y.1.1)).1 -
        (signature (Chromosome.prime^[i + 2] Y.1.1)).1 ≤
      (signature (Chromosome.prime^[i] Y.1.1)).2 -
        (signature (Chromosome.prime^[i + 1] Y.1.1)).2 := by
  simpa [Sigma.sigma, hi] using
    Mix2LambdaSection17.cond_15_7_Mix_Pi_2Lambda Y.1.2 i

lemma cond_15_6_even_index {m i : ℕ} (Y : nMixPi2Lambda (m + 2))
    (hi : Even i) :
    (signature (Chromosome.prime^[i + 1] Y.1.1)).2 -
        (signature (Chromosome.prime^[i + 2] Y.1.1)).2 ≤
      (signature (Chromosome.prime^[i] Y.1.1)).1 -
        (signature (Chromosome.prime^[i + 1] Y.1.1)).1 := by
  simpa [Sigma.sigma, hi] using
    Mix2LambdaSection17.cond_15_6_Mix_Pi_2Lambda Y.1.2 i

lemma cond_15_7_two_mul {m p : ℕ} (Y : nMixPi2Lambda (m + 2)) :
    (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 -
        (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).1 ≤
      (signature (Chromosome.prime^[2 * p] Y.1.1)).2 -
        (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 := by
  simpa using cond_15_7_even_index (i := 2 * p) Y ⟨p, by ring⟩

lemma cond_15_6_two_mul {m p : ℕ} (Y : nMixPi2Lambda (m + 2)) :
    (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).2 -
        (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).2 ≤
      (signature (Chromosome.prime^[2 * p] Y.1.1)).1 -
        (signature (Chromosome.prime^[2 * p + 1] Y.1.1)).1 := by
  simpa using cond_15_6_even_index (i := 2 * p) Y ⟨p, by ring⟩

lemma cond_15_7_two_mul_add_two {m q : ℕ} (Y : nMixPi2Lambda (m + 2)) :
    (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 -
        (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1 ≤
      (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 -
        (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 := by
  simpa using cond_15_7_even_index (i := 2 * q + 2) Y ⟨q + 1, by ring⟩

lemma cond_15_6_two_mul_add_two {m q : ℕ} (Y : nMixPi2Lambda (m + 2)) :
    (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 -
        (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2 ≤
      (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 -
        (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 := by
  simpa using cond_15_6_even_index (i := 2 * q + 2) Y ⟨q + 1, by ring⟩

lemma totalMult_cast_eq_sigma_zero_sub_sigma_one (X : Chromosome) :
    X.sum (fun _ n => (n : ℚ)) =
      (Sigma.sigma X 0).1 + (Sigma.sigma X 0).2 -
        ((Sigma.sigma X 1).1 + (Sigma.sigma X 1).2) := by
  have h0 : (Sigma.sigma X 0).1 + (Sigma.sigma X 0).2 =
      (X.rank : ℚ) := by
    simpa [Sigma.sigma] using (@signature_sum_eq_rank X)
  have h1 : (Sigma.sigma X 1).1 + (Sigma.sigma X 1).2 =
      (X.prime.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[1] X)
    simpa [Sigma.sigma, Function.iterate_one] using this
  have hcells := MixLambdaPi.cells (Z := X)
  linarith

lemma totalMult_cast_eq_of_nat_eq {X Y : Chromosome}
    (h : X.sum (fun _ n => n) = Y.sum (fun _ n => n)) :
    X.sum (fun _ n => (n : ℚ)) = Y.sum (fun _ n => (n : ℚ)) := by
  exact_mod_cast h

lemma totalMult_cast_eq_sub_one_of_nat_add_one {X Y : Chromosome}
    (h : X.sum (fun _ n => n) + 1 = Y.sum (fun _ n => n)) :
    X.sum (fun _ n => (n : ℚ)) = Y.sum (fun _ n => (n : ℚ)) - 1 := by
  have hq : X.sum (fun _ n => (n : ℚ)) + 1 = Y.sum (fun _ n => (n : ℚ)) := by exact_mod_cast h
  linarith

lemma totalMult_cast_eq_sub_two_of_nat_add_two {X Y : Chromosome}
    (h : X.sum (fun _ n => n) + 2 = Y.sum (fun _ n => n)) :
    X.sum (fun _ n => (n : ℚ)) = Y.sum (fun _ n => (n : ℚ)) - 2 := by
  have hq : X.sum (fun _ n => (n : ℚ)) + 2 = Y.sum (fun _ n => (n : ℚ)) := by exact_mod_cast h
  linarith

lemma totalMult_le_rank (X : Chromosome) :
    X.sum (fun _ n => n) ≤ X.rank := by
  rw [rank_def, Finsupp.sum, Finsupp.sum]
  exact Finset.sum_le_sum fun g _ => by
    simpa [smul_eq_mul, mul_comm] using
      Nat.le_mul_of_pos_right (X g) g.rank_pos

lemma totalMult_sub_single_one {X : Chromosome} {gm : Gene}
    (hgm1 : X gm = 1) :
    (X - Finsupp.single gm 1).sum (fun _ n => n) + 1 =
      X.sum (fun _ n => n) := by
  have hsub : X = (X - Finsupp.single gm 1) + Finsupp.single gm 1 := by
    ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : gm = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  conv_rhs => rw [hsub]
  rw [Finsupp.sum_add_index (by simp) (by intros; simp),
    Finsupp.sum_single_index (by simp)]

lemma totalMult_sub_single_one_cast {X : Chromosome} {gm : Gene}
    (hgm1 : X gm = 1) :
    (X - Finsupp.single gm 1).sum (fun _ n => (n : ℚ)) =
      X.sum (fun _ n => (n : ℚ)) - 1 :=
  totalMult_cast_eq_sub_one_of_nat_add_one (totalMult_sub_single_one hgm1)

lemma totalMult_sub_two_single_one {X : Chromosome} {g₁ g₂ : Gene}
    (hg₁ : X g₁ = 1) (hg₂ : (X - Finsupp.single g₁ 1 : Chromosome) g₂ = 1) :
    (X - Finsupp.single g₁ 1 - Finsupp.single g₂ 1).sum (fun _ n => n) + 2 =
      X.sum (fun _ n => n) := by
  have h1 := totalMult_sub_single_one hg₁
  have h2 := totalMult_sub_single_one (X := X - Finsupp.single g₁ 1) (gm := g₂) hg₂
  omega

lemma totalMult_sub_two_single_one_cast {X : Chromosome} {g₁ g₂ : Gene}
    (hg₁ : X g₁ = 1) (hg₂ : (X - Finsupp.single g₁ 1 : Chromosome) g₂ = 1) :
    (X - Finsupp.single g₁ 1 - Finsupp.single g₂ 1).sum (fun _ n => (n : ℚ)) =
    X.sum (fun _ n => (n : ℚ)) - 2 :=
  totalMult_cast_eq_sub_two_of_nat_add_two (totalMult_sub_two_single_one hg₁ hg₂)

lemma totalMult_sub_single_one_of_pos {X : Chromosome} {gm : Gene}
    (hgm : 0 < X gm) :
    (X - Finsupp.single gm 1).sum (fun _ n => n) + 1 =
      X.sum (fun _ n => n) := by
  have hsub : X = (X - Finsupp.single gm 1) + Finsupp.single gm 1 := by
    ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : gm = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  conv_rhs => rw [hsub]
  rw [Finsupp.sum_add_index (by simp) (by intros; simp),
    Finsupp.sum_single_index (by simp)]

lemma totalMult_sub_double_single {X : Chromosome} {gm : Gene}
    (hgm2 : 2 ≤ X gm) :
    (X - Finsupp.single gm 1 - Finsupp.single gm 1).sum (fun _ n => n) + 2 =
      X.sum (fun _ n => n) := by
  have hfirst : 0 < X gm := by omega
  have hsecond :
      0 < (X - Finsupp.single gm 1 : Chromosome) gm := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have h1 := totalMult_sub_single_one_of_pos (X := X) (gm := gm) hfirst
  have h2 := totalMult_sub_single_one_of_pos
    (X := X - Finsupp.single gm 1) (gm := gm) hsecond
  omega

lemma prime_iterate_eq_sub_single_of_rank_le_of_pos
    {X : Chromosome} {gm : Gene} (hgm : 0 < X gm)
    {i : ℕ} (hi : gm.rank ≤ i) :
    Chromosome.prime^[i] X =
      Chromosome.prime^[i] (X - Finsupp.single gm 1) := by
  have hsingle_zero : Chromosome.prime^[i] (Finsupp.single gm 1 : Chromosome) = 0 := by
    rw [← Chromosome.prime_iterate_eq_zero_rank_le]
    intro g hg
    rw [Finsupp.support_single _ (by norm_num), Finset.mem_singleton] at hg
    subst hg
    exact hi
  have hsub : X = (X - Finsupp.single gm 1) + Finsupp.single gm 1 := by
    ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : gm = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  conv_lhs => rw [hsub]
  rw [iterate_map_add, hsingle_zero, add_zero]

lemma prime_iterate_eq_sub_single_of_rank_le
    {X : Chromosome} {gm : Gene} (hgm1 : X gm = 1)
    {i : ℕ} (hi : gm.rank ≤ i) :
    Chromosome.prime^[i] X =
      Chromosome.prime^[i] (X - Finsupp.single gm 1) :=
  prime_iterate_eq_sub_single_of_rank_le_of_pos (by omega) hi

lemma prime_iterate_eq_sub_double_single_of_rank_le
    {X : Chromosome} {gm : Gene} (hgm2 : 2 ≤ X gm)
    {i : ℕ} (hi : gm.rank ≤ i) :
    Chromosome.prime^[i] X =
      Chromosome.prime^[i] (X - Finsupp.single gm 1 - Finsupp.single gm 1) := by
  have hfirst : 0 < X gm := by omega
  have hsecond :
      0 < (X - Finsupp.single gm 1 : Chromosome) gm := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  rw [prime_iterate_eq_sub_single_of_rank_le_of_pos
    (X := X) (gm := gm) hfirst hi]
  rw [prime_iterate_eq_sub_single_of_rank_le_of_pos
    (X := X - Finsupp.single gm 1) (gm := gm) hsecond hi]

/-- First-component upper-edge drop: from levels `1` to `3`, every gene of rank
at least `2` contributes one cell, provided the rank-`2` genes are positive. -/
lemma edge_drop_fst_eq_totalMult_positive {W : Chromosome}
    (hW : ∀ g ∈ W.support, 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Positive)) :
    (Sigma.sigma W 1).1 - (Sigma.sigma W 3).1 =
      W.sum (fun _ m => (m : ℚ)) := by
  induction W using Finsupp.induction with
  | zero => simp [Sigma.sigma]
  | single_add g n f hg hn ih =>
      have hgr : 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Positive) := hW g (by simp [hn])
      have hf : ∀ g' ∈ f.support, 2 ≤ g'.rank ∧ (g'.rank = 2 → g'.type = .Positive) := by
        intro g' hg'
        apply hW
        simp only [Finsupp.mem_support_iff, Finsupp.add_apply]
        have hz : (Finsupp.single g n) g' = 0 := by
          rw [Finsupp.single_apply, if_neg]
          rintro rfl
          exact hg hg'
        rw [hz, zero_add]
        exact Finsupp.mem_support_iff.mp hg'
      have he : (Finsupp.single g n : Chromosome) = n • Gene.ofRank g.rank g.type := by
        rw [Gene.ofRank_eq_gene]
        simp
      have e1 : Chromosome.prime^[1] (Finsupp.single g n) =
          n • Gene.ofRank (g.rank - 1) g.type := by
        rw [he, iterate_map_nsmul, prime_iterate_ofRank]
      have e3 : Chromosome.prime^[3] (Finsupp.single g n) =
          n • Gene.ofRank (g.rank - 3) g.type := by
        rw [he, iterate_map_nsmul, prime_iterate_ofRank]
      have hsingle : (Sigma.sigma (Finsupp.single g n) 1).1 -
          (Sigma.sigma (Finsupp.single g n) 3).1 = (n : ℚ) := by
        simp only [Sigma.sigma, e1, e3, map_nsmul]
        rcases Nat.lt_or_ge g.rank 3 with hlt | hge
        · have hr2 : g.rank = 2 := by omega
          have hpos : g.type = .Positive := hgr.2 hr2
          rw [hr2, hpos, show (2 - 1 : ℕ) = 1 from rfl, show (2 - 3 : ℕ) = 0 from rfl,
            signature_ofRank_one_positive, signature_ofRank_zero]
          simp
        · rw [show g.rank - 1 = (g.rank - 3) + 2 from by omega, signature_ofRank_eq₂']
          simp only [Prod.smul_fst, Prod.fst_add]
          ring
      rw [Finsupp.sum_add_index (by simp) (by intros; simp), Finsupp.sum_single_index (by simp),
        Sigma.sigma_linearity, Sigma.sigma_linearity, Prod.fst_add, Prod.fst_add]
      linarith [hsingle, ih hf]

/-- Second-component upper-edge drop: from levels `1` to `3`, every gene of
rank at least `2` contributes one cell, provided the rank-`2` genes are
negative. -/
lemma edge_drop_snd_eq_totalMult_negative {W : Chromosome}
    (hW : ∀ g ∈ W.support, 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Negative)) :
    (Sigma.sigma W 1).2 - (Sigma.sigma W 3).2 =
      W.sum (fun _ m => (m : ℚ)) := by
  induction W using Finsupp.induction with
  | zero => simp [Sigma.sigma]
  | single_add g n f hg hn ih =>
      have hgr : 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Negative) := hW g (by simp [hn])
      have hf : ∀ g' ∈ f.support, 2 ≤ g'.rank ∧ (g'.rank = 2 → g'.type = .Negative) := by
        intro g' hg'
        apply hW
        simp only [Finsupp.mem_support_iff, Finsupp.add_apply]
        have hz : (Finsupp.single g n) g' = 0 := by
          rw [Finsupp.single_apply, if_neg]
          rintro rfl
          exact hg hg'
        rw [hz, zero_add]
        exact Finsupp.mem_support_iff.mp hg'
      have he : (Finsupp.single g n : Chromosome) = n • Gene.ofRank g.rank g.type := by
        rw [Gene.ofRank_eq_gene]
        simp
      have e1 : Chromosome.prime^[1] (Finsupp.single g n) =
          n • Gene.ofRank (g.rank - 1) g.type := by
        rw [he, iterate_map_nsmul, prime_iterate_ofRank]
      have e3 : Chromosome.prime^[3] (Finsupp.single g n) =
          n • Gene.ofRank (g.rank - 3) g.type := by
        rw [he, iterate_map_nsmul, prime_iterate_ofRank]
      have hsingle : (Sigma.sigma (Finsupp.single g n) 1).2 -
          (Sigma.sigma (Finsupp.single g n) 3).2 = (n : ℚ) := by
        simp only [Sigma.sigma, e1, e3, map_nsmul]
        rcases Nat.lt_or_ge g.rank 3 with hlt | hge
        · have hr2 : g.rank = 2 := by omega
          have hneg : g.type = .Negative := hgr.2 hr2
          rw [hr2, hneg, show (2 - 1 : ℕ) = 1 from rfl, show (2 - 3 : ℕ) = 0 from rfl,
            signature_ofRank_one_negative, signature_ofRank_zero]
          simp
        · rw [show g.rank - 1 = (g.rank - 3) + 2 from by omega, signature_ofRank_eq₂']
          simp only [Prod.smul_snd, Prod.snd_add]
          ring
      rw [Finsupp.sum_add_index (by simp) (by intros; simp), Finsupp.sum_single_index (by simp),
        Sigma.sigma_linearity, Sigma.sigma_linearity, Prod.snd_add, Prod.snd_add]
      linarith [hsingle, ih hf]

lemma edge_drop_fst_eq_totalMult_positive_iterate {W : Chromosome} {i : ℕ}
    (hW : ∀ g ∈ (Chromosome.prime^[i] W).support,
      2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Positive)) :
    (Sigma.sigma W (1 + i)).1 - (Sigma.sigma W (3 + i)).1 =
      (Chromosome.prime^[i] W).sum (fun _ m => (m : ℚ)) := by
  have hdrop := edge_drop_fst_eq_totalMult_positive (W := Chromosome.prime^[i] W) hW
  have h1 : Chromosome.prime^[1] (Chromosome.prime^[i] W) =
      Chromosome.prime^[1 + i] W := by
    rw [← Function.iterate_add_apply]
  have h3 : Chromosome.prime^[3] (Chromosome.prime^[i] W) =
      Chromosome.prime^[3 + i] W := by
    rw [← Function.iterate_add_apply]
  simpa [Sigma.sigma, Function.iterate_one, Function.iterate_succ, h1, h3] using hdrop

lemma edge_drop_snd_eq_totalMult_negative_iterate {W : Chromosome} {i : ℕ}
    (hW : ∀ g ∈ (Chromosome.prime^[i] W).support,
      2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Negative)) :
    (Sigma.sigma W (1 + i)).2 - (Sigma.sigma W (3 + i)).2 =
      (Chromosome.prime^[i] W).sum (fun _ m => (m : ℚ)) := by
  have hdrop := edge_drop_snd_eq_totalMult_negative (W := Chromosome.prime^[i] W) hW
  have h1 : Chromosome.prime^[1] (Chromosome.prime^[i] W) =
      Chromosome.prime^[1 + i] W := by
    rw [← Function.iterate_add_apply]
  have h3 : Chromosome.prime^[3] (Chromosome.prime^[i] W) =
      Chromosome.prime^[3 + i] W := by
    rw [← Function.iterate_add_apply]
  simpa [Sigma.sigma, Function.iterate_one, Function.iterate_succ, h1, h3] using hdrop

lemma one_le_signature_prime_pred_fst_of_positive {X : Chromosome} {gpos : Gene}
    (hgpos : gpos.type = .Positive) (hXgpos : 0 < X gpos) :
    1 ≤ (signature (Chromosome.prime^[gpos.rank - 1] X)).1 := by
  let r := gpos.rank
  have hr : 1 ≤ r := gpos.rank_pos
  have hgpos_single : Gene.ofRank r .Positive = (Finsupp.single gpos 1 : Chromosome) := by
    rw [← hgpos]; exact Gene.ofRank_eq_gene (g := gpos)
  have hprime_gpos : Chromosome.prime^[r - 1] (Finsupp.single gpos 1 : Chromosome) =
      Gene.ofRank 1 .Positive := by
    rw [← hgpos_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
  have hXeq : X = Finsupp.single gpos 1 + (X - Finsupp.single gpos 1) := by
    rw [add_comm, sub_single_add_single_eq hXgpos]
  calc (1 : ℚ)
      = (signature (Gene.ofRank 1 .Positive : Chromosome)).1 := by
        simp [signature_ofRank_one_positive]
    _ = (signature (Chromosome.prime^[r - 1] (Finsupp.single gpos 1 : Chromosome))).1 := by
        rw [hprime_gpos]
    _ ≤ (signature (Chromosome.prime^[r - 1] X)).1 := by
        conv_rhs => rw [hXeq]
        rw [iterate_map_add, map_add]
        exact le_add_of_nonneg_right (signature_nonneg _).1

lemma one_le_signature_prime_pred_snd_of_negative {X : Chromosome} {gneg : Gene}
    (hgneg : gneg.type = .Negative) (hXgneg : 0 < X gneg) :
    1 ≤ (signature (Chromosome.prime^[gneg.rank - 1] X)).2 := by
  let r := gneg.rank
  have hr : 1 ≤ r := gneg.rank_pos
  have hgneg_single : Gene.ofRank r .Negative = (Finsupp.single gneg 1 : Chromosome) := by
    rw [← hgneg]; exact Gene.ofRank_eq_gene (g := gneg)
  have hprime_gneg : Chromosome.prime^[r - 1] (Finsupp.single gneg 1 : Chromosome) =
      Gene.ofRank 1 .Negative := by
    rw [← hgneg_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
  have hXeq : X = Finsupp.single gneg 1 + (X - Finsupp.single gneg 1) := by
    rw [add_comm, sub_single_add_single_eq hXgneg]
  calc (1 : ℚ)
      = (signature (Gene.ofRank 1 .Negative : Chromosome)).2 := by
        simp [signature_ofRank_one_negative]
    _ = (signature (Chromosome.prime^[r - 1] (Finsupp.single gneg 1 : Chromosome))).2 := by
        rw [hprime_gneg]
    _ ≤ (signature (Chromosome.prime^[r - 1] X)).2 := by
        conv_rhs => rw [hXeq]
        rw [iterate_map_add, map_add]
        exact le_add_of_nonneg_right (signature_nonneg _).2

lemma signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
    {W : Chromosome} {p : ℕ}
    (hpol_top : ∀ g : Gene, 0 < W g → g.rank = 2 * p + 1 →
      g.type ≠ GeneType.NonPolarized)
    (hrank : ∀ g : Gene, 0 < W g → g.rank ≤ 2 * p + 1)
    (hno : W ⟨2 * p + 1, GeneType.Positive, by omega⟩ = 0) :
    (signature (Chromosome.prime^[2 * p] W)).1 = 0 := by
  rw [signature_fst, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro g hg
  by_cases hcoeff : (Chromosome.prime^[2 * p] W) g = 0
  · simp [hcoeff]
  · have hcoeff_pos : 0 < (Chromosome.prime^[2 * p] W) g :=
      Nat.pos_of_ne_zero hcoeff
    let g0 : Gene :=
      ⟨g.rank + 2 * p, g.type, Nat.le_add_right_of_le g.rank_pos⟩
    have hg0_pos : 0 < W g0 := by
      simpa [g0, prime_iterate_coeff] using hcoeff_pos
    have hg_rank : g.rank = 1 := by
      have hle := hrank g0 hg0_pos
      dsimp [g0] at hle
      change g.rank + 2 * p ≤ 2 * p + 1 at hle
      have hpos := g.rank_pos
      omega
    have hg0_rank : g0.rank = 2 * p + 1 := by
      dsimp [g0]
      rw [hg_rank]
      omega
    have hg_pol : g.type ≠ GeneType.NonPolarized := hpol_top g0 hg0_pos hg0_rank
    have hg_not_pos : g.type ≠ GeneType.Positive := by
      intro hpos
      have hg0_eq :
          g0 = ⟨2 * p + 1, GeneType.Positive, by omega⟩ := by
        ext
        · exact hg0_rank
        · dsimp [g0]
          exact hpos
      have : 0 < W ⟨2 * p + 1, GeneType.Positive, by omega⟩ := by
        simpa [hg0_eq] using hg0_pos
      rw [hno] at this
      omega
    have hg_neg : g.type = GeneType.Negative := by
      cases htype : g.type
      · exact False.elim (hg_pol htype)
      · exact False.elim (hg_not_pos htype)
      · rfl
    simp [Gene.signature, hg_rank, hg_neg]

lemma signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
    {W : Chromosome} {p : ℕ}
    (hpol_top : ∀ g : Gene, 0 < W g → g.rank = 2 * p + 1 →
      g.type ≠ GeneType.NonPolarized)
    (hrank : ∀ g : Gene, 0 < W g → g.rank ≤ 2 * p + 1)
    (hno : W ⟨2 * p + 1, GeneType.Negative, by omega⟩ = 0) :
    (signature (Chromosome.prime^[2 * p] W)).2 = 0 := by
  rw [signature_snd, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro g hg
  by_cases hcoeff : (Chromosome.prime^[2 * p] W) g = 0
  · simp [hcoeff]
  · have hcoeff_pos : 0 < (Chromosome.prime^[2 * p] W) g :=
      Nat.pos_of_ne_zero hcoeff
    let g0 : Gene :=
      ⟨g.rank + 2 * p, g.type, Nat.le_add_right_of_le g.rank_pos⟩
    have hg0_pos : 0 < W g0 := by
      simpa [g0, prime_iterate_coeff] using hcoeff_pos
    have hg_rank : g.rank = 1 := by
      have hle := hrank g0 hg0_pos
      dsimp [g0] at hle
      change g.rank + 2 * p ≤ 2 * p + 1 at hle
      have hpos := g.rank_pos
      omega
    have hg0_rank : g0.rank = 2 * p + 1 := by
      dsimp [g0]
      rw [hg_rank]
      omega
    have hg_pol : g.type ≠ GeneType.NonPolarized := hpol_top g0 hg0_pos hg0_rank
    have hg_not_neg : g.type ≠ GeneType.Negative := by
      intro hneg
      have hg0_eq :
          g0 = ⟨2 * p + 1, GeneType.Negative, by omega⟩ := by
        ext
        · exact hg0_rank
        · dsimp [g0]
          exact hneg
      have : 0 < W ⟨2 * p + 1, GeneType.Negative, by omega⟩ := by
        simpa [hg0_eq] using hg0_pos
      rw [hno] at this
      omega
    have hg_pos : g.type = GeneType.Positive := by
      cases htype : g.type
      · exact False.elim (hg_pol htype)
      · rfl
      · exact False.elim (hg_not_neg htype)
    simp [Gene.signature, hg_rank, hg_pos]

end MixPi2Lambda
