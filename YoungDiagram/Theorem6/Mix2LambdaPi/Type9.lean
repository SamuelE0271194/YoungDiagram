import YoungDiagram.Theorem6.Mix2LambdaPi.Case1
import YoungDiagram.Theorem6.Mix2LambdaPrelim

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

private lemma type9_signature_eq_before
    {p j : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (hj : j < 2 * p + 2) :
    signature (Chromosome.prime^[j] (Y9 hε p).1) =
      signature (Chromosome.prime^[j] (X9 p).1) := by
  have h1 : j ≤ 2 * p + 1 := by omega
  have h2 : j ≤ 2 * p + 2 := by omega
  have h3 : j ≤ 2 * p + 3 := by omega
  simp only [X9_eq, Y9_eq, iterate_map_add, prime_iterate_ofRank, map_add,
    signature_ofRank_nonPolarized]
  have heq : 2 * p + 3 - j - 2 = 2 * p + 1 - j := by omega
  rw [signature_ofRank_eq₂ (k := 2 * p + 3 - j) (by omega),
    ← add_assoc, signature_ofRank_sum_even, heq]
  · simp only [Nat.cast_sub h2, Nat.cast_sub h1,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor <;> ring
  · rw [Nat.even_iff]
    omega

private lemma type9_signature_eq_after
    {p j : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (hj : 2 * p + 3 ≤ j) :
    signature (Chromosome.prime^[j] (Y9 hε p).1) =
      signature (Chromosome.prime^[j] (X9 p).1) := by
  simp only [X9_eq, Y9_eq, iterate_map_add, prime_iterate_ofRank]
  have h1 : 2 * p + 1 - j = 0 := by omega
  have h2 : 2 * p + 2 - j = 0 := by omega
  have h3 : 2 * p + 3 - j = 0 := by omega
  simp [h1, h2, h3, Gene.ofRank_zero]

private lemma type9_signature_mid
    {p : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    signature (Chromosome.prime^[2 * p + 2] (Y9 hε p).1) =
      signature (Chromosome.prime^[2 * p + 2] (X9 p).1) +
        signature (Gene.ofRank 1 (-ε)) := by
  simp only [X9_eq, Y9_eq, iterate_map_add, prime_iterate_ofRank]
  have h1 : 2 * p + 1 - (2 * p + 2) = 0 := by omega
  have h2 : 2 * p + 2 - (2 * p + 2) = 0 := by omega
  have h3 : 2 * p + 3 - (2 * p + 2) = 1 := by omega
  simp [h1, h3, Gene.ofRank_zero]

/-- The first reduction in §17 for Label 3: replace a double nonpolarized
gene by the type9 target. -/
lemma exists_mutation_le_type9
    {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (p : ℕ) (g : Gene)
    (hgNP : g.type = .NonPolarized)
    (hgrank : g.rank = 2 * p + 2)
    (hXg2 : 2 ≤ X.1.1 g) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome := X.1.1 - Finsupp.single g 2
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_two_mem_Mix_2Lambda_Pi X.1.2
      (show Even g.rank by rw [hgrank]; exact ⟨p + 1, by ring⟩)
  let rest : Mix (2 • Lambda, Pi) := ⟨restval, rest_mem⟩
  have hg_ofRank :
      Gene.ofRank (2 * p + 2) .NonPolarized =
        (Finsupp.single g 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g)
    rwa [hgrank, hgNP] at h
  have hX9val : (X9 p).1 = Finsupp.single g 2 := by
    rw [X9_eq, hg_ofRank]
    ext g'
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hXeq : (X9 p).1 + restval = X.1.1 := by
    rw [hX9val, add_comm]
    exact sub_single_two_add_single_two_eq hXg2
  have hY_no_gene : ∀ g' : Gene, g'.rank = 2 * p + 2 → Y.1.1 g' = 0 := by
    intro g' hgr'
    by_contra hne
    have hg'Y : 0 < Y.1.1 g' := Nat.pos_of_ne_zero hne
    have hg'even : Even g'.rank := by rw [hgr']; exact ⟨p + 1, by ring⟩
    have hg'evenPart : 0 < Y.1.1.evenPart g' := by
      rw [evenPart_eq, Finsupp.filter_apply, if_pos hg'even]
      exact hg'Y
    have hg'NP :=
      Mix2LambdaSection17.type_eq_nonpolarized_of_mem_twoLambda Y.1.2.1 hg'evenPart
    have hg'eq : g' = g :=
      Gene.ext (hgr'.trans hgrank.symm) (hg'NP.trans hgNP.symm)
    have hgY : 0 < Y.1.1 g := by rwa [← hg'eq]
    have hle := hcommon g (by omega)
    omega
  have hYr_pred : Chromosome.prime^[2 * p + 1] Y.1.1 ≠ 0 := by
    intro hzero
    have hdom := (le_iff_dominates.mp hXY.le (2 * p + 1)).1
    have hone :=
      (Mix2LambdaSection17.one_le_signature_of_double_nonpolarized hgNP hXg2).1
    rw [hgrank, show 2 * p + 2 - 1 = 2 * p + 1 by omega] at hone
    rw [hzero, map_zero] at hdom
    simp only [Prod.fst_zero] at hdom
    linarith
  have hYr : Chromosome.prime^[2 * p + 2] Y.1.1 ≠ 0 :=
    Mix2LambdaSection17.prime_iterate_ne_zero_of_no_gene (by omega)
      hY_no_gene (by simpa only [show 2 * p + 2 - 1 = 2 * p + 1 by omega]
        using hYr_pred)
  have hrank_lt := h17_1 (2 * p + 2) (by omega) hYr
  have hle_r := le_iff_dominates.mp hXY.le (2 * p + 2)
  change Sigma.sigma X.1.1 (2 * p + 2) ≤ Sigma.sigma Y.1.1 (2 * p + 2) at hle_r
  have hsig_ne :
      Sigma.sigma X.1.1 (2 * p + 2) ≠ Sigma.sigma Y.1.1 (2 * p + 2) := by
    intro heq
    have := congr_arg (fun q : ℚ × ℚ => q.1 + q.2) heq
    simp only [Sigma.sigma, signature_sum_eq_rank] at this
    exact (ne_of_lt hrank_lt) (by exact_mod_cast this)
  have hmemX := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 (2 * p + 2)
  have hmemY := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 (2 * p + 2)
  have heven : Even (2 * p + 2) := ⟨p + 1, by ring⟩
  rw [if_pos heven] at hmemX hmemY
  rcases lt_or_eq_of_le hle_r.1 with hfst | hfst
  · have hboost :=
      Mix2LambdaSection17.add_one_le_fst_of_lt_Mix_2Lambda_Pi hmemX hmemY hfst
    change (Sigma.sigma X.1.1 (2 * p + 2)).1 + 1 ≤
      (Sigma.sigma Y.1.1 (2 * p + 2)).1 at hboost
    refine ⟨⟨(Y9 (ε := .Negative) (by decide) p).1 + restval,
        add_mem (Y9 (ε := .Negative) (by decide) p).2 rest_mem⟩, ?_, ?_⟩
    · exact (Subtype.ext hXeq :
        (X9 p : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
          Step.mk (X9 p) (Y9 (ε := .Negative) (by decide) p) rest
            (Primitive.type9 .Negative (by decide) p)
    · change (Y9 (ε := .Negative) (by decide) p).1 + restval ≤ Y.1.1
      rw [le_iff_dominates]
      intro j
      rw [iterate_map_add, map_add]
      have hdecomp :
          signature (Chromosome.prime^[j] X.1.1) =
            signature (Chromosome.prime^[j] (X9 p).1) +
              signature (Chromosome.prime^[j] restval) := by
        conv_lhs => rw [← hXeq]
        rw [iterate_map_add, map_add]
      by_cases hj : j < 2 * p + 2
      · rw [type9_signature_eq_before (by decide) hj, ← hdecomp]
        exact le_iff_dominates.mp hXY.le j
      · by_cases hj' : 2 * p + 3 ≤ j
        · rw [type9_signature_eq_after (by decide) hj', ← hdecomp]
          exact le_iff_dominates.mp hXY.le j
        · have hjeq : j = 2 * p + 2 := by omega
          subst hjeq
          rw [type9_signature_mid (p := p) (ε := .Negative) (by decide),
            GeneType.neg_negative, signature_ofRank_one_positive]
          have heq :
              (signature (Chromosome.prime^[2 * p + 2] (X9 p).1) + (1, 0)) +
                  signature (Chromosome.prime^[2 * p + 2] restval) =
                (1, 0) + Sigma.sigma X.1.1 (2 * p + 2) := by
            change _ = (1, 0) +
              signature (Chromosome.prime^[2 * p + 2] X.1.1)
            rw [hdecomp]
            abel
          rw [heq]
          rw [Prod.le_def]
          simp only [Prod.fst_add, Prod.snd_add, zero_add]
          change
            (1 + (Sigma.sigma X.1.1 (2 * p + 2)).1 ≤
                (Sigma.sigma Y.1.1 (2 * p + 2)).1) ∧
              (Sigma.sigma X.1.1 (2 * p + 2)).2 ≤
                (Sigma.sigma Y.1.1 (2 * p + 2)).2
          exact ⟨by simpa [add_comm] using hboost, hle_r.2⟩
  · have hsnd : (Sigma.sigma X.1.1 (2 * p + 2)).2 <
        (Sigma.sigma Y.1.1 (2 * p + 2)).2 := by
      rcases lt_or_eq_of_le hle_r.2 with h | h
      · exact h
      · exact (hsig_ne (Prod.ext hfst h)).elim
    have hboost :=
      Mix2LambdaSection17.add_one_le_snd_of_lt_Mix_2Lambda_Pi hmemX hmemY hsnd
    change (Sigma.sigma X.1.1 (2 * p + 2)).2 + 1 ≤
      (Sigma.sigma Y.1.1 (2 * p + 2)).2 at hboost
    refine ⟨⟨(Y9 (ε := .Positive) (by decide) p).1 + restval,
        add_mem (Y9 (ε := .Positive) (by decide) p).2 rest_mem⟩, ?_, ?_⟩
    · exact (Subtype.ext hXeq :
        (X9 p : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
          Step.mk (X9 p) (Y9 (ε := .Positive) (by decide) p) rest
            (Primitive.type9 .Positive (by decide) p)
    · change (Y9 (ε := .Positive) (by decide) p).1 + restval ≤ Y.1.1
      rw [le_iff_dominates]
      intro j
      rw [iterate_map_add, map_add]
      have hdecomp :
          signature (Chromosome.prime^[j] X.1.1) =
            signature (Chromosome.prime^[j] (X9 p).1) +
              signature (Chromosome.prime^[j] restval) := by
        conv_lhs => rw [← hXeq]
        rw [iterate_map_add, map_add]
      by_cases hj : j < 2 * p + 2
      · rw [type9_signature_eq_before (by decide) hj, ← hdecomp]
        exact le_iff_dominates.mp hXY.le j
      · by_cases hj' : 2 * p + 3 ≤ j
        · rw [type9_signature_eq_after (by decide) hj', ← hdecomp]
          exact le_iff_dominates.mp hXY.le j
        · have hjeq : j = 2 * p + 2 := by omega
          subst hjeq
          rw [type9_signature_mid (p := p) (ε := .Positive) (by decide),
            GeneType.neg_positive, signature_ofRank_one_negative]
          have heq :
              (signature (Chromosome.prime^[2 * p + 2] (X9 p).1) + (0, 1)) +
                  signature (Chromosome.prime^[2 * p + 2] restval) =
                (0, 1) + Sigma.sigma X.1.1 (2 * p + 2) := by
            change _ = (0, 1) +
              signature (Chromosome.prime^[2 * p + 2] X.1.1)
            rw [hdecomp]
            abel
          rw [heq]
          rw [Prod.le_def]
          simp only [Prod.fst_add, Prod.snd_add, zero_add]
          change
            (Sigma.sigma X.1.1 (2 * p + 2)).1 ≤
                (Sigma.sigma Y.1.1 (2 * p + 2)).1 ∧
              1 + (Sigma.sigma X.1.1 (2 * p + 2)).2 ≤
                (Sigma.sigma Y.1.1 (2 * p + 2)).2
          exact ⟨hle_r.1, by simpa [add_comm] using hboost⟩

lemma exists_mutation_le_of_nonpolarized
    {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g : Gene) (hXg : 0 < X.1.1 g)
    (hgNP : g.type = .NonPolarized) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have heven : Even g.rank := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hgodd : 0 < X.1.1.oddPart g := by
      rw [oddPart_eq, Finsupp.filter_apply, if_pos hodd]
      exact hXg
    have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2.2) g
      (Finsupp.mem_support_iff.mpr hgodd.ne')
    exact hpol hgNP
  obtain ⟨q, hq⟩ := heven
  have hqpos : 0 < q := by
    have hrpos := g.rank_pos
    rw [hq] at hrpos
    omega
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqpos)
  have hgrank : g.rank = 2 * p + 2 := by omega
  have hgeven : 0 < X.1.1.evenPart g := by
    rw [evenPart_eq, Finsupp.filter_apply, if_pos (show Even g.rank by
      rw [hgrank]; exact ⟨p + 1, by ring⟩)]
    exact hXg
  have hXg2 :=
    Mix2LambdaSection17.two_le_coeff_of_mem_twoLambda X.1.2.1 hgeven
  rw [evenPart_eq, Finsupp.filter_apply,
    if_pos (show Even g.rank by rw [hgrank]; exact ⟨p + 1, by ring⟩)] at hXg2
  exact exists_mutation_le_type9 X Y hXY hcommon h17_1 p g hgNP hgrank hXg2

end Mix2LambdaPi
