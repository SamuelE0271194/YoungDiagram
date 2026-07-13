import YoungDiagram.Theorem6.Mix2LambdaPi.Prelim
import YoungDiagram.Theorem6.MixPi2Lambda.Prelim
import YoungDiagram.Theorem6.MixLambdaPi.Drops

/-! Shared §17 signature facts for Labels 3 and 4. -/

open Variety hiding prime prime_def
open Chromosome Pointwise

namespace Mix2LambdaSection17

private lemma cond_15_6_add_Pi_Lambda
    {P N : Chromosome} (hP : P ∈ Pi) (hN : N ∈ Lambda) (k : ℕ) :
    if Even k then
      (Sigma.sigma (P + N) (k + 1)).2 - (Sigma.sigma (P + N) (k + 2)).2 ≤
        (Sigma.sigma (P + N) k).1 - (Sigma.sigma (P + N) (k + 1)).1
    else
      (Sigma.sigma (P + N) (k + 1)).1 - (Sigma.sigma (P + N) (k + 2)).1 ≤
        (Sigma.sigma (P + N) k).2 - (Sigma.sigma (P + N) (k + 1)).2 := by
  have hPcond := Sigma.cond_15_6 P k hP
  simp only [Sigma.sigma_linearity, Prod.fst_add, Prod.snd_add]
  split_ifs with heven
  · rw [if_pos heven] at hPcond
    have hNcond := MixLambdaPi.lambda_drop_ineq hN k
    calc
      _ = ((Sigma.sigma P (k + 1)).2 - (Sigma.sigma P (k + 2)).2) +
          ((Sigma.sigma N (k + 1)).2 - (Sigma.sigma N (k + 2)).2) := by ring
      _ ≤ ((Sigma.sigma P k).1 - (Sigma.sigma P (k + 1)).1) +
          ((Sigma.sigma N k).1 - (Sigma.sigma N (k + 1)).1) :=
        add_le_add hPcond hNcond
      _ = _ := by ring
  · rw [if_neg heven] at hPcond
    have hNcond := MixLambdaPi.lambda_drop_ineq' hN k
    calc
      _ = ((Sigma.sigma P (k + 1)).1 - (Sigma.sigma P (k + 2)).1) +
          ((Sigma.sigma N (k + 1)).1 - (Sigma.sigma N (k + 2)).1) := by ring
      _ ≤ ((Sigma.sigma P k).2 - (Sigma.sigma P (k + 1)).2) +
          ((Sigma.sigma N k).2 - (Sigma.sigma N (k + 1)).2) :=
        add_le_add hPcond hNcond
      _ = _ := by ring

private lemma cond_15_7_add_Pi_Lambda
    {P N : Chromosome} (hP : P ∈ Pi) (hN : N ∈ Lambda) (k : ℕ) :
    if Even k then
      (Sigma.sigma (P + N) (k + 1)).1 - (Sigma.sigma (P + N) (k + 2)).1 ≤
        (Sigma.sigma (P + N) k).2 - (Sigma.sigma (P + N) (k + 1)).2
    else
      (Sigma.sigma (P + N) (k + 1)).2 - (Sigma.sigma (P + N) (k + 2)).2 ≤
        (Sigma.sigma (P + N) k).1 - (Sigma.sigma (P + N) (k + 1)).1 := by
  have hPcond := Sigma.cond_15_7 P k hP
  simp only [Sigma.sigma_linearity, Prod.fst_add, Prod.snd_add]
  split_ifs with heven
  · rw [if_pos heven] at hPcond
    have hNcond := MixLambdaPi.lambda_drop_ineq' hN k
    calc
      _ = ((Sigma.sigma P (k + 1)).1 - (Sigma.sigma P (k + 2)).1) +
          ((Sigma.sigma N (k + 1)).1 - (Sigma.sigma N (k + 2)).1) := by ring
      _ ≤ ((Sigma.sigma P k).2 - (Sigma.sigma P (k + 1)).2) +
          ((Sigma.sigma N k).2 - (Sigma.sigma N (k + 1)).2) :=
        add_le_add hPcond hNcond
      _ = _ := by ring
  · rw [if_neg heven] at hPcond
    have hNcond := MixLambdaPi.lambda_drop_ineq hN k
    calc
      _ = ((Sigma.sigma P (k + 1)).2 - (Sigma.sigma P (k + 2)).2) +
          ((Sigma.sigma N (k + 1)).2 - (Sigma.sigma N (k + 2)).2) := by ring
      _ ≤ ((Sigma.sigma P k).1 - (Sigma.sigma P (k + 1)).1) +
          ((Sigma.sigma N k).1 - (Sigma.sigma N (k + 1)).1) :=
        add_le_add hPcond hNcond
      _ = _ := by ring

/-- Condition (15.6) for Label 3. -/
lemma cond_15_6_Mix_2Lambda_Pi
    {X : Chromosome} (hX : X ∈ Mix (2 • Lambda, Pi)) (k : ℕ) :
    if Even k then
      (Sigma.sigma X (k + 1)).2 - (Sigma.sigma X (k + 2)).2 ≤
        (Sigma.sigma X k).1 - (Sigma.sigma X (k + 1)).1
    else
      (Sigma.sigma X (k + 1)).1 - (Sigma.sigma X (k + 2)).1 ≤
        (Sigma.sigma X k).2 - (Sigma.sigma X (k + 1)).2 := by
  rw [X.parity_decomposition]
  exact cond_15_6_add_Pi_Lambda hX.2 (smul_Lambda_le_Lambda hX.1) k

/-- Condition (15.7) for Label 3. -/
lemma cond_15_7_Mix_2Lambda_Pi
    {X : Chromosome} (hX : X ∈ Mix (2 • Lambda, Pi)) (k : ℕ) :
    if Even k then
      (Sigma.sigma X (k + 1)).1 - (Sigma.sigma X (k + 2)).1 ≤
        (Sigma.sigma X k).2 - (Sigma.sigma X (k + 1)).2
    else
      (Sigma.sigma X (k + 1)).2 - (Sigma.sigma X (k + 2)).2 ≤
        (Sigma.sigma X k).1 - (Sigma.sigma X (k + 1)).1 := by
  rw [X.parity_decomposition]
  exact cond_15_7_add_Pi_Lambda hX.2 (smul_Lambda_le_Lambda hX.1) k

/-- Condition (15.6) for Label 4. -/
lemma cond_15_6_Mix_Pi_2Lambda
    {X : Chromosome} (hX : X ∈ Mix (Pi, 2 • Lambda)) (k : ℕ) :
    if Even k then
      (Sigma.sigma X (k + 1)).2 - (Sigma.sigma X (k + 2)).2 ≤
        (Sigma.sigma X k).1 - (Sigma.sigma X (k + 1)).1
    else
      (Sigma.sigma X (k + 1)).1 - (Sigma.sigma X (k + 2)).1 ≤
        (Sigma.sigma X k).2 - (Sigma.sigma X (k + 1)).2 := by
  rw [X.parity_decomposition]
  simpa only [add_comm] using
    cond_15_6_add_Pi_Lambda hX.1 (smul_Lambda_le_Lambda hX.2) k

/-- Condition (15.7) for Label 4. -/
lemma cond_15_7_Mix_Pi_2Lambda
    {X : Chromosome} (hX : X ∈ Mix (Pi, 2 • Lambda)) (k : ℕ) :
    if Even k then
      (Sigma.sigma X (k + 1)).1 - (Sigma.sigma X (k + 2)).1 ≤
        (Sigma.sigma X k).2 - (Sigma.sigma X (k + 1)).2
    else
      (Sigma.sigma X (k + 1)).2 - (Sigma.sigma X (k + 2)).2 ≤
        (Sigma.sigma X k).1 - (Sigma.sigma X (k + 1)).1 := by
  rw [X.parity_decomposition]
  simpa only [add_comm] using
    cond_15_7_add_Pi_Lambda hX.1 (smul_Lambda_le_Lambda hX.2) k

/-- Decomposition `2g + (X - 2g) = X` when `X g ≥ 2`. -/
lemma double_single_add_rest {X : Chromosome} {g : Gene} (hXg : 2 ≤ X g) :
    Finsupp.single g 1 + Finsupp.single g 1 +
      (X - Finsupp.single g 1 - Finsupp.single g 1) = X := by
  ext g'
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases h : g = g'
  · subst h
    simp
    omega
  · simp [h]

/-- Decompose two copies each of two distinct genes from a chromosome. -/
lemma double_pair_add_rest {X : Chromosome} {g h : Gene}
    (hXg : 2 ≤ X g) (hXh : 2 ≤ X h) (hne : g ≠ h) :
    Finsupp.single g 1 + Finsupp.single g 1 +
      Finsupp.single h 1 + Finsupp.single h 1 +
      (X - Finsupp.single g 1 - Finsupp.single g 1 -
        Finsupp.single h 1 - Finsupp.single h 1) = X := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hxg : g = x
  · subst hxg
    simp [hne.symm]
    omega
  · by_cases hxh : h = x
    · subst hxh
      simp [hne]
      omega
    · simp [hxg, hxh]

/-- Decompose one copy of two distinct genes from a chromosome. -/
lemma single_pair_add_rest {X : Chromosome} {g h : Gene}
    (hXg : 1 ≤ X g) (hXh : 1 ≤ X h) (hne : g ≠ h) :
    Finsupp.single g 1 + Finsupp.single h 1 +
      (X - Finsupp.single g 1 - Finsupp.single h 1) = X := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hxg : g = x
  · subst hxg
    simp [hne.symm]
    omega
  · by_cases hxh : h = x
    · subst hxh
      simp [hne]
      omega
    · simp [hxg, hxh]

/-- Decompose one copy of three pairwise distinct genes from a chromosome. -/
lemma single_triple_add_rest {X : Chromosome} {g h k : Gene}
    (hXg : 1 ≤ X g) (hXh : 1 ≤ X h) (hXk : 1 ≤ X k)
    (hgh : g ≠ h) (hgk : g ≠ k) (hhk : h ≠ k) :
    Finsupp.single g 1 + Finsupp.single h 1 + Finsupp.single k 1 +
      (X - Finsupp.single g 1 - Finsupp.single h 1 -
        Finsupp.single k 1) = X := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hxg : g = x
  · subst hxg
    simp [hgh.symm, hgk.symm]
    omega
  · by_cases hxh : h = x
    · subst hxh
      simp [hgh, hhk.symm]
      omega
    · by_cases hxk : k = x
      · subst hxk
        simp [hgk, hhk]
        omega
      · simp [hxg, hxh, hxk]

/-- Choose a gene of maximal rank from a nonzero chromosome. -/
lemma exists_max_rank_gene_of_ne_zero {X : Chromosome} (hX : X ≠ 0) :
    ∃ g : Gene, 0 < X g ∧ ∀ h : Gene, 0 < X h → h.rank ≤ g.rank := by
  classical
  have hne : X.support.Nonempty := Finsupp.support_nonempty_iff.mpr hX
  let S : Finset ℕ := X.support.image Gene.rank
  have hSne : S.Nonempty := by
    obtain ⟨g, hg⟩ := hne
    exact ⟨g.rank, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩
  obtain ⟨g, hg_support, hgrank⟩ :=
    Finset.mem_image.mp (Finset.max'_mem S hSne)
  refine ⟨g, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg_support), ?_⟩
  intro h hh
  have hhrank_mem : h.rank ∈ S :=
    Finset.mem_image.mpr ⟨h, Finsupp.mem_support_iff.mpr hh.ne', rfl⟩
  have hle := Finset.le_max' S h.rank hhrank_mem
  rw [hgrank]
  exact hle

/-- Choose a maximal-rank gene from the part of `X` remaining after deleting
one copy of two distinct genes that each occur exactly once. -/
lemma exists_max_rank_gene_of_single_pair_rest_ne_zero
    {X : Chromosome} {g h : Gene}
    (hXg : X g = 1) (hXh : X h = 1) (hne : g ≠ h)
    (hrest : X - Finsupp.single g 1 - Finsupp.single h 1 ≠ 0) :
    ∃ k : Gene,
      0 < ((X - Finsupp.single g 1 - Finsupp.single h 1 : Chromosome) k) ∧
      0 < X k ∧ k ≠ g ∧ k ≠ h ∧
      ∀ l : Gene,
        0 < ((X - Finsupp.single g 1 - Finsupp.single h 1 : Chromosome) l) →
        l.rank ≤ k.rank := by
  obtain ⟨k, hkrest, hkmax⟩ := exists_max_rank_gene_of_ne_zero hrest
  have hkX : 0 < X k := by
    simp only [Finsupp.tsub_apply, Finsupp.single_apply] at hkrest
    split_ifs at hkrest <;> omega
  have hkg : k ≠ g := by
    intro hk
    subst hk
    simp [hXg, hne.symm] at hkrest
  have hkh : k ≠ h := by
    intro hk
    subst hk
    simp [hXh, hne] at hkrest
  exact ⟨k, hkrest, hkX, hkg, hkh, hkmax⟩

/-- If `X ≤ Y` and `Y` has vanished after `k` prime steps, then every gene of
`X` has rank at most `k`. -/
lemma rank_le_of_le_prime_zero {X Y : Chromosome} (hXY : X ≤ Y) {k : ℕ}
    (hYzero : Chromosome.prime^[k] Y = 0)
    {g : Gene} (hgX : 0 < X g) :
    g.rank ≤ k := by
  have hle := le_iff_dominates.mp hXY k
  have hXsig_zero : signature (Chromosome.prime^[k] X) = 0 := by
    rw [hYzero, map_zero] at hle
    exact Prod.ext
      (le_antisymm hle.1 (signature_nonneg (Chromosome.prime^[k] X)).1)
      (le_antisymm hle.2 (signature_nonneg (Chromosome.prime^[k] X)).2)
  have hXzero : Chromosome.prime^[k] X = 0 := signature_eq_zero hXsig_zero
  exact prime_iterate_eq_zero_rank_le.mpr hXzero g
    (Finsupp.mem_support_iff.mpr hgX.ne')

/-- An odd rank below the next even boundary is either rank `1`, or has the
form `2t+3` with `t` still below the preceding positive/negative-pair level. -/
lemma odd_rank_le_even_succ_cases {r q : ℕ}
    (hodd : Odd r) (hle : r ≤ 2 * q + 4) :
    r = 1 ∨ ∃ t : ℕ, t ≤ q ∧ r = 2 * t + 3 := by
  obtain ⟨p, hp⟩ := hodd
  by_cases hp0 : p = 0
  · left
    omega
  · right
    refine ⟨p - 1, ?_, ?_⟩ <;> omega

/-- Decompose a `2+1` pair of distinct genes from a chromosome. -/
lemma double_single_pair_add_rest {X : Chromosome} {g h : Gene}
    (hXg : 2 ≤ X g) (hXh : 1 ≤ X h) (hne : g ≠ h) :
    Finsupp.single g 1 + Finsupp.single g 1 + Finsupp.single h 1 +
      (X - Finsupp.single g 1 - Finsupp.single g 1 -
        Finsupp.single h 1) = X := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hxg : g = x
  · subst hxg
    simp [hne.symm]
    omega
  · by_cases hxh : h = x
    · subst hxh
      simp [hne]
      omega
    · simp [hxg, hxh]

/-- The same `2+1` decomposition with the single copy written first. -/
lemma single_double_pair_add_rest {X : Chromosome} {g h : Gene}
    (hXg : 2 ≤ X g) (hXh : 1 ≤ X h) (hne : g ≠ h) :
    Finsupp.single h 1 + Finsupp.single g 1 + Finsupp.single g 1 +
      (X - Finsupp.single g 1 - Finsupp.single g 1 -
        Finsupp.single h 1) = X := by
  rw [show Finsupp.single h 1 + Finsupp.single g 1 + Finsupp.single g 1 =
      Finsupp.single g 1 + Finsupp.single g 1 + Finsupp.single h 1 by abel]
  exact double_single_pair_add_rest hXg hXh hne

/-- In the absence of a `2+2` opposite-sign pair, the other coefficient in an
equal-rank `2+1` pair is exactly one. -/
lemma opposite_coeff_eq_one_of_no_double
    {X : Chromosome} {gpos gneg : Gene}
    (hnodouble : ¬ ∃ (p n : Gene),
      p.rank = n.rank ∧ p.type = .Positive ∧ n.type = .Negative ∧
      2 ≤ X p ∧ 2 ≤ X n)
    (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hpos : 0 < X gpos) (hneg : 0 < X gneg) :
    (2 ≤ X gpos → X gneg = 1) ∧ (2 ≤ X gneg → X gpos = 1) := by
  constructor
  · intro hpos2
    have hneg_lt : X gneg < 2 := by
      by_contra h
      push Not at h
      exact hnodouble ⟨gpos, gneg, hrank, hgpos, hgneg, hpos2, h⟩
    omega
  · intro hneg2
    have hpos_lt : X gpos < 2 := by
      by_contra h
      push Not at h
      exact hnodouble ⟨gpos, gneg, hrank, hgpos, hgneg, h, hneg2⟩
    omega

/-- Exhaustive multiplicity split for an equal-rank positive/negative pair once
the `2+2` case has been removed. -/
lemma equal_rank_pair_multiplicity_cases
    {X : Chromosome}
    (hnodouble : ¬ ∃ (p n : Gene),
      p.rank = n.rank ∧ p.type = .Positive ∧ n.type = .Negative ∧
      2 ≤ X p ∧ 2 ≤ X n) :
    (∃ (p n : Gene), p.rank = n.rank ∧ p.type = .Positive ∧
      n.type = .Negative ∧ 2 ≤ X p ∧ X n = 1) ∨
    (∃ (p n : Gene), p.rank = n.rank ∧ p.type = .Positive ∧
      n.type = .Negative ∧ X p = 1 ∧ 2 ≤ X n) ∨
    (∃ (p n : Gene), p.rank = n.rank ∧ p.type = .Positive ∧
      n.type = .Negative ∧ X p = 1 ∧ X n = 1) ∨
    ¬ ∃ (p n : Gene), p.rank = n.rank ∧ p.type = .Positive ∧
      n.type = .Negative ∧ 0 < X p ∧ 0 < X n := by
  by_cases hpairs : ∃ (p n : Gene), p.rank = n.rank ∧ p.type = .Positive ∧
      n.type = .Negative ∧ 0 < X p ∧ 0 < X n
  · obtain ⟨p, n, hrank, hp, hn, hXp, hXn⟩ := hpairs
    have hone := opposite_coeff_eq_one_of_no_double
      hnodouble hrank hp hn hXp hXn
    by_cases hp2 : 2 ≤ X p
    · exact Or.inl ⟨p, n, hrank, hp, hn, hp2, hone.1 hp2⟩
    · have hp1 : X p = 1 := by omega
      by_cases hn2 : 2 ≤ X n
      · exact Or.inr <| Or.inl ⟨p, n, hrank, hp, hn, hp1, hn2⟩
      · have hn1 : X n = 1 := by omega
        exact Or.inr <| Or.inr <| Or.inl ⟨p, n, hrank, hp, hn, hp1, hn1⟩
  · exact Or.inr <| Or.inr <| Or.inr hpairs

/-- Choose an equal-rank positive/negative pair of minimal rank.  This is the
Lean version of the phrase "let `m` be minimal with respect to this property"
in §17. -/
lemma exists_min_equal_rank_pair
    {X : Chromosome}
    (hpairs : ∃ (p n : Gene), p.rank = n.rank ∧ p.type = .Positive ∧
      n.type = .Negative ∧ 0 < X p ∧ 0 < X n) :
    ∃ (p n : Gene), p.rank = n.rank ∧ p.type = .Positive ∧
      n.type = .Negative ∧ 0 < X p ∧ 0 < X n ∧
      ∀ (p' n' : Gene), p'.rank = n'.rank → p'.type = .Positive →
        n'.type = .Negative → 0 < X p' → 0 < X n' → p.rank ≤ p'.rank := by
  classical
  let S : Finset Gene := X.support.filter fun p =>
    p.type = .Positive ∧
      ∃ n : Gene, p.rank = n.rank ∧ n.type = .Negative ∧ 0 < X n
  have hSne : S.Nonempty := by
    obtain ⟨p, n, hrank, hp, hn, hXp, hXn⟩ := hpairs
    refine ⟨p, ?_⟩
    simp only [S, Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨hXp.ne', hp, ⟨n, hrank, hn, hXn⟩⟩
  obtain ⟨p, hpS, hpmin⟩ := Finset.exists_min_image S Gene.rank hSne
  simp only [S, Finset.mem_filter, Finsupp.mem_support_iff] at hpS
  obtain ⟨hXp_ne, hp, n, hrank, hn, hXn⟩ := hpS
  refine ⟨p, n, hrank, hp, hn, Nat.pos_of_ne_zero hXp_ne, hXn, ?_⟩
  intro p' n' hrank' hp' hn' hXp' hXn'
  exact hpmin p' (by
    simp only [S, Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨hXp'.ne', hp', ⟨n', hrank', hn', hXn'⟩⟩)

/-- Minimal equal-rank pair, with multiplicities split once the `2+2` case has
already been removed. -/
lemma exists_min_equal_rank_pair_multiplicity_cases
    {X : Chromosome}
    (hnodouble : ¬ ∃ (p n : Gene),
      p.rank = n.rank ∧ p.type = .Positive ∧ n.type = .Negative ∧
      2 ≤ X p ∧ 2 ≤ X n)
    (hpairs : ∃ (p n : Gene), p.rank = n.rank ∧ p.type = .Positive ∧
      n.type = .Negative ∧ 0 < X p ∧ 0 < X n) :
    ∃ (p n : Gene), p.rank = n.rank ∧ p.type = .Positive ∧
      n.type = .Negative ∧ 0 < X p ∧ 0 < X n ∧
      (∀ (p' n' : Gene), p'.rank = n'.rank → p'.type = .Positive →
        n'.type = .Negative → 0 < X p' → 0 < X n' → p.rank ≤ p'.rank) ∧
      ((2 ≤ X p ∧ X n = 1) ∨ (X p = 1 ∧ 2 ≤ X n) ∨
        (X p = 1 ∧ X n = 1)) := by
  obtain ⟨p, n, hrank, hp, hn, hXp, hXn, hmin⟩ :=
    exists_min_equal_rank_pair hpairs
  have hone := opposite_coeff_eq_one_of_no_double
    hnodouble hrank hp hn hXp hXn
  refine ⟨p, n, hrank, hp, hn, hXp, hXn, hmin, ?_⟩
  by_cases hp2 : 2 ≤ X p
  · exact Or.inl ⟨hp2, hone.1 hp2⟩
  · have hp1 : X p = 1 := by omega
    by_cases hn2 : 2 ≤ X n
    · exact Or.inr <| Or.inl ⟨hp1, hn2⟩
    · have hn1 : X n = 1 := by omega
      exact Or.inr <| Or.inr ⟨hp1, hn1⟩

private lemma signature_eq_components_of_even_support {Z : Chromosome}
    (hev : ∀ g ∈ Z.support, Even g.rank) :
    (signature Z).1 = (signature Z).2 := by
  rw [signature_fst, signature_snd]
  apply Finset.sum_congr rfl
  intro g hg
  have hg_sig : g.signature.1 = g.signature.2 := by
    cases ht : g.type with
    | NonPolarized =>
        rw [Gene.signature_of_nonPolarized ht]
    | Positive =>
        rw [Gene.signature_of_positive ht, if_pos (hev g hg)]
    | Negative =>
        rw [Gene.signature_of_negative ht, if_pos (hev g hg)]
  simp [hg_sig]

private lemma signature_eq_components_of_mem_Lambda
    {W : Chromosome} (hW : W ∈ Lambda) :
    (signature W).1 = (signature W).2 := by
  rw [signature_fst, signature_snd]
  apply Finset.sum_congr rfl
  intro g hg
  have hgNP : g.type = .NonPolarized :=
    IsNonPolarized_def'.mp (mem_Lambda_iff.mp hW) g hg
  have hg_sig : g.signature.1 = g.signature.2 := by
    rw [Gene.signature_of_nonPolarized hgNP]
  simp [hg_sig]

private lemma signature_eq_components_of_mem_twoLambda
    {W : Chromosome} (hW : W ∈ 2 • Lambda) :
    (signature W).1 = (signature W).2 := by
  obtain ⟨W0, hW0, hW0eq⟩ :=
    (AddSubmonoid.mem_smul_pointwise_iff_exists W 2 Lambda).mp hW
  change 2 • W0 = W at hW0eq
  rw [← hW0eq, map_nsmul]
  change 2 * (signature W0).1 = 2 * (signature W0).2
  rw [signature_eq_components_of_mem_Lambda hW0]

lemma type_eq_nonpolarized_of_mem_twoLambda
    {W : Chromosome} (hW : W ∈ 2 • Lambda)
    {g : Gene} (hg : 0 < W g) :
    g.type = .NonPolarized := by
  obtain ⟨W0, hW0, hW0eq⟩ :=
    (AddSubmonoid.mem_smul_pointwise_iff_exists W 2 Lambda).mp hW
  change 2 • W0 = W at hW0eq
  have hW0g : 0 < W0 g := by
    rw [← hW0eq, Finsupp.smul_apply, smul_eq_mul] at hg
    omega
  exact IsNonPolarized_def'.mp (mem_Lambda_iff.mp hW0) g
    (Finsupp.mem_support_iff.mpr hW0g.ne')

lemma two_le_coeff_of_mem_twoLambda
    {W : Chromosome} (hW : W ∈ 2 • Lambda)
    {g : Gene} (hg : 0 < W g) :
    2 ≤ W g := by
  obtain ⟨W0, _, hW0eq⟩ :=
    (AddSubmonoid.mem_smul_pointwise_iff_exists W 2 Lambda).mp hW
  change 2 • W0 = W at hW0eq
  rw [← hW0eq, Finsupp.smul_apply, smul_eq_mul] at hg ⊢
  omega

/-- In Label 3, every polarized gene in the support has odd rank: the even
part belongs to `2 • Lambda`. -/
lemma odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
    {X : Chromosome} (hX : X ∈ Mix (2 • Lambda, Pi))
    {g : Gene} (hgX : 0 < X g) (hgpol : g.type ≠ .NonPolarized) :
    Odd g.rank := by
  by_contra hodd
  have heven : Even g.rank := Nat.not_odd_iff_even.mp hodd
  have hg_even : 0 < X.evenPart g := by
    rw [evenPart_eq, Finsupp.filter_apply, if_pos heven]
    exact hgX
  have hNP :=
    type_eq_nonpolarized_of_mem_twoLambda hX.1 hg_even
  exact hgpol hNP

/-- In Label 4, every polarized gene in the support has even rank: the odd
part belongs to `2 • Lambda`. -/
lemma even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
    {X : Chromosome} (hX : X ∈ Mix (Pi, 2 • Lambda))
    {g : Gene} (hgX : 0 < X g) (hgpol : g.type ≠ .NonPolarized) :
    Even g.rank := by
  by_contra heven
  have hodd : Odd g.rank := Nat.not_even_iff_odd.mp heven
  have hg_odd : 0 < X.oddPart g := by
    rw [oddPart_eq, Finsupp.filter_apply, if_pos hodd]
    exact hgX
  have hNP :=
    type_eq_nonpolarized_of_mem_twoLambda hX.2 hg_odd
  exact hgpol hNP

/-- A chromosome in `2 • Lambda` has a diagonal integral signature. -/
lemma signature_twoLambda_isNat
    {W : Chromosome} (hW : W ∈ 2 • Lambda) :
    ∃ n : ℕ, signature W = ((n : ℚ), (n : ℚ)) := by
  obtain ⟨W0, hW0, hW0eq⟩ :=
    (AddSubmonoid.mem_smul_pointwise_iff_exists W 2 Lambda).mp hW
  change 2 • W0 = W at hW0eq
  have heq := signature_eq_components_of_mem_Lambda hW0
  have hsum := signature_sum_eq_rank (X := W0)
  refine ⟨W0.rank, ?_⟩
  rw [← hW0eq, map_nsmul]
  apply Prod.ext
  · change 2 * (signature W0).1 = (W0.rank : ℚ)
    linarith
  · change 2 * (signature W0).2 = (W0.rank : ℚ)
    linarith

/-- Every chromosome in Label 3 has integral signature components. -/
lemma signature_Mix_2Lambda_Pi_isNat
    {Z : Chromosome} (hZ : Z ∈ Mix (2 • Lambda, Pi)) :
    ∃ n : ℕ × ℕ, signature Z = ((n.1 : ℚ), (n.2 : ℚ)) := by
  obtain ⟨e, he⟩ := signature_twoLambda_isNat hZ.1
  obtain ⟨o, ho⟩ := signature_pi_isNat hZ.2
  refine ⟨(e + o.1, e + o.2), ?_⟩
  rw [Z.parity_decomposition, map_add, he, ho]
  norm_num
  constructor <;> ring

/-- Every chromosome in Label 4 has integral signature components. -/
lemma signature_Mix_Pi_2Lambda_isNat
    {Z : Chromosome} (hZ : Z ∈ Mix (Pi, 2 • Lambda)) :
    ∃ n : ℕ × ℕ, signature Z = ((n.1 : ℚ), (n.2 : ℚ)) := by
  obtain ⟨e, he⟩ := signature_pi_isNat hZ.1
  obtain ⟨o, ho⟩ := signature_twoLambda_isNat hZ.2
  refine ⟨(e.1 + o, e.2 + o), ?_⟩
  rw [Z.parity_decomposition, map_add, he, ho]
  norm_num
  constructor <;> ring

lemma add_one_le_fst_of_lt_Mix_2Lambda_Pi
    {X Y : Chromosome}
    (hX : X ∈ Mix (2 • Lambda, Pi)) (hY : Y ∈ Mix (2 • Lambda, Pi))
    (h : (signature X).1 < (signature Y).1) :
    (signature X).1 + 1 ≤ (signature Y).1 := by
  obtain ⟨x, hx⟩ := signature_Mix_2Lambda_Pi_isNat hX
  obtain ⟨y, hy⟩ := signature_Mix_2Lambda_Pi_isNat hY
  rw [hx, hy] at h ⊢
  change (x.1 : ℚ) < y.1 at h
  change (x.1 : ℚ) + 1 ≤ y.1
  exact_mod_cast Nat.add_one_le_iff.mpr (by exact_mod_cast h)

lemma add_one_le_snd_of_lt_Mix_2Lambda_Pi
    {X Y : Chromosome}
    (hX : X ∈ Mix (2 • Lambda, Pi)) (hY : Y ∈ Mix (2 • Lambda, Pi))
    (h : (signature X).2 < (signature Y).2) :
    (signature X).2 + 1 ≤ (signature Y).2 := by
  obtain ⟨x, hx⟩ := signature_Mix_2Lambda_Pi_isNat hX
  obtain ⟨y, hy⟩ := signature_Mix_2Lambda_Pi_isNat hY
  rw [hx, hy] at h ⊢
  change (x.2 : ℚ) < y.2 at h
  change (x.2 : ℚ) + 1 ≤ y.2
  exact_mod_cast Nat.add_one_le_iff.mpr (by exact_mod_cast h)

set_option maxHeartbeats 800000 in
-- Expanding the two-copy decomposition through iterated `prime` is elaboration-heavy.
/-- A double nonpolarized gene leaves `(1,1)` one level before it vanishes. -/
lemma one_le_signature_of_double_nonpolarized
    {X : Chromosome} {g : Gene}
    (hNP : g.type = .NonPolarized) (hXg : 2 ≤ X g) :
    1 ≤ (signature (Chromosome.prime^[g.rank - 1] X)).1 ∧
      1 ≤ (signature (Chromosome.prime^[g.rank - 1] X)).2 := by
  have hg_single :
      Gene.ofRank g.rank .NonPolarized = (Finsupp.single g 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g)
    rwa [hNP] at h
  have hXeq :
      Finsupp.single g 1 + Finsupp.single g 1 +
        (X - Finsupp.single g 1 - Finsupp.single g 1) = X :=
    double_single_add_rest hXg
  have hprime :
      Chromosome.prime^[g.rank - 1]
          (Finsupp.single g 1 + Finsupp.single g 1) =
        Gene.ofRank 1 .NonPolarized + Gene.ofRank 1 .NonPolarized := by
    rw [iterate_map_add, ← hg_single, prime_iterate_ofRank,
      Nat.sub_sub_self g.rank_pos]
  have hnonneg :=
    signature_nonneg
      (Chromosome.prime^[g.rank - 1]
        (X - Finsupp.single g 1 - Finsupp.single g 1))
  have hsig :
      signature (Chromosome.prime^[g.rank - 1] X) =
        signature (Gene.ofRank 1 .NonPolarized + Gene.ofRank 1 .NonPolarized) +
          signature (Chromosome.prime^[g.rank - 1]
            (X - Finsupp.single g 1 - Finsupp.single g 1)) := by
    conv_lhs => rw [← hXeq]
    rw [iterate_map_add, map_add, hprime]
  rw [hsig, map_add, signature_ofRank_nonPolarized]
  norm_num
  exact ⟨hnonneg.1, hnonneg.2⟩

/-- If `Y` has no gene of rank `r`, nonzero at level `r-1` forces nonzero at
level `r`. -/
lemma prime_iterate_ne_zero_of_no_gene
    {Y : Chromosome} {r : ℕ} (hr : 1 ≤ r)
    (hY_no_gene : ∀ g : Gene, g.rank = r → Y g = 0)
    (hYr_minus_one : Chromosome.prime^[r - 1] Y ≠ 0) :
    Chromosome.prime^[r] Y ≠ 0 := by
  have hno_low :
      ∀ h : Gene, h.rank = 1 →
        (Chromosome.prime^[r - 1] Y) h = 0 := by
    intro h hhrank
    rw [prime_iterate_coeff]
    apply hY_no_gene
    simp only [hhrank]
    omega
  have hr_eq : r = 1 + (r - 1) := by omega
  rw [hr_eq, Function.iterate_add_apply, Function.iterate_one]
  apply prime_ne_zero_of_rank_ge_two hYr_minus_one
  intro h hh
  rw [Finsupp.mem_support_iff] at hh
  by_contra hlt
  have hhrank : h.rank = 1 := le_antisymm (by omega) h.rank_pos
  exact hh (hno_low h hhrank)

/-- Every chromosome in Label 4 has equal signature components. -/
lemma signature_eq_components_of_mem_Mix_Pi_2Lambda
    {Z : Chromosome} (hZ : Z ∈ Mix (Pi, 2 • Lambda)) :
    (signature Z).1 = (signature Z).2 := by
  have hev : (signature Z.evenPart).1 = (signature Z.evenPart).2 := by
    apply signature_eq_components_of_even_support
    intro g hg
    have hne : Z.evenPart g ≠ 0 := Finsupp.mem_support_iff.mp hg
    by_contra hodd
    rw [evenPart_eq, Finsupp.filter_apply, if_neg hodd] at hne
    exact hne rfl
  have hodd : (signature Z.oddPart).1 = (signature Z.oddPart).2 :=
    signature_eq_components_of_mem_twoLambda hZ.2
  rw [Z.parity_decomposition, map_add, Prod.fst_add, Prod.snd_add, hev, hodd]

/-- A strict dominance gap inside Label 4 is at least `(1,1)`, since both
signature components are equal natural numbers. -/
lemma one_pair_add_le_of_lt_Mix_Pi_2Lambda
    {X Y : Chromosome}
    (hX : X ∈ Mix (Pi, 2 • Lambda)) (hY : Y ∈ Mix (Pi, 2 • Lambda))
    (hle : signature X ≤ signature Y)
    (hne : signature X ≠ signature Y) :
    ((1 : ℚ), (1 : ℚ)) + signature X ≤ signature Y := by
  have hXeq := signature_eq_components_of_mem_Mix_Pi_2Lambda hX
  have hYeq := signature_eq_components_of_mem_Mix_Pi_2Lambda hY
  obtain ⟨x, hx⟩ := signature_Mix_Pi_2Lambda_isNat hX
  obtain ⟨y, hy⟩ := signature_Mix_Pi_2Lambda_isNat hY
  have hfst : (signature X).1 < (signature Y).1 := by
    apply lt_of_le_of_ne hle.1
    intro heq
    apply hne
    exact Prod.ext heq (by rw [← hXeq, ← hYeq, heq])
  rw [hx, hy] at hfst ⊢
  norm_num at hfst ⊢
  change ((1 : ℚ) + x.1 ≤ y.1) ∧ ((1 : ℚ) + x.2 ≤ y.2)
  have hnat : x.1 + 1 ≤ y.1 := by
    apply Nat.add_one_le_iff.mpr
    exact_mod_cast hfst
  have hxeq : x.1 = x.2 := by
    rw [hx] at hXeq
    norm_num at hXeq
    exact_mod_cast hXeq
  have hyeq : y.1 = y.2 := by
    rw [hy] at hYeq
    norm_num at hYeq
    exact_mod_cast hYeq
  have hnat' : (1 : ℚ) + x.1 ≤ y.1 := by
    have hcast : (x.1 : ℚ) + 1 ≤ y.1 := by exact_mod_cast hnat
    simpa [add_comm] using hcast
  exact ⟨hnat', by rw [← hxeq, ← hyeq]; exact hnat'⟩

/-- For Label 3, odd prime levels have equal signature components. -/
lemma signature_prime_iterate_odd_eq_components_L3
    {X : Chromosome} (hX : X ∈ Mix (2 • Lambda, Pi))
    {i : ℕ} (hi : ¬ Even i) :
    (signature (Chromosome.prime^[i] X)).1 =
      (signature (Chromosome.prime^[i] X)).2 := by
  have hmem := Variety.prime_mem_Mix_2Lambda_Pi_iterate hX i
  rw [if_neg hi] at hmem
  exact signature_eq_components_of_mem_Mix_Pi_2Lambda hmem

/-- For Label 4, even prime levels have equal signature components. -/
lemma signature_prime_iterate_even_eq_components_L4
    {X : Chromosome} (hX : X ∈ Mix (Pi, 2 • Lambda))
    {i : ℕ} (hi : Even i) :
    (signature (Chromosome.prime^[i] X)).1 =
      (signature (Chromosome.prime^[i] X)).2 := by
  have hmem := Variety.prime_mem_Mix_Pi_2Lambda_iterate hX i
  rw [if_pos hi] at hmem
  exact signature_eq_components_of_mem_Mix_Pi_2Lambda hmem

/-- Choose a gene of minimal rank in a nonzero chromosome.  This is the Lean
version of "let `m` be the minimum rank of a gene of `X`" in §17. -/
lemma exists_min_rank_gene {X : Chromosome} (hX : X ≠ 0) :
    ∃ g : Gene, 0 < X g ∧ ∀ g' : Gene, 0 < X g' → g.rank ≤ g'.rank := by
  classical
  obtain ⟨g0, hg0⟩ := Finsupp.support_nonempty_iff.mpr hX
  obtain ⟨g, hgS, hgmin⟩ := Finset.exists_min_image X.support Gene.rank ⟨g0, hg0⟩
  refine ⟨g, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hgS), ?_⟩
  intro g' hg'
  exact hgmin g' (Finsupp.mem_support_iff.mpr (ne_of_gt hg'))

/-- Pure-arithmetic window-propagation engine for §17.  Given a seed
`f j0 ≤ c j0` and, at each step of length two inside the window, the drop
comparison `c i - c (i+2) ≤ f i - f (i+2)`, the inequality `f ≤ c` propagates
along the window.  Here `f` plays the role of an `X`-signature component and
`c` the matching `Y`-signature component. -/
lemma le_of_window_step (f c : ℕ → ℚ) (j0 d : ℕ)
    (hseed : f j0 ≤ c j0)
    (hstep : ∀ t, t < d →
      c (j0 + 2 * t) - c (j0 + 2 * t + 2) ≤
        f (j0 + 2 * t) - f (j0 + 2 * t + 2)) :
    ∀ t, t ≤ d → f (j0 + 2 * t) ≤ c (j0 + 2 * t) := by
  intro t
  induction t with
  | zero => intro _; simpa using hseed
  | succ n ih =>
      intro ht
      have hn : n ≤ d := by omega
      have hn' : n < d := by omega
      have ihn := ih hn
      have hs := hstep n hn'
      have he : j0 + 2 * (n + 1) = j0 + 2 * n + 2 := by ring
      rw [he]
      linarith

/-- First-component window propagation: the `a_j ≤ c_j` half of §17's window
argument, instantiating `le_of_window_step` at the first signature component. -/
lemma fst_propagate_window {X Y : Chromosome} (j0 d : ℕ)
    (hseed :
      (signature (Chromosome.prime^[j0] X)).1 ≤
        (signature (Chromosome.prime^[j0] Y)).1)
    (hstep : ∀ t, t < d →
      (signature (Chromosome.prime^[j0 + 2 * t] Y)).1 -
          (signature (Chromosome.prime^[j0 + 2 * t + 2] Y)).1 ≤
        (signature (Chromosome.prime^[j0 + 2 * t] X)).1 -
          (signature (Chromosome.prime^[j0 + 2 * t + 2] X)).1) :
    ∀ t, t ≤ d →
      (signature (Chromosome.prime^[j0 + 2 * t] X)).1 ≤
        (signature (Chromosome.prime^[j0 + 2 * t] Y)).1 :=
  le_of_window_step
    (fun i => (signature (Chromosome.prime^[i] X)).1)
    (fun i => (signature (Chromosome.prime^[i] Y)).1)
    j0 d hseed hstep

/-- Second-component window propagation: the `b_j ≤ d_j` half of §17's window
argument, instantiating `le_of_window_step` at the second signature component. -/
lemma snd_propagate_window {X Y : Chromosome} (j0 d : ℕ)
    (hseed :
      (signature (Chromosome.prime^[j0] X)).2 ≤
        (signature (Chromosome.prime^[j0] Y)).2)
    (hstep : ∀ t, t < d →
      (signature (Chromosome.prime^[j0 + 2 * t] Y)).2 -
          (signature (Chromosome.prime^[j0 + 2 * t + 2] Y)).2 ≤
        (signature (Chromosome.prime^[j0 + 2 * t] X)).2 -
          (signature (Chromosome.prime^[j0 + 2 * t + 2] X)).2) :
    ∀ t, t ≤ d →
      (signature (Chromosome.prime^[j0 + 2 * t] X)).2 ≤
        (signature (Chromosome.prime^[j0 + 2 * t] Y)).2 :=
  le_of_window_step
    (fun i => (signature (Chromosome.prime^[i] X)).2)
    (fun i => (signature (Chromosome.prime^[i] Y)).2)
    j0 d hseed hstep

/-- Strict variant of `le_of_window_step`: a strict seed `f j0 < c j0`
propagates to `f (j0 + 2t) < c (j0 + 2t)` along the window.  Used for the §17
diagonal middle windows, where the type-10/14 mutation slack is `(1,1)` at every
level and hence the dominance goal is strict. -/
lemma lt_of_window_step (f c : ℕ → ℚ) (j0 d : ℕ)
    (hseed : f j0 < c j0)
    (hstep : ∀ t, t < d →
      c (j0 + 2 * t) - c (j0 + 2 * t + 2) ≤
        f (j0 + 2 * t) - f (j0 + 2 * t + 2)) :
    ∀ t, t ≤ d → f (j0 + 2 * t) < c (j0 + 2 * t) := by
  intro t
  induction t with
  | zero => intro _; simpa using hseed
  | succ n ih =>
      intro ht
      have hn : n ≤ d := by omega
      have hn' : n < d := by omega
      have ihn := ih hn
      have hs := hstep n hn'
      have he : j0 + 2 * (n + 1) = j0 + 2 * n + 2 := by ring
      rw [he]
      linarith

/-- First-component strict window propagation. -/
lemma fst_propagate_window_lt {X Y : Chromosome} (j0 d : ℕ)
    (hseed :
      (signature (Chromosome.prime^[j0] X)).1 <
        (signature (Chromosome.prime^[j0] Y)).1)
    (hstep : ∀ t, t < d →
      (signature (Chromosome.prime^[j0 + 2 * t] Y)).1 -
          (signature (Chromosome.prime^[j0 + 2 * t + 2] Y)).1 ≤
        (signature (Chromosome.prime^[j0 + 2 * t] X)).1 -
          (signature (Chromosome.prime^[j0 + 2 * t + 2] X)).1) :
    ∀ t, t ≤ d →
      (signature (Chromosome.prime^[j0 + 2 * t] X)).1 <
        (signature (Chromosome.prime^[j0 + 2 * t] Y)).1 :=
  lt_of_window_step
    (fun i => (signature (Chromosome.prime^[i] X)).1)
    (fun i => (signature (Chromosome.prime^[i] Y)).1)
    j0 d hseed hstep

/-- Second-component strict window propagation. -/
lemma snd_propagate_window_lt {X Y : Chromosome} (j0 d : ℕ)
    (hseed :
      (signature (Chromosome.prime^[j0] X)).2 <
        (signature (Chromosome.prime^[j0] Y)).2)
    (hstep : ∀ t, t < d →
      (signature (Chromosome.prime^[j0 + 2 * t] Y)).2 -
          (signature (Chromosome.prime^[j0 + 2 * t + 2] Y)).2 ≤
        (signature (Chromosome.prime^[j0 + 2 * t] X)).2 -
          (signature (Chromosome.prime^[j0 + 2 * t + 2] X)).2) :
    ∀ t, t ≤ d →
      (signature (Chromosome.prime^[j0 + 2 * t] X)).2 <
        (signature (Chromosome.prime^[j0 + 2 * t] Y)).2 :=
  lt_of_window_step
    (fun i => (signature (Chromosome.prime^[i] X)).2)
    (fun i => (signature (Chromosome.prime^[i] Y)).2)
    j0 d hseed hstep

/-! ### Rank-drop below the minimum rank

Below the minimum rank of `X`, priming preserves every gene (it merely lowers all
ranks by one), so the one-step rank drop `rank (prime^[i] X) - rank (prime^[i+1] X)`
equals the total multiplicity of `X` and is therefore constant.  This is the Lean
form of the §17 identity `r_i - r_{i+1} = r_0 - r_1` for `i` below the minimum
rank of a gene of `X`. -/

/-- General identity: `rank X = rank (prime X) + totalMult X`, where the total
multiplicity is the sum of all coefficients. -/
lemma rank_eq_prime_rank_add_totalMult (X : Chromosome) :
    X.rank = (Chromosome.prime X).rank + X.sum (fun _ n => n) := by
  rw [rank_def, rank_of_prime]
  simp only [Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [smul_eq_mul]
  have h1 : g.rank - 1 + 1 = g.rank := Nat.sub_add_cancel g.rank_pos
  calc X g * g.rank = X g * (g.rank - 1 + 1) := by rw [h1]
    _ = X g * (g.rank - 1) + X g := by ring

/-- Total multiplicity is invariant under priming, as long as the iteration
level stays below every gene's rank (so no gene is annihilated). -/
lemma totalMult_prime_iterate_eq_of_lt_minRank (X : Chromosome) (i : ℕ)
    (h : ∀ g ∈ X.support, i < g.rank) :
    (Chromosome.prime^[i] X).sum (fun _ n => n) = X.sum (fun _ n => n) := by
  simp only [Finsupp.sum]
  refine Finset.sum_bij'
    (fun g _ => (⟨g.rank + i, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
    (fun g' hg' => (⟨g'.rank - i, g'.type, by
      have := h g' hg'; omega⟩ : Gene))
    ?_ ?_ ?_ ?_ ?_
  · intro g hg
    rw [Finsupp.mem_support_iff, prime_iterate_coeff] at hg
    exact Finsupp.mem_support_iff.mpr hg
  · intro g' hg'
    have hlt := h g' hg'
    rw [Finsupp.mem_support_iff, prime_iterate_coeff]
    simp only [Nat.sub_add_cancel (Nat.le_of_lt hlt)]
    exact Finsupp.mem_support_iff.mp hg'
  · intro g _
    exact Gene.ext (show g.rank + i - i = g.rank by omega) rfl
  · intro g' hg'
    have hlt := h g' hg'
    exact Gene.ext (show g'.rank - i + i = g'.rank by omega) rfl
  · intro g _
    rw [prime_iterate_coeff]

/-- One-step rank drop is constant below the minimum rank: it equals the
zero-level drop `rank X - rank (prime X)`.  This is `r_i - r_{i+1} = r_0 - r_1`
of §17. -/
lemma rank_prime_iterate_drop_eq_of_lt_minRank (X : Chromosome) (i : ℕ)
    (h : ∀ g ∈ X.support, i < g.rank) :
    (Chromosome.prime^[i] X).rank - (Chromosome.prime^[i + 1] X).rank =
      X.rank - (Chromosome.prime X).rank := by
  have e0 : X.rank = (Chromosome.prime X).rank + X.sum (fun _ n => n) :=
    rank_eq_prime_rank_add_totalMult X
  have ei : (Chromosome.prime^[i] X).rank =
      (Chromosome.prime^[i + 1] X).rank + X.sum (fun _ n => n) := by
    have key := rank_eq_prime_rank_add_totalMult (Chromosome.prime^[i] X)
    rw [totalMult_prime_iterate_eq_of_lt_minRank X i h] at key
    rwa [show Chromosome.prime (Chromosome.prime^[i] X) =
      Chromosome.prime^[i + 1] X from (Function.iterate_succ_apply' _ _ _).symm] at key
  omega

/-- Priming never increases total multiplicity: every gene of `prime X` comes
from a gene of `X` of one higher rank, injectively. -/
lemma totalMult_prime_le (X : Chromosome) :
    (Chromosome.prime X).sum (fun _ n => n) ≤ X.sum (fun _ n => n) := by
  classical
  rw [Finsupp.sum, Finsupp.sum]
  calc ∑ g ∈ (Chromosome.prime X).support, (Chromosome.prime X) g
      = ∑ g ∈ (Chromosome.prime X).support,
          X ⟨g.rank + 1, g.type, Nat.le_add_right_of_le g.rank_pos⟩ := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        simpa using prime_iterate_coeff 1 X g
    _ = ∑ g' ∈ (Chromosome.prime X).support.image
            (fun g => (⟨g.rank + 1, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene)),
          X g' := by
        refine (Finset.sum_image ?_).symm
        intro a _ b _ hab
        exact Gene.ext (by have := congrArg Gene.rank hab; simpa using this)
          (by have := congrArg Gene.type hab; simpa using this)
    _ ≤ ∑ g' ∈ X.support, X g' := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
        intro g' hg'
        simp only [Finset.mem_image] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        rw [Finsupp.mem_support_iff]
        have hpc : (Chromosome.prime X) g
            = X ⟨g.rank + 1, g.type, Nat.le_add_right_of_le g.rank_pos⟩ := by
          simpa using prime_iterate_coeff 1 X g
        rw [← hpc]
        exact Finsupp.mem_support_iff.mp hg

/-- Total multiplicity is antitone under iterated priming. -/
lemma totalMult_prime_iterate_le (X : Chromosome) (k : ℕ) :
    (Chromosome.prime^[k] X).sum (fun _ n => n) ≤ X.sum (fun _ n => n) := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (totalMult_prime_le _).trans ih

/-- The one-step rank drop equals the total multiplicity at that level. -/
lemma rank_prime_iterate_drop_eq_totalMult (X : Chromosome) (k : ℕ) :
    (Chromosome.prime^[k] X).rank - (Chromosome.prime^[k + 1] X).rank =
      (Chromosome.prime^[k] X).sum (fun _ n => n) := by
  have key := rank_eq_prime_rank_add_totalMult (Chromosome.prime^[k] X)
  rw [show Chromosome.prime (Chromosome.prime^[k] X) =
    Chromosome.prime^[k + 1] X from (Function.iterate_succ_apply' _ _ _).symm] at key
  omega

/-- Rank-drop antitonicity: `r_k - r_{k+1} ≤ r_0 - r_1`.  This is the §17
inequality `r_i - r_{i+1} ≥ s_i - s_{i+1}`'s `Y`-side ingredient (applied to
`Y`, whose drops are bounded by the zeroth drop). -/
lemma rank_prime_iterate_drop_le_zero (X : Chromosome) (k : ℕ) :
    (Chromosome.prime^[k] X).rank - (Chromosome.prime^[k + 1] X).rank ≤
      X.rank - (Chromosome.prime X).rank := by
  rw [rank_prime_iterate_drop_eq_totalMult,
    show X.rank - (Chromosome.prime X).rank = X.sum (fun _ n => n) by
      have := rank_eq_prime_rank_add_totalMult X; omega]
  exact totalMult_prime_iterate_le X k

/-- §17 seed inequality.  At an **odd** level in Label 3 the two signature
components are equal, so a strict rank gap (the form of (17.1)) splits evenly:
both components are strictly dominated.  This is the seed fed to the strict
window propagation in the no-equal-rank-pair case. -/
lemma seed_strict_lt_at_odd
    {X Y : Chromosome} (hX : X ∈ Mix (2 • Lambda, Pi))
    (hY : Y ∈ Mix (2 • Lambda, Pi)) {i : ℕ} (hodd : ¬ Even i)
    (hrank : (Chromosome.prime^[i] X).rank < (Chromosome.prime^[i] Y).rank) :
    (signature (Chromosome.prime^[i] X)).1 <
        (signature (Chromosome.prime^[i] Y)).1 ∧
      (signature (Chromosome.prime^[i] X)).2 <
        (signature (Chromosome.prime^[i] Y)).2 := by
  have hXeq := signature_prime_iterate_odd_eq_components_L3 hX hodd
  have hYeq := signature_prime_iterate_odd_eq_components_L3 hY hodd
  have hXsum : (signature (Chromosome.prime^[i] X)).1 +
      (signature (Chromosome.prime^[i] X)).2 =
      ((Chromosome.prime^[i] X).rank : ℚ) := signature_sum_eq_rank
  have hYsum : (signature (Chromosome.prime^[i] Y)).1 +
      (signature (Chromosome.prime^[i] Y)).2 =
      ((Chromosome.prime^[i] Y).rank : ℚ) := signature_sum_eq_rank
  have hcast : ((Chromosome.prime^[i] X).rank : ℚ) <
      ((Chromosome.prime^[i] Y).rank : ℚ) := by exact_mod_cast hrank
  constructor <;> linarith

/-- Integrality upgrade: in Label 3 both signature components are natural
numbers, so two strict component gaps at a level give a full `(1,1)` gap.  This
feeds the type10/14 middle-window dominance. -/
lemma one_one_le_of_both_lt
    {X Y : Chromosome} (hX : X ∈ Mix (2 • Lambda, Pi))
    (hY : Y ∈ Mix (2 • Lambda, Pi)) {i : ℕ}
    (hfst : (signature (Chromosome.prime^[i] X)).1 <
        (signature (Chromosome.prime^[i] Y)).1)
    (hsnd : (signature (Chromosome.prime^[i] X)).2 <
        (signature (Chromosome.prime^[i] Y)).2) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[i] X) ≤
      signature (Chromosome.prime^[i] Y) := by
  have hXmem := Variety.prime_mem_Mix_2Lambda_Pi_iterate hX i
  have hYmem := Variety.prime_mem_Mix_2Lambda_Pi_iterate hY i
  -- The signature components are integral in both mix varieties; case on parity.
  have key : ∀ (a b : ℚ × ℚ),
      (∃ n : ℕ × ℕ, a = ((n.1 : ℚ), (n.2 : ℚ))) →
      (∃ n : ℕ × ℕ, b = ((n.1 : ℚ), (n.2 : ℚ))) →
      a.1 < b.1 → a.2 < b.2 → ((1 : ℚ), (1 : ℚ)) + a ≤ b := by
    rintro a b ⟨na, hna⟩ ⟨nb, hnb⟩ h1 h2
    subst hna hnb
    simp only at h1 h2
    rw [Prod.le_def]
    refine ⟨?_, ?_⟩
    · change (1 : ℚ) + (na.1 : ℚ) ≤ (nb.1 : ℚ)
      have hn : na.1 + 1 ≤ nb.1 := Nat.add_one_le_iff.mpr (by exact_mod_cast h1)
      have : ((na.1 : ℚ)) + 1 ≤ (nb.1 : ℚ) := by exact_mod_cast hn
      linarith
    · change (1 : ℚ) + (na.2 : ℚ) ≤ (nb.2 : ℚ)
      have hn : na.2 + 1 ≤ nb.2 := Nat.add_one_le_iff.mpr (by exact_mod_cast h2)
      have : ((na.2 : ℚ)) + 1 ≤ (nb.2 : ℚ) := by exact_mod_cast hn
      linarith
  by_cases hev : Even i
  · rw [if_pos hev] at hXmem hYmem
    exact key _ _ (signature_Mix_2Lambda_Pi_isNat hXmem)
      (signature_Mix_2Lambda_Pi_isNat hYmem) hfst hsnd
  · rw [if_neg hev] at hXmem hYmem
    exact key _ _ (signature_Mix_Pi_2Lambda_isNat hXmem)
      (signature_Mix_Pi_2Lambda_isNat hYmem) hfst hsnd

end Mix2LambdaSection17
