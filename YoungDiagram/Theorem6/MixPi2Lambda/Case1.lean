import YoungDiagram.Theorem6.MixPi2Lambda.Prelim

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! ## Rank-zero and rank-one cases -/

/-- Rank-0 elements of `Mix (Pi, 2 • Lambda)` are all zero, so `X < Y` is absurd. -/
lemma exists_mutation_le_rank_zero {X Y : nMixPi2Lambda 0} (hXY : X < Y) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_zero X.2).trans (rank_zero Y.2).symm) (ne_of_lt hXY)

/-- There are no rank-1 elements of `Mix (Pi, 2 • Lambda)`. -/
lemma exists_mutation_le_rank_one {X Y : nMixPi2Lambda 1} (_hXY : X < Y) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  exfalso
  obtain ⟨ε, hε⟩ := rank_one X.2
  have hodd : X.1.1.oddPart = X.1.1 := by rw [hε, oddPart_ofRank]; simp
  have hX2L : X.1.1 ∈ 2 • Lambda := by
    rw [← hodd]
    exact (mem_Mix_iff.mp X.1.2).2
  obtain ⟨Y0, _, hY02⟩ := hX2L
  change 2 • Y0 = X.1.1 at hY02
  set g : Gene := ⟨1, ε, Nat.one_pos⟩
  have hone : X.1.1 g = 1 := by
    rw [hε, Gene.ofRank_eq_gene' Nat.one_ne_zero]
    exact Finsupp.single_eq_same
  have htwo : X.1.1 g = 2 * Y0 g := by
    rw [← hY02]; rfl
  rw [hone] at htwo
  omega

/-! ## Case 1: X and Y share a gene -/

/-- Arithmetic: `single g 2 = 2 • single g 1`, viewed as chromosome. -/
lemma single_two_eq_two_smul (g : Gene) :
    (Finsupp.single g 2 : Chromosome) = 2 • (Finsupp.single g 1 : Chromosome) := by
  ext g'
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> rfl

/-- A single gene of even rank with polarized type is in `Mix (Pi, 2 • Lambda)`. -/
private lemma single_even_one_mem_Mix_Pi_2Lambda {g : Gene} (hev : Even g.rank)
    (hpol : g.type ≠ .NonPolarized) :
    (Finsupp.single g 1 : Chromosome) ∈ Mix (Pi, 2 • Lambda) := by
  refine ⟨?_, ?_⟩
  · -- evenPart of single g 1 is single g 1, in Π
    have h : evenPart (Finsupp.single g 1 : Chromosome) = Finsupp.single g 1 := by
      rw [evenPart_single, if_pos hev]
    rw [h, mem_Pi_iff, IsPolarized_single Nat.one_ne_zero]
    exact hpol
  · -- oddPart of single g 1 is 0, trivially in 2 • Λ
    have h : oddPart (Finsupp.single g 1 : Chromosome) = 0 := by
      rw [oddPart_single, if_pos hev]
    rw [h]
    exact zero_mem _

/-- A double-coefficient single gene of odd rank with NonPolarized type is in
`Mix (Pi, 2 • Lambda)`. -/
private lemma single_odd_two_mem_Mix_Pi_2Lambda {g : Gene} (hodd : Odd g.rank)
    (hNP : g.type = .NonPolarized) :
    (Finsupp.single g 2 : Chromosome) ∈ Mix (Pi, 2 • Lambda) := by
  refine ⟨?_, ?_⟩
  · -- evenPart of single g 2 = 0 (since rank is odd)
    have h : evenPart (Finsupp.single g 2 : Chromosome) = 0 := by
      rw [single_two_eq_two_smul, map_nsmul, evenPart_single,
        if_neg (Nat.not_even_iff_odd.mpr hodd), smul_zero]
    rw [h]; exact zero_mem _
  · -- oddPart of single g 2 = single g 2 = 2 • single g 1; need ∈ 2 • Λ
    have h : oddPart (Finsupp.single g 2 : Chromosome) = Finsupp.single g 2 := by
      rw [single_two_eq_two_smul, map_nsmul, oddPart_single,
        if_neg (Nat.not_even_iff_odd.mpr hodd), ← single_two_eq_two_smul]
    rw [h, single_two_eq_two_smul]
    rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
    refine ⟨Finsupp.single g 1, ?_, rfl⟩
    rw [mem_Lambda_iff, IsNonPolarized_single Nat.one_ne_zero]; exact hNP

/-- For `X ∈ Mix (Pi, 2 • Lambda)` with `0 < X g` and `g.rank` odd, the gene `g`
is `NonPolarized` and `X g ≥ 2` (since `X.oddPart = 2 • Y0` for some `Y0`). -/
private lemma odd_rank_gene_data {X : Chromosome} (hX : X ∈ Mix (Pi, 2 • Lambda))
    {g : Gene} (hgX : 0 < X g) (hodd : Odd g.rank) :
    g.type = .NonPolarized ∧ 2 ≤ X g := by
  -- oddPart X ∈ 2 • Λ, so write X.oddPart = 2 • Y0.
  have hodd_mem : X.oddPart ∈ 2 • Lambda := hX.2
  obtain ⟨Y0, hY0_mem, hY0_eq⟩ :=
    (AddSubmonoid.mem_smul_pointwise_iff_exists X.oddPart 2 Lambda).mp hodd_mem
  -- 0 < X.oddPart g, since g.rank is odd.
  have hgod : 0 < X.oddPart g := by
    rw [oddPart_eq, Finsupp.filter_apply, if_pos hodd]; exact hgX
  -- 2 • Y0 = X.oddPart, so X.oddPart g = 2 * Y0 g.
  have hodd_apply : X.oddPart g = 2 * Y0 g := by
    rw [← hY0_eq]
    show (2 • Y0) g = 2 * Y0 g
    rw [Finsupp.smul_apply, smul_eq_mul]
  -- g.type = .NonPolarized (from Y0 ∈ Λ)
  have hY0g_pos : 0 < Y0 g := by
    rw [hodd_apply] at hgod; omega
  have hNP : g.type = .NonPolarized :=
    IsNonPolarized_def'.mp (mem_Lambda_iff.mp hY0_mem) g
      (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hY0g_pos))
  refine ⟨hNP, ?_⟩
  -- X g = X.oddPart g = 2 * Y0 g ≥ 2.
  have hXeq : X g = 2 * Y0 g := by
    have h1 : X g = X.oddPart g := by
      rw [oddPart_eq, Finsupp.filter_apply, if_pos hodd]
    rw [h1, hodd_apply]
  rw [hXeq]; omega

/-- For `X ∈ Mix (Pi, 2 • Lambda)` with `0 < X g` and `g.rank` even, the gene `g`
has polarized type. -/
private lemma even_rank_gene_polarized {X : Chromosome} (hX : X ∈ Mix (Pi, 2 • Lambda))
    {g : Gene} (hgX : 0 < X g) (hev : Even g.rank) :
    g.type ≠ .NonPolarized := by
  -- 0 < X.evenPart g since g.rank is even.
  have hgev : 0 < X.evenPart g := by
    rw [evenPart_eq, Finsupp.filter_apply, if_pos hev]; exact hgX
  exact IsPolarized_def'.mp (mem_Pi_iff.mp hX.1) g
    (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgev))

/-- For even-rank shared gene case: subtracting `single g 1` keeps us in
`Mix (Pi, 2 • Lambda)`. -/
lemma sub_single_one_mem_Mix_Pi_2Lambda {X : Chromosome}
    (hX : X ∈ Mix (Pi, 2 • Lambda)) {g : Gene} (hev : Even g.rank) :
    X - (Finsupp.single g 1 : Chromosome) ∈ Mix (Pi, 2 • Lambda) := by
  refine ⟨?_, ?_⟩
  · -- evenPart drops by single g 1; closed under sub by IsPolarized_sub.
    rw [evenPart_sub]
    exact IsPolarized_sub _ hX.1
  · -- oddPart unchanged since single g 1 has odd part 0 (rank even).
    have h : oddPart (X - Finsupp.single g 1) = X.oddPart := by
      rw [oddPart_sub, oddPart_single, if_pos hev, tsub_zero]
    rw [h]; exact hX.2

/-- For odd-rank shared gene case: subtracting `single g 2` keeps us in
`Mix (Pi, 2 • Lambda)`. -/
lemma sub_single_two_mem_Mix_Pi_2Lambda {X : Chromosome}
    (hX : X ∈ Mix (Pi, 2 • Lambda)) {g : Gene} (hodd : Odd g.rank) :
    X - (Finsupp.single g 2 : Chromosome) ∈ Mix (Pi, 2 • Lambda) := by
  refine ⟨?_, ?_⟩
  · -- evenPart: X.evenPart unchanged (single g 2 has even part 0)
    have h : evenPart (X - Finsupp.single g 2) = X.evenPart := by
      rw [evenPart_sub, single_two_eq_two_smul, map_nsmul, evenPart_single,
        if_neg (Nat.not_even_iff_odd.mpr hodd), smul_zero, tsub_zero]
    rw [h]; exact hX.1
  · -- oddPart: X.oddPart - single g 2 ∈ 2 • Λ
    have h : oddPart (X - Finsupp.single g 2) = X.oddPart - Finsupp.single g 2 := by
      rw [oddPart_sub]
      congr 1
      rw [single_two_eq_two_smul, map_nsmul, oddPart_single,
        if_neg (Nat.not_even_iff_odd.mpr hodd), ← single_two_eq_two_smul]
    rw [h]
    -- X.oddPart ∈ 2 • Λ; write X.oddPart = 2 • Y0.
    obtain ⟨Y0, hY0_mem, hY0_eq⟩ :=
      (AddSubmonoid.mem_smul_pointwise_iff_exists X.oddPart 2 Lambda).mp hX.2
    rw [AddSubmonoid.mem_smul_pointwise_iff_exists]
    refine ⟨Y0 - Finsupp.single g 1, ?_, ?_⟩
    · rw [mem_Lambda_iff]
      exact IsFiltered_sub _ (mem_Lambda_iff.mp hY0_mem)
    · -- Need: 2 • (Y0 - single g 1) = X.oddPart - single g 2
      rw [← hY0_eq, single_two_eq_two_smul]
      ext g'
      simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega

/-- When `2 ≤ X g`, we have `X = (X - single g 2) + single g 2`. -/
lemma sub_single_two_add_single_two_eq {X : Chromosome} {g : Gene}
    (hg : 2 ≤ X g) :
    (X - Finsupp.single g 2) + Finsupp.single g 2 = X := by
  ext g'
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h; omega
  · omega

/-- Rank arithmetic: `(X - single g 2).rank = X.rank - 2 * g.rank` when `2 ≤ X g`. -/
private lemma rank_sub_single_two {X : Chromosome} {g : Gene} (hg : 2 ≤ X g) :
    (X - Finsupp.single g 2).rank = X.rank - 2 * g.rank := by
  have hX_eq : X = (X - Finsupp.single g 2) + Finsupp.single g 2 :=
    (sub_single_two_add_single_two_eq hg).symm
  have hrank_X : X.rank =
      (X - Finsupp.single g 2).rank + Chromosome.rank (Finsupp.single g 2) := by
    conv_lhs => rw [hX_eq]
    exact map_add Chromosome.rank _ _
  have hrank_single : Chromosome.rank (Finsupp.single g 2) = 2 * g.rank := by
    rw [rank_single]; ring
  omega

/-- Strict inequality preserved when removing `single g 2`. -/
private lemma sub_single_two_lt_sub_single_two {X Y : Chromosome} {g : Gene}
    (hgX : 2 ≤ X g) (hgY : 2 ≤ Y g) (hXY : X < Y) :
    X - Finsupp.single g 2 < Y - Finsupp.single g 2 := by
  have hX_eq := sub_single_two_add_single_two_eq hgX
  have hY_eq := sub_single_two_add_single_two_eq hgY
  refine ⟨fun k ↦ ?_, fun hge ↦ lt_irrefl X (lt_of_lt_of_le hXY (fun k ↦ ?_))⟩
  · have h : (prime^[k] X).signature ≤ (prime^[k] Y).signature :=
      (le_iff_dominates.mp hXY.le) k
    nth_rw 1 [← hX_eq, ← hY_eq] at h
    simpa only [iterate_map_add, map_add, add_le_add_iff_right] using h
  · nth_rw 1 [← hY_eq, ← hX_eq]
    simpa only [iterate_map_add, map_add, add_le_add_iff_right] using hge k

/-- Remove a shared gene from both X and Y, apply IH, then reattach.
The proof splits on whether `g.rank` is even (remove `single g 1`) or odd
(remove `single g 2`). For even `g.rank`, the gene lives in the evenPart (Π),
so subtraction is straightforward. For odd `g.rank`, the gene lives in the
oddPart (2 • Λ), so `g.type = .NonPolarized` and `X g ≥ 2`; we remove two
copies, preserving the `2 • Λ` constraint. -/
lemma exists_mutation_le_shared_gene (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nMixPi2Lambda k, X.1 < Y.1 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨g, hgX, hgY⟩ := hcommon
  by_cases hev : Even g.rank
  · -- EVEN case: remove single g 1.
    have hpol : g.type ≠ .NonPolarized :=
      even_rank_gene_polarized X.1.2 hgX hev
    have hsg_mem : (Finsupp.single g 1 : Chromosome) ∈ Mix (Pi, 2 • Lambda) :=
      single_even_one_mem_Mix_Pi_2Lambda hev hpol
    let X'v : Chromosome := X.1.1 - Finsupp.single g 1
    let Y'v : Chromosome := Y.1.1 - Finsupp.single g 1
    have hX'mem : X'v ∈ Mix (Pi, 2 • Lambda) :=
      sub_single_one_mem_Mix_Pi_2Lambda X.1.2 hev
    have hY'mem : Y'v ∈ Mix (Pi, 2 • Lambda) :=
      sub_single_one_mem_Mix_Pi_2Lambda Y.1.2 hev
    have hlt_chrom : X'v < Y'v := sub_single_lt_sub_single hgX hgY hXY
    have hlt' : (⟨X'v, hX'mem⟩ : Mix (Pi, 2 • Lambda)) < ⟨Y'v, hY'mem⟩ := hlt_chrom
    have hX'rank : X'v.rank = m + 2 - g.rank := by
      rw [rank_sub_single hgX]; exact congrArg (· - g.rank) X.2
    have hY'rank : Y'v.rank = m + 2 - g.rank := by
      rw [rank_sub_single hgY]; exact congrArg (· - g.rank) Y.2
    obtain ⟨Z', hmut', hle'⟩ :=
      ih (m + 2 - g.rank) (Nat.sub_lt (by omega) g.rank_pos)
        ⟨⟨X'v, hX'mem⟩, hX'rank⟩ ⟨⟨Y'v, hY'mem⟩, hY'rank⟩ hlt'
    refine ⟨⟨Z'.1 + Finsupp.single g 1, add_mem Z'.2 hsg_mem⟩, ?_, ?_⟩
    · have hX_eq : X.1 = ⟨X'v, hX'mem⟩ + ⟨Finsupp.single g 1, hsg_mem⟩ :=
        Subtype.ext (sub_single_add_single_eq hgX).symm
      rw [hX_eq]
      exact MixPi2Lambda.Step.add_right ⟨Finsupp.single g 1, hsg_mem⟩ hmut'
    · change Z'.1 + Finsupp.single g 1 ≤ Y.1.1
      rw [← sub_single_add_single_eq hgY, le_iff_dominates]
      intro k
      have h := (le_iff_dominates.mp hle') k
      simp only [iterate_map_add, map_add, add_le_add_iff_right]
      exact h
  · -- ODD case: remove single g 2.
    rw [Nat.not_even_iff_odd] at hev
    obtain ⟨hNP, hX_ge_2⟩ := odd_rank_gene_data X.1.2 hgX hev
    obtain ⟨_, hY_ge_2⟩ := odd_rank_gene_data Y.1.2 hgY hev
    have hsg_mem : (Finsupp.single g 2 : Chromosome) ∈ Mix (Pi, 2 • Lambda) :=
      single_odd_two_mem_Mix_Pi_2Lambda hev hNP
    let X'v : Chromosome := X.1.1 - Finsupp.single g 2
    let Y'v : Chromosome := Y.1.1 - Finsupp.single g 2
    have hX'mem : X'v ∈ Mix (Pi, 2 • Lambda) :=
      sub_single_two_mem_Mix_Pi_2Lambda X.1.2 hev
    have hY'mem : Y'v ∈ Mix (Pi, 2 • Lambda) :=
      sub_single_two_mem_Mix_Pi_2Lambda Y.1.2 hev
    have hlt_chrom : X'v < Y'v := sub_single_two_lt_sub_single_two hX_ge_2 hY_ge_2 hXY
    have hlt' : (⟨X'v, hX'mem⟩ : Mix (Pi, 2 • Lambda)) < ⟨Y'v, hY'mem⟩ := hlt_chrom
    have hX'rank : X'v.rank = m + 2 - 2 * g.rank := by
      rw [rank_sub_single_two hX_ge_2]; exact congrArg (· - 2 * g.rank) X.2
    have hY'rank : Y'v.rank = m + 2 - 2 * g.rank := by
      rw [rank_sub_single_two hY_ge_2]; exact congrArg (· - 2 * g.rank) Y.2
    have hr_pos : 0 < 2 * g.rank := by
      have := g.rank_pos; omega
    obtain ⟨Z', hmut', hle'⟩ :=
      ih (m + 2 - 2 * g.rank) (Nat.sub_lt (by omega) hr_pos)
        ⟨⟨X'v, hX'mem⟩, hX'rank⟩ ⟨⟨Y'v, hY'mem⟩, hY'rank⟩ hlt'
    refine ⟨⟨Z'.1 + Finsupp.single g 2, add_mem Z'.2 hsg_mem⟩, ?_, ?_⟩
    · have hX_eq : X.1 = ⟨X'v, hX'mem⟩ + ⟨Finsupp.single g 2, hsg_mem⟩ :=
        Subtype.ext (sub_single_two_add_single_two_eq hX_ge_2).symm
      rw [hX_eq]
      exact MixPi2Lambda.Step.add_right ⟨Finsupp.single g 2, hsg_mem⟩ hmut'
    · change Z'.1 + Finsupp.single g 2 ≤ Y.1.1
      rw [← sub_single_two_add_single_two_eq hY_ge_2, le_iff_dominates]
      intro k
      have h := (le_iff_dominates.mp hle') k
      simp only [iterate_map_add, map_add, add_le_add_iff_right]
      exact h

end MixPi2Lambda
