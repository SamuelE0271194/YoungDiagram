import YoungDiagram.Theorem6.Mix2LambdaPi.Type16
import YoungDiagram.Theorem6.Mix2LambdaPrelim
import YoungDiagram.Sigma.Diff

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

lemma snd_pred_strict_of_snd_succ_strict
    {b₀ a₁ b₁ a₂ b₂ d₀ c₁ d₁ c₂ d₂ : ℚ}
    (hfst_succ_eq : a₂ = c₂)
    (hgap_rank_fst : a₁ + 1 ≤ c₁)
    (hgap_rank_snd : b₁ + 1 ≤ d₁)
    (hYdrop : c₁ - c₂ ≤ d₀ - d₁)
    (hXdrop : b₀ - b₁ ≤ a₁ - a₂ + 1)
    (_hsnd_succ : b₂ < d₂) :
    b₀ < d₀ := by
  linarith

lemma fst_pred_strict_of_fst_succ_strict
    {a₀ a₁ b₁ a₂ b₂ c₀ c₁ d₁ c₂ d₂ : ℚ}
    (hsnd_succ_eq : b₂ = d₂)
    (hgap_rank_fst : a₁ + 1 ≤ c₁)
    (hgap_rank_snd : b₁ + 1 ≤ d₁)
    (hYdrop : d₁ - d₂ ≤ c₀ - c₁)
    (hXdrop : a₀ - a₁ ≤ b₁ - b₂ + 1)
    (_hfst_succ : a₂ < c₂) :
    a₀ < c₀ := by
  linarith

lemma snd_drop_le_fst_drop_succ_add_one
    {p : ℕ} (X : Chromosome) (hXPi : X ∈ Pi)
    (gneg : Gene) (hgneg_rank : gneg.rank = 2 * p + 1)
    (hgneg : gneg.type = GeneType.Negative) (hcoeff : X gneg = 1) :
    (signature (Chromosome.prime^[2 * p] X)).2 -
        (signature (Chromosome.prime^[2 * p + 1] X)).2 ≤
      (signature (Chromosome.prime^[2 * p + 1] X)).1 -
        (signature (Chromosome.prime^[2 * p + 2] X)).1 + 1 := by
  change (Sigma.sigma X (2 * p)).2 - (Sigma.sigma X (2 * p + 1)).2 ≤
    (Sigma.sigma X (2 * p + 1)).1 - (Sigma.sigma X (2 * p + 2)).1 + 1
  rw [Sigma.sigma_snd_diff X (2 * p) hXPi]
  rw [Sigma.sigma_fst_diff X (2 * p + 1) hXPi]
  change ((Chromosome.prime^[2 * p] X).sum (fun g m =>
      if g.type = Sigma.altType g.rank GeneType.Negative then (m : ℚ) else 0)) ≤
    ((Chromosome.prime^[2 * p + 1] X).sum (fun g m =>
      if g.type = Sigma.altType g.rank GeneType.Positive then (m : ℚ) else 0)) + 1
  rw [Sigma.prime_iterate_sum_eq X (2 * p) GeneType.Negative]
  rw [Sigma.prime_iterate_sum_eq X (2 * p + 1) GeneType.Positive]
  have heven : Int.negOnePow ((2 * p : ℕ) : ℤ) = 1 := by
    exact Int.negOnePow_even _ ⟨(p : ℤ), by norm_num; ring⟩
  have hodd : Int.negOnePow (((2 * p + 1 : ℕ) : ℤ)) = -1 := by
    exact Int.negOnePow_odd _ ⟨(p : ℤ), by norm_num⟩
  simp only [heven, hodd, one_smul, GeneType.neg_one_smul,
    GeneType.neg_positive]
  set S₀ := X.support.filter
    (fun g => 2 * p < g.rank ∧ g.type = Sigma.altType g.rank GeneType.Negative)
  set S₁ := X.support.filter
    (fun g => 2 * p + 1 < g.rank ∧
      g.type = Sigma.altType g.rank GeneType.Negative)
  have hgneg_mem_support : gneg ∈ X.support := by
    rw [Finsupp.mem_support_iff]
    omega
  have hsplit : S₀ = insert gneg S₁ := by
    ext g
    simp only [S₀, S₁, Finset.mem_filter, Finset.mem_insert]
    constructor
    · intro h
      rcases h with ⟨hgsupp, hgt, hgtype⟩
      by_cases hr : g.rank = 2 * p + 1
      · left
        apply Gene.ext (hr.trans hgneg_rank.symm)
        rw [hgtype]
        rw [Sigma.altType_odd]
        · exact hgneg.symm
        · rw [hr]
          exact Nat.not_even_iff_odd.mpr ⟨p, by ring⟩
      · right
        exact ⟨hgsupp, by omega, hgtype⟩
    · intro h
      rcases h with hg | h
      · subst hg
        refine ⟨hgneg_mem_support, ?_, ?_⟩
        · rw [hgneg_rank]
          omega
        · rw [hgneg, hgneg_rank]
          symm
          apply Sigma.altType_odd
          exact Nat.not_even_iff_odd.mpr ⟨p, by ring⟩
      · rcases h with ⟨hgsupp, hgt, hgtype⟩
        exact ⟨hgsupp, by omega, hgtype⟩
  rw [hsplit]
  have hnot : gneg ∉ S₁ := by
    simp [S₁, hgneg_rank]
  rw [Finset.sum_insert hnot]
  rw [hcoeff]
  ring_nf
  exact le_rfl

lemma fst_drop_le_snd_drop_succ_add_one
    {p : ℕ} (X : Chromosome) (hXPi : X ∈ Pi)
    (gpos : Gene) (hgpos_rank : gpos.rank = 2 * p + 1)
    (hgpos : gpos.type = GeneType.Positive) (hcoeff : X gpos = 1) :
    (signature (Chromosome.prime^[2 * p] X)).1 -
        (signature (Chromosome.prime^[2 * p + 1] X)).1 ≤
      (signature (Chromosome.prime^[2 * p + 1] X)).2 -
        (signature (Chromosome.prime^[2 * p + 2] X)).2 + 1 := by
  change (Sigma.sigma X (2 * p)).1 - (Sigma.sigma X (2 * p + 1)).1 ≤
    (Sigma.sigma X (2 * p + 1)).2 - (Sigma.sigma X (2 * p + 2)).2 + 1
  rw [Sigma.sigma_fst_diff X (2 * p) hXPi]
  rw [Sigma.sigma_snd_diff X (2 * p + 1) hXPi]
  change ((Chromosome.prime^[2 * p] X).sum (fun g m =>
      if g.type = Sigma.altType g.rank GeneType.Positive then (m : ℚ) else 0)) ≤
    ((Chromosome.prime^[2 * p + 1] X).sum (fun g m =>
      if g.type = Sigma.altType g.rank GeneType.Negative then (m : ℚ) else 0)) + 1
  rw [Sigma.prime_iterate_sum_eq X (2 * p) GeneType.Positive]
  rw [Sigma.prime_iterate_sum_eq X (2 * p + 1) GeneType.Negative]
  have heven : Int.negOnePow ((2 * p : ℕ) : ℤ) = 1 := by
    exact Int.negOnePow_even _ ⟨(p : ℤ), by norm_num; ring⟩
  have hodd : Int.negOnePow (((2 * p + 1 : ℕ) : ℤ)) = -1 := by
    exact Int.negOnePow_odd _ ⟨(p : ℤ), by norm_num⟩
  simp only [heven, hodd, one_smul, GeneType.neg_one_smul,
    GeneType.neg_negative]
  set S₀ := X.support.filter
    (fun g => 2 * p < g.rank ∧ g.type = Sigma.altType g.rank GeneType.Positive)
  set S₁ := X.support.filter
    (fun g => 2 * p + 1 < g.rank ∧
      g.type = Sigma.altType g.rank GeneType.Positive)
  have hgpos_mem_support : gpos ∈ X.support := by
    rw [Finsupp.mem_support_iff]
    omega
  have hsplit : S₀ = insert gpos S₁ := by
    ext g
    simp only [S₀, S₁, Finset.mem_filter, Finset.mem_insert]
    constructor
    · intro h
      rcases h with ⟨hgsupp, hgt, hgtype⟩
      by_cases hr : g.rank = 2 * p + 1
      · left
        apply Gene.ext (hr.trans hgpos_rank.symm)
        rw [hgtype]
        rw [Sigma.altType_odd]
        · exact hgpos.symm
        · rw [hr]
          exact Nat.not_even_iff_odd.mpr ⟨p, by ring⟩
      · right
        exact ⟨hgsupp, by omega, hgtype⟩
    · intro h
      rcases h with hg | h
      · subst hg
        refine ⟨hgpos_mem_support, ?_, ?_⟩
        · rw [hgpos_rank]
          omega
        · rw [hgpos, hgpos_rank]
          symm
          apply Sigma.altType_odd
          exact Nat.not_even_iff_odd.mpr ⟨p, by ring⟩
      · rcases h with ⟨hgsupp, hgt, hgtype⟩
        exact ⟨hgsupp, by omega, hgtype⟩
  rw [hsplit]
  have hnot : gpos ∉ S₁ := by
    simp [S₁, hgpos_rank]
  rw [Finset.sum_insert hnot]
  rw [hcoeff]
  ring_nf
  exact le_rfl

private lemma type15_diagonal_signature_eq_before
    {q j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hj : j < 2 * q + 2) :
    signature (Chromosome.prime^[j] (Y15 (le_refl q) hε).1) =
      signature (Chromosome.prime^[j] (X15 (le_refl q) hε).1) := by
  simp only [X15_eq, Y15_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  by_cases hj_eq : j = 2 * q + 1
  · subst j
    have e1 : 2 * q + 1 - (2 * q + 1) = 0 := by omega
    have e2 : 2 * q + 3 - (2 * q + 1) = 2 := by omega
    have e3 : 2 * q + 5 - (2 * q + 1) = 4 := by omega
    rw [e1, e2, e3, Gene.ofRank_zero, map_zero, zero_add]
    simp [signature_ofRank_eq₂']
  · have hj_lt : j < 2 * q + 1 := by omega
    have eA : 2 * q + 3 - j = (2 * q + 1 - j) + 2 := by omega
    have eC : 2 * q + 5 - j = (2 * q + 3 - j) + 2 := by omega
    rw [eA, eC]
    rw [signature_ofRank_eq₂' (k := 2 * q + 1 - j) (ε := ε),
      signature_ofRank_eq₂' (k := 2 * q + 1 - j) (ε := -ε),
      signature_ofRank_eq₂' (k := 2 * q + 3 - j) (ε := ε)]
    rw [eA, signature_ofRank_eq₂' (k := 2 * q + 1 - j) (ε := ε)]
    abel_nf

private lemma type15_diagonal_signature_at_pred
    {q : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * q + 2] (Y15 (le_refl q) hε).1) =
      signature (Gene.ofRank 1 ε) +
        signature (Chromosome.prime^[2 * q + 2] (X15 (le_refl q) hε).1) := by
  simp only [X15_eq, Y15_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h1 : 2 * q + 1 - (2 * q + 2) = 0 := by omega
  have h2 : 2 * q + 3 - (2 * q + 2) = 1 := by omega
  have h3 : 2 * q + 5 - (2 * q + 2) = 3 := by omega
  rw [h1, h2, h3, Gene.ofRank_zero, map_zero, zero_add]
  cases ε <;> simp [GeneType.neg_positive, GeneType.neg_negative,
    signature_ofRank_eq₂', signature_ofRank_one_positive,
    signature_ofRank_one_negative] at hε ⊢

private lemma type15_diagonal_signature_at_rank
    {q : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * q + 3] (Y15 (le_refl q) hε).1) =
      ((1 : ℚ), (1 : ℚ)) := by
  simp only [Y15_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h1 : 2 * q + 1 - (2 * q + 3) = 0 := by omega
  have h3 : 2 * q + 5 - (2 * q + 3) = 2 := by omega
  rw [h1, h3, Gene.ofRank_zero, map_zero, zero_add]
  simp [signature_ofRank_eq₂']

private lemma type15_diagonal_source_at_rank
    {q : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * q + 3] (X15 (le_refl q) hε).1) = 0 := by
  simp [X15_eq, prime_iterate_ofRank]

private lemma type15_diagonal_signature_at_succ
    {q : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * q + 4] (Y15 (le_refl q) hε).1) =
      signature (Gene.ofRank 1 ε) := by
  simp only [Y15_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h1 : 2 * q + 1 - (2 * q + 4) = 0 := by omega
  have h2 : 2 * q + 5 - (2 * q + 4) = 1 := by omega
  simp [h1, h2]

private lemma type15_diagonal_source_at_succ
    {q : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * q + 4] (X15 (le_refl q) hε).1) = 0 := by
  simp [X15_eq, prime_iterate_ofRank]

private lemma type15_diagonal_signature_eq_after
    {q j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hj : 2 * q + 4 < j) :
    signature (Chromosome.prime^[j] (Y15 (le_refl q) hε).1) =
      signature (Chromosome.prime^[j] (X15 (le_refl q) hε).1) := by
  simp only [X15_eq, Y15_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h1 : 2 * q + 1 - j = 0 := by omega
  have h2 : 2 * q + 3 - j = 0 := by omega
  have h3 : 2 * q + 5 - j = 0 := by omega
  simp [h1, h2, h3]

/-- The same-rank type15 branch, assuming the three local sigma gaps required
by its profile.  This is the branch used when a `2+1` equal-rank pair has the
strict successor gap in the component opposite to the type16 output. -/
lemma exists_mutation_le_type15_diagonal
    {N q : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (gε gnegε : Gene)
    (hgε : gε.type = ε) (hgnegε : gnegε.type = -ε)
    (hgrank : gε.rank = 2 * q + 3)
    (hrank : gε.rank = gnegε.rank)
    (hεcopy : 1 ≤ X.1.1 gε) (hnegεcopy : 1 ≤ X.1.1 gnegε)
    (hgap_pred :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * q + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 2] Y.1.1))
    (hgap_rank :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 3] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * q + 4] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 4] Y.1.1)) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : gε ≠ gnegε := by
    intro h
    have ht := congrArg Gene.type h
    rw [hgε, hgnegε] at ht
    cases he : ε with
    | NonPolarized => exact hε he
    | Positive => simp [he] at ht
    | Negative => simp [he] at ht
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gε 1 - Finsupp.single gnegε 1
  have hoddε : Odd gε.rank := by
    rw [hgrank]
    exact ⟨q + 1, by ring⟩
  have hoddnegε : Odd gnegε.rank := hrank ▸ hoddε
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hoddε) hoddnegε
  let rest : Mix (2 • Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgε_eq :
      Gene.ofRank (2 * q + 3) ε =
        (Finsupp.single gε 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gε)
    rwa [hgrank, hgε] at h
  have hgnegε_eq :
      Gene.ofRank (2 * q + 3) (-ε) =
        (Finsupp.single gnegε 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gnegε)
    rw [hgnegε, ← hrank, hgrank] at h
    exact h
  have hX15val :
      (X15 (le_refl q) hε).1 =
        Finsupp.single gε 1 + Finsupp.single gnegε 1 := by
    rw [X15_eq, hgε_eq, hgnegε_eq]
  have hXeq : (X15 (le_refl q) hε).1 + restval = X.1.1 := by
    rw [hX15val]
    exact Mix2LambdaSection17.single_pair_add_rest hεcopy hnegεcopy hne
  refine ⟨⟨(Y15 (le_refl q) hε).1 + restval,
      add_mem (Y15 (le_refl q) hε).2 rest_mem⟩, ?_, ?_⟩
  · exact (Subtype.ext hXeq :
      (X15 (le_refl q) hε : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
        Step.mk (X15 (le_refl q) hε) (Y15 (le_refl q) hε) rest
          (Primitive.type15 ε hε (le_refl q))
  · change (Y15 (le_refl q) hε).1 + restval ≤ Y.1.1
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp :
        signature (Chromosome.prime^[j] X.1.1) =
          signature (Chromosome.prime^[j] (X15 (le_refl q) hε).1) +
            signature (Chromosome.prime^[j] restval) := by
      conv_lhs => rw [← hXeq]
      rw [iterate_map_add, map_add]
    by_cases hj_before : j < 2 * q + 2
    · rw [type15_diagonal_signature_eq_before hj_before, ← hdecomp]
      exact le_iff_dominates.mp hXY.le j
    · by_cases hj_pred : j = 2 * q + 2
      · subst j
        rw [type15_diagonal_signature_at_pred]
        calc
          signature (Gene.ofRank 1 ε) +
                signature (Chromosome.prime^[2 * q + 2]
                  (X15 (le_refl q) hε).1) +
              signature (Chromosome.prime^[2 * q + 2] restval)
              = signature (Gene.ofRank 1 ε) +
                (signature (Chromosome.prime^[2 * q + 2]
                    (X15 (le_refl q) hε).1) +
                  signature (Chromosome.prime^[2 * q + 2] restval)) := by abel
          _ = signature (Gene.ofRank 1 ε) +
                signature (Chromosome.prime^[2 * q + 2] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[2 * q + 2] Y.1.1) := hgap_pred
      · by_cases hj_rank : j = 2 * q + 3
        · subst j
          rw [type15_diagonal_signature_at_rank]
          rw [type15_diagonal_source_at_rank] at hdecomp
          simp only [zero_add] at hdecomp
          rw [← hdecomp]
          exact hgap_rank
        · by_cases hj_succ : j = 2 * q + 4
          · subst j
            rw [type15_diagonal_signature_at_succ]
            rw [type15_diagonal_source_at_succ] at hdecomp
            simp only [zero_add] at hdecomp
            rw [← hdecomp]
            exact hgap_succ
          · have hj_after : 2 * q + 4 < j := by omega
            rw [type15_diagonal_signature_eq_after hj_after, ← hdecomp]
            exact le_iff_dominates.mp hXY.le j

/-- In the same-rank type15 situation, the rank where the two source genes
vanish has the required `(1,1)` dominance gap.  This is the `1+1` analogue of
`type16_diagonal_gap_rank`. -/
lemma type15_diagonal_gap_rank
    {N q : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gε gnegε : Gene)
    (hgε : gε.type = ε) (hgnegε : gnegε.type = -ε)
    (hgrank : gε.rank = 2 * q + 3)
    (hrank : gε.rank = gnegε.rank)
    (hεcopy : 1 ≤ X.1.1 gε) (hnegεcopy : 1 ≤ X.1.1 gnegε) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
      signature (Chromosome.prime^[2 * q + 3] Y.1.1) := by
  have hne : gε ≠ gnegε := by
    intro h
    have ht := congrArg Gene.type h
    rw [hgε, hgnegε] at ht
    cases he : ε with
    | NonPolarized => exact hε he
    | Positive => simp [he] at ht
    | Negative => simp [he] at ht
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gε 1 - Finsupp.single gnegε 1
  have hgε_eq :
      Gene.ofRank (2 * q + 3) ε =
        (Finsupp.single gε 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gε)
    rwa [hgrank, hgε] at h
  have hgnegε_eq :
      Gene.ofRank (2 * q + 3) (-ε) =
        (Finsupp.single gnegε 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gnegε)
    rw [hgnegε, ← hrank, hgrank] at h
    exact h
  have hX15val :
      (X15 (le_refl q) hε).1 =
        Finsupp.single gε 1 + Finsupp.single gnegε 1 := by
    rw [X15_eq, hgε_eq, hgnegε_eq]
  have hXeq : (X15 (le_refl q) hε).1 + restval = X.1.1 := by
    rw [hX15val]
    exact Mix2LambdaSection17.single_pair_add_rest hεcopy hnegεcopy hne
  have hY_no_gene : ∀ g : Gene, g.rank = 2 * q + 3 → Y.1.1 g = 0 := by
    intro g hgr
    by_contra hzero
    have hgY : 0 < Y.1.1 g := Nat.pos_of_ne_zero hzero
    have hpol : g.type ≠ .NonPolarized := by
      have hgodd : Odd g.rank := by rw [hgr]; exact ⟨q + 1, by ring⟩
      have : 0 < Y.1.1.oddPart g := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hgodd]
        exact hgY
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) g
        (Finsupp.mem_support_iff.mpr this.ne')
    cases he : ε with
    | NonPolarized => exact hε he
    | Positive =>
        cases ht : g.type with
        | NonPolarized => exact hpol ht
        | Positive =>
            have heq : g = gε :=
              Gene.ext (hgr.trans hgrank.symm) (ht.trans (he.symm.trans hgε.symm))
            have hle := hcommon gε (by omega)
            rw [heq] at hgY
            omega
        | Negative =>
            have heq : g = gnegε :=
              Gene.ext (hgr.trans hgrank.symm |>.trans hrank)
                (calc
                  g.type = .Negative := ht
                  _ = gnegε.type := by
                    rw [hgnegε, he, GeneType.neg_positive])
            have hle := hcommon gnegε (by omega)
            rw [heq] at hgY
            omega
    | Negative =>
        cases ht : g.type with
        | NonPolarized => exact hpol ht
        | Positive =>
            have heq : g = gnegε :=
              Gene.ext (hgr.trans hgrank.symm |>.trans hrank)
                (calc
                  g.type = .Positive := ht
                  _ = gnegε.type := by
                    rw [hgnegε, he, GeneType.neg_negative])
            have hle := hcommon gnegε (by omega)
            rw [heq] at hgY
            omega
        | Negative =>
            have heq : g = gε :=
              Gene.ext (hgr.trans hgrank.symm) (ht.trans (he.symm.trans hgε.symm))
            have hle := hcommon gε (by omega)
            rw [heq] at hgY
            omega
  have hYr_pred : Chromosome.prime^[2 * q + 2] Y.1.1 ≠ 0 := by
    intro hzero
    have hdom := le_iff_dominates.mp hXY.le (2 * q + 2)
    have hsource :
        ((1 : ℚ), (1 : ℚ)) ≤
          signature (Chromosome.prime^[2 * q + 2] X.1.1) := by
      have hdecomp :
          signature (Chromosome.prime^[2 * q + 2] X.1.1) =
            signature (Chromosome.prime^[2 * q + 2] (X15 (le_refl q) hε).1) +
              signature (Chromosome.prime^[2 * q + 2] restval) := by
        conv_lhs => rw [← hXeq]
        rw [iterate_map_add, map_add]
      have hsrc :
          ((1 : ℚ), (1 : ℚ)) ≤
            signature (Chromosome.prime^[2 * q + 2] (X15 (le_refl q) hε).1) := by
        simp only [X15_eq, iterate_map_add, prime_iterate_ofRank, map_add]
        have hone : 2 * q + 3 - (2 * q + 2) = 1 := by omega
        rw [hone]
        cases ε with
        | NonPolarized => exact False.elim (hε rfl)
        | Positive =>
            simp [signature_ofRank_one_positive, signature_ofRank_one_negative]
        | Negative =>
            simp [signature_ofRank_one_positive, signature_ofRank_one_negative]
      rw [hdecomp]
      exact hsrc.trans (le_add_of_nonneg_right (signature_nonneg _))
    rw [hzero, map_zero] at hdom
    exact (not_le_of_gt (show (0 : ℚ) < 1 by norm_num))
      (hsource.1.trans hdom.1)
  have hYr : Chromosome.prime^[2 * q + 3] Y.1.1 ≠ 0 :=
    Mix2LambdaSection17.prime_iterate_ne_zero_of_no_gene (by omega)
      hY_no_gene (by simpa only [show 2 * q + 3 - 1 = 2 * q + 2 by omega]
        using hYr_pred)
  have hle_r := le_iff_dominates.mp hXY.le (2 * q + 3)
  have hne_r :
      signature (Chromosome.prime^[2 * q + 3] X.1.1) ≠
        signature (Chromosome.prime^[2 * q + 3] Y.1.1) := by
    intro heq
    have hrank_lt := h17_1 (2 * q + 3) (by omega) hYr
    have := congr_arg (fun q : ℚ × ℚ => q.1 + q.2) heq
    simp only [signature_sum_eq_rank] at this
    exact (ne_of_lt hrank_lt) (by exact_mod_cast this)
  have hXr_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 (2 * q + 3)
  have hYr_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 (2 * q + 3)
  have hodd : ¬ Even (2 * q + 3) :=
    Nat.not_even_iff_odd.mpr ⟨q + 1, by ring⟩
  rw [if_neg hodd] at hXr_mem hYr_mem
  exact Mix2LambdaSection17.one_pair_add_le_of_lt_Mix_Pi_2Lambda
    hXr_mem hYr_mem hle_r hne_r

/-- Positive-double wrong-component type15 branch:
`2g⁺(2q+3)+g⁻(2q+3)` uses the pair
`g⁻(2q+3)+g⁺(2q+3)` as a type15 source and leaves one `g⁺` in the rest. -/
lemma exists_mutation_le_type15_positive_of_snd_lt
    {N q : ℕ}
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgpos_rank : gpos.rank = 2 * q + 3)
    (hrank : gpos.rank = gneg.rank)
    (hpos : 1 ≤ X.1.1 gpos) (hneg : 1 ≤ X.1.1 gneg)
    (hgap_rank :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 3] Y.1.1))
    (hsnd_pred :
      (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2)
    (hsnd_succ :
      (signature (Chromosome.prime^[2 * q + 4] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hgap_pred := type16_succ_gap_negative X Y hXY hsnd_pred
  have hgap_succ := type16_succ_gap_negative X Y hXY (p := q + 1) hsnd_succ
  apply exists_mutation_le_type15_diagonal
    (ε := GeneType.Negative) (by decide) X Y hXY
    gneg gpos hgneg
  · simpa using hgpos
  · rw [← hrank, hgpos_rank]
  · exact hrank.symm
  · exact hneg
  · exact hpos
  · exact hgap_pred
  · exact hgap_rank
  · simpa [show 2 * (q + 1) + 2 = 2 * q + 4 by omega] using hgap_succ

/-- The positive type15 branch with the middle `(1,1)` gap discharged from
the reduced §17 hypotheses. -/
lemma exists_mutation_le_type15_positive_of_snd_lt_of_pair
    {N q : ℕ}
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgpos_rank : gpos.rank = 2 * q + 3)
    (hrank : gpos.rank = gneg.rank)
    (hpos : 1 ≤ X.1.1 gpos) (hneg : 1 ≤ X.1.1 gneg)
    (hsnd_pred :
      (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2)
    (hsnd_succ :
      (signature (Chromosome.prime^[2 * q + 4] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hgneg_rank : gneg.rank = 2 * q + 3 := by
    rw [← hrank, hgpos_rank]
  have hgap_rank :=
    type15_diagonal_gap_rank (ε := GeneType.Negative) (by decide)
      X Y hXY hcommon h17_1 gneg gpos hgneg (by simpa using hgpos)
      hgneg_rank hrank.symm hneg hpos
  exact exists_mutation_le_type15_positive_of_snd_lt X Y hXY
    gpos gneg hgpos hgneg hgpos_rank hrank hpos hneg hgap_rank
    hsnd_pred hsnd_succ

/-- Negative-double wrong-component type15 branch:
`g⁺(2q+3)+2g⁻(2q+3)` uses the pair
`g⁺(2q+3)+g⁻(2q+3)` as a type15 source and leaves one `g⁻` in the rest. -/
lemma exists_mutation_le_type15_negative_of_fst_lt
    {N q : ℕ}
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgneg_rank : gneg.rank = 2 * q + 3)
    (hrank : gpos.rank = gneg.rank)
    (hpos : 1 ≤ X.1.1 gpos) (hneg : 1 ≤ X.1.1 gneg)
    (hgap_rank :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 3] Y.1.1))
    (hfst_pred :
      (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1)
    (hfst_succ :
      (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hgap_pred := type16_succ_gap_positive X Y hXY hfst_pred
  have hgap_succ := type16_succ_gap_positive X Y hXY (p := q + 1) hfst_succ
  apply exists_mutation_le_type15_diagonal
    (ε := GeneType.Positive) (by decide) X Y hXY
    gpos gneg hgpos
  · simpa using hgneg
  · rw [hrank, hgneg_rank]
  · exact hrank
  · exact hpos
  · exact hneg
  · exact hgap_pred
  · exact hgap_rank
  · simpa [show 2 * (q + 1) + 2 = 2 * q + 4 by omega] using hgap_succ

/-- The negative type15 branch with the middle `(1,1)` gap discharged from
the reduced §17 hypotheses. -/
lemma exists_mutation_le_type15_negative_of_fst_lt_of_pair
    {N q : ℕ}
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgneg_rank : gneg.rank = 2 * q + 3)
    (hrank : gpos.rank = gneg.rank)
    (hpos : 1 ≤ X.1.1 gpos) (hneg : 1 ≤ X.1.1 gneg)
    (hfst_pred :
      (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1)
    (hfst_succ :
      (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hgap_rank :=
    type15_diagonal_gap_rank (ε := GeneType.Positive) (by decide)
      X Y hXY hcommon h17_1 gpos gneg hgpos (by simpa using hgneg)
      (by rw [hrank, hgneg_rank]) hrank hpos hneg
  exact exists_mutation_le_type15_negative_of_fst_lt X Y hXY
    gpos gneg hgpos hgneg hgneg_rank hrank hpos hneg hgap_rank
    hfst_pred hfst_succ

end Mix2LambdaPi
