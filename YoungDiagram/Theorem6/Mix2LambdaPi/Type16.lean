import YoungDiagram.Theorem6.Mix2LambdaPi.Type13

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-- A thin theorem-level wrapper for general type16.  The caller supplies the
source decomposition and the dominance bound after replacing the source by the
type16 target. -/
lemma exists_mutation_le_type16_of_decomp
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N) (restval : Chromosome)
    (hXeq : (X16 h_le hε).1 + restval = X.1.1)
    (hrest : restval ∈ Mix (2 • Lambda, Pi))
    (hZle : (Y16 h_le hε).1 + restval ≤ Y.1.1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let rest : Mix (2 • Lambda, Pi) := ⟨restval, hrest⟩
  refine ⟨⟨(Y16 h_le hε).1 + restval,
      add_mem (Y16 h_le hε).2 hrest⟩, ?_, hZle⟩
  exact (Subtype.ext hXeq :
      (X16 h_le hε : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
    Step.mk (X16 h_le hε) (Y16 h_le hε) rest
      (Primitive.type16 ε hε h_le)

/-- Concrete-gene wrapper for general type16.  This packages the source
decomposition `2g^ε(2m+1)+g^{-ε}(2n+1)+rest` and the rest membership; the
caller still supplies the final dominance bound for the type16 target plus the
rest.  The rank-one boundary used in §17 Case 3 is the specialization `m = 0`. -/
lemma exists_mutation_le_type16_of_genes
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N)
    (gdouble gsingle : Gene)
    (hdouble_type : gdouble.type = ε)
    (hsingle_type : gsingle.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * m + 1)
    (hsingle_rank : gsingle.rank = 2 * n + 1)
    (hdouble : 2 ≤ X.1.1 gdouble) (hsingle : 1 ≤ X.1.1 gsingle)
    (hne : gdouble ≠ gsingle)
    (hZle :
      (Y16 h_le hε).1 +
          (X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
            Finsupp.single gsingle 1) ≤ Y.1.1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
      Finsupp.single gsingle 1
  have hodddouble : Odd gdouble.rank := by
    rw [hdouble_rank]
    exact ⟨m, rfl⟩
  have hoddsingle : Odd gsingle.rank := by
    rw [hsingle_rank]
    exact ⟨n, rfl⟩
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi
        (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hodddouble) hodddouble)
      hoddsingle
  have hgdouble_eq :
      Gene.ofRank (2 * m + 1) ε =
        (Finsupp.single gdouble 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gdouble)
    rwa [hdouble_rank, hdouble_type] at h
  have hgsingle_eq :
      Gene.ofRank (2 * n + 1) (-ε) =
        (Finsupp.single gsingle 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gsingle)
    rwa [hsingle_rank, hsingle_type] at h
  have hX16val :
      (X16 h_le hε).1 =
        Finsupp.single gdouble 1 + Finsupp.single gdouble 1 +
          Finsupp.single gsingle 1 := by
    rw [X16_eq, hgdouble_eq, hgsingle_eq]
  have hXeq : (X16 h_le hε).1 + restval = X.1.1 := by
    rw [hX16val]
    exact Mix2LambdaSection17.double_single_pair_add_rest
      hdouble hsingle hne
  exact exists_mutation_le_type16_of_decomp hε h_le X Y restval hXeq
    rest_mem hZle

private lemma type16_diagonal_signature_eq_before
    {p j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hj : j < 2 * p + 1) :
    signature (Chromosome.prime^[j] (Y16 (le_refl p) hε).1) =
      signature (Chromosome.prime^[j] (X16 (le_refl p) hε).1) := by
  have hj' : j ≤ 2 * p := by omega
  simp only [X16_eq, Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h := mutation_type16_sig_eq_aux (n := p) (m := p) (ε := ε)
    ((2 * p - j) / 2) ((2 * p - j) % 2)
  have eq1 :
      2 * ((2 * p - j) / 2) + 1 + (2 * p - j) % 2 =
        2 * p + 1 - j := by omega
  have eq2 :
      2 * (((2 * p - j) / 2) + (p - p)) + 1 + (2 * p - j) % 2 =
        2 * p + 1 - j := by omega
  have eq3 :
      2 * ((2 * p - j) / 2) + (2 * p - j) % 2 =
        2 * p - j := by omega
  have eq4 :
      2 * (((2 * p - j) / 2) + (p - p)) + 3 + (2 * p - j) % 2 =
        2 * p + 3 - j := by omega
  rw [eq1, eq2, eq3, eq4] at h
  exact h.symm

private lemma type16_diagonal_signature_at_rank
    {p : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * p + 1] (Y16 (le_refl p) hε).1) =
      ((1 : ℚ), (1 : ℚ)) := by
  simp only [Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h0 : 2 * p - (2 * p + 1) = 0 := by omega
  have h2 : 2 * p + 3 - (2 * p + 1) = 2 := by omega
  rw [h0, h2, Gene.ofRank_zero, map_zero, zero_add,
    signature_ofRank_eq₂']
  simp

private lemma type16_diagonal_source_at_rank
    {p : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * p + 1] (X16 (le_refl p) hε).1) = 0 := by
  simp [X16_eq, prime_iterate_ofRank]

private lemma type16_diagonal_signature_at_succ
    {p : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * p + 2] (Y16 (le_refl p) hε).1) =
      signature (Gene.ofRank 1 ε) := by
  simp only [Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h0 : 2 * p - (2 * p + 2) = 0 := by omega
  have h1 : 2 * p + 3 - (2 * p + 2) = 1 := by omega
  simp [h0, h1]

private lemma type16_diagonal_source_at_succ
    {p : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * p + 2] (X16 (le_refl p) hε).1) = 0 := by
  simp [X16_eq, prime_iterate_ofRank]

private lemma type16_diagonal_signature_eq_after
    {p j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hj : 2 * p + 2 < j) :
    signature (Chromosome.prime^[j] (Y16 (le_refl p) hε).1) =
      signature (Chromosome.prime^[j] (X16 (le_refl p) hε).1) := by
  simp only [X16_eq, Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h0 : 2 * p - j = 0 := by omega
  have h1 : 2 * p + 1 - j = 0 := by omega
  have h3 : 2 * p + 3 - j = 0 := by omega
  simp [h0, h1, h3]

private lemma type16_rank_one_signature_eq_zero
    {q : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[0] (Y16 (Nat.zero_le (q + 1)) hε).1) =
      signature (Chromosome.prime^[0] (X16 (Nat.zero_le (q + 1)) hε).1) := by
  simpa only [Function.iterate_zero_apply, X16_eq, Y16_eq] using
    (mutation_type16_signature_eq (ε := ε) (m := 0) (n := q + 1)
      (h_le := Nat.zero_le (q + 1))).symm

private lemma type16_rank_one_signature_odd_mid
    {q j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hjlo : 1 ≤ j) (hjhi : j ≤ 2 * q + 3) (hjodd : ¬ Even j) :
    signature (Chromosome.prime^[j] (Y16 (Nat.zero_le (q + 1)) hε).1) =
      signature (Chromosome.prime^[j] (X16 (Nat.zero_le (q + 1)) hε).1) +
        ((1 : ℚ), (1 : ℚ)) := by
  simp only [X16_eq, Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h1 : 1 - j = 0 := by omega
  have h0 : 0 - j = 0 := by omega
  have htop : 2 * (q + 1) + 3 - j =
      (2 * (q + 1) + 1 - j) + 2 := by
    omega
  rw [h1, h0, htop, Gene.ofRank_zero, map_zero, zero_add, zero_add,
    signature_ofRank_eq₂']
  have hk_even : Even (2 * (q + 1) + 1 - j) := by
    rcases Nat.not_even_iff_odd.mp hjodd with ⟨t, rfl⟩
    use q + 1 - t
    omega
  rw [signature_ofRank_even_half (ε := ε) hk_even,
    signature_ofRank_even_half (ε := -ε) hk_even]
  simp

private lemma type16_rank_one_signature_even_mid
    {q j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hjlo : 1 ≤ j) (hjhi : j ≤ 2 * q + 3) (hjeven : Even j) :
    signature (Chromosome.prime^[j] (Y16 (Nat.zero_le (q + 1)) hε).1) =
      signature (Chromosome.prime^[j] (X16 (Nat.zero_le (q + 1)) hε).1) +
        (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε)) := by
  simp only [X16_eq, Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h1 : 1 - j = 0 := by omega
  have h0 : 0 - j = 0 := by omega
  have htop : 2 * (q + 1) + 3 - j =
      (2 * (q + 1) + 1 - j) + 2 := by
    omega
  rw [h1, h0, htop, Gene.ofRank_zero, map_zero, zero_add, zero_add,
    signature_ofRank_eq₂']
  have hj_le_even : j ≤ 2 * q + 2 := by
    rcases hjeven with ⟨t, ht⟩
    rw [ht] at hjhi ⊢
    omega
  have hk_pos : 1 ≤ 2 * (q + 1) + 1 - j := by omega
  have hk_odd : ¬ Even (2 * (q + 1) + 1 - j) := by
    intro hk_even
    rcases hjeven with ⟨t, ht⟩
    rw [ht] at hk_even
    rcases hk_even with ⟨u, hu⟩
    omega
  have hk_pred_even : Even (2 * (q + 1) + 1 - j - 1) := by
    by_contra h
    exact hk_odd ((Nat.even_sub_one hk_pos).2 h)
  cases ε with
  | NonPolarized => exact False.elim (hε rfl)
  | Positive =>
      simp only [GeneType.neg_positive, signature_ofRank_one_positive]
      rw [signature_ofRank_positive hk_pos, signature_ofRank_negative hk_pos,
        signature_ofRank_even_half (ε := GeneType.Negative) hk_pred_even,
        signature_ofRank_even_half (ε := GeneType.Positive) hk_pred_even]
      simp
      ring_nf
  | Negative =>
      simp only [GeneType.neg_negative, signature_ofRank_one_negative]
      rw [signature_ofRank_negative hk_pos, signature_ofRank_positive hk_pos,
        signature_ofRank_even_half (ε := GeneType.Positive) hk_pred_even,
        signature_ofRank_even_half (ε := GeneType.Negative) hk_pred_even]
      simp
      ring_nf

private lemma type16_rank_one_signature_succ
    {q : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * q + 4]
        (Y16 (Nat.zero_le (q + 1)) hε).1) =
      signature (Chromosome.prime^[2 * q + 4]
          (X16 (Nat.zero_le (q + 1)) hε).1) +
        signature (Gene.ofRank 1 ε) := by
  simp only [X16_eq, Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h0 : 0 - (2 * q + 4) = 0 := by omega
  have h1 : 1 - (2 * q + 4) = 0 := by omega
  have htop_source : 2 * (q + 1) + 1 - (2 * q + 4) = 0 := by omega
  have htop_target : 2 * (q + 1) + 3 - (2 * q + 4) = 1 := by omega
  simp [h0, h1, htop_source, htop_target]

private lemma type16_rank_one_signature_eq_after
    {q j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hj : 2 * q + 4 < j) :
    signature (Chromosome.prime^[j] (Y16 (Nat.zero_le (q + 1)) hε).1) =
      signature (Chromosome.prime^[j] (X16 (Nat.zero_le (q + 1)) hε).1) := by
  simp only [X16_eq, Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h0 : 0 - j = 0 := by omega
  have h1 : 1 - j = 0 := by omega
  have hsource : 2 * (q + 1) + 1 - j = 0 := by omega
  have htarget : 2 * (q + 1) + 3 - j = 0 := by omega
  simp [h0, h1, hsource, htarget]

/-- Dominance assembly for the rank-one lower endpoint of type16,
`2g^ε(1)+g^{-ε}(2q+3) → 2g(0)+g^ε(2q+5)`.

The target-source signature delta is parity-dependent in the middle window:
odd levels need `(1,1)` slack, while even levels need two copies of the
rank-one `ε` signature. -/
lemma type16_rank_one_target_add_rest_le_of_gaps
    {N q : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1) (restval : Chromosome)
    (hXeq : (X16 (Nat.zero_le (q + 1)) hε).1 + restval = X.1.1)
    (hgap_odd : ∀ j, 1 ≤ j → j ≤ 2 * q + 3 → ¬ Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_even : ∀ j, 1 ≤ j → j ≤ 2 * q + 3 → Even j →
      (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * q + 4] X.1.1) ≤
        signature (Chromosome.prime^[2 * q + 4] Y.1.1)) :
    (Y16 (Nat.zero_le (q + 1)) hε).1 + restval ≤ Y.1.1 := by
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp :
      signature (Chromosome.prime^[j] X.1.1) =
        signature (Chromosome.prime^[j] (X16 (Nat.zero_le (q + 1)) hε).1) +
          signature (Chromosome.prime^[j] restval) := by
    conv_lhs => rw [← hXeq]
    rw [iterate_map_add, map_add]
  by_cases hj_zero : j = 0
  · subst j
    rw [type16_rank_one_signature_eq_zero, ← hdecomp]
    exact le_iff_dominates.mp hXY.le 0
  · by_cases hj_mid : j ≤ 2 * q + 3
    · have hjlo : 1 ≤ j := by omega
      by_cases hjeven : Even j
      · rw [type16_rank_one_signature_even_mid hjlo hj_mid hjeven]
        calc
          (signature (Chromosome.prime^[j] (X16 (Nat.zero_le (q + 1)) hε).1) +
                  (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε))) +
              signature (Chromosome.prime^[j] restval)
              = (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε)) +
                  (signature (Chromosome.prime^[j]
                      (X16 (Nat.zero_le (q + 1)) hε).1) +
                    signature (Chromosome.prime^[j] restval)) := by abel
          _ = (signature (Gene.ofRank 1 ε) + signature (Gene.ofRank 1 ε)) +
                signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
            hgap_even j hjlo hj_mid hjeven
      · rw [type16_rank_one_signature_odd_mid hjlo hj_mid hjeven]
        calc
          (signature (Chromosome.prime^[j] (X16 (Nat.zero_le (q + 1)) hε).1) +
                  ((1 : ℚ), (1 : ℚ))) +
              signature (Chromosome.prime^[j] restval)
              = ((1 : ℚ), (1 : ℚ)) +
                  (signature (Chromosome.prime^[j]
                      (X16 (Nat.zero_le (q + 1)) hε).1) +
                    signature (Chromosome.prime^[j] restval)) := by abel
          _ = ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
            hgap_odd j hjlo hj_mid hjeven
    · by_cases hj_succ : j = 2 * q + 4
      · subst j
        rw [type16_rank_one_signature_succ]
        calc
          (signature (Chromosome.prime^[2 * q + 4]
                    (X16 (Nat.zero_le (q + 1)) hε).1) +
                  signature (Gene.ofRank 1 ε)) +
              signature (Chromosome.prime^[2 * q + 4] restval)
              = signature (Gene.ofRank 1 ε) +
                  (signature (Chromosome.prime^[2 * q + 4]
                      (X16 (Nat.zero_le (q + 1)) hε).1) +
                    signature (Chromosome.prime^[2 * q + 4] restval)) := by abel
          _ = signature (Gene.ofRank 1 ε) +
                signature (Chromosome.prime^[2 * q + 4] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[2 * q + 4] Y.1.1) := hgap_succ
      · have hj_after : 2 * q + 4 < j := by omega
        rw [type16_rank_one_signature_eq_after hj_after, ← hdecomp]
        exact le_iff_dominates.mp hXY.le j

/-- In the diagonal type16 `2+1` situation, the rank where the two lower
nonpolarized genes are created has the required `(1,1)` dominance gap. -/
lemma type16_diagonal_gap_rank
    {N p : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gdouble gsingle : Gene)
    (hdouble_type : gdouble.type = ε)
    (hsingle_type : gsingle.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * p + 1)
    (hrank : gdouble.rank = gsingle.rank)
    (hdouble : 2 ≤ X.1.1 gdouble) (hsingle : 1 ≤ X.1.1 gsingle) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * p + 1] X.1.1) ≤
      signature (Chromosome.prime^[2 * p + 1] Y.1.1) := by
  have hne : gdouble ≠ gsingle := by
    intro h
    have ht := congrArg Gene.type h
    rw [hdouble_type, hsingle_type] at ht
    cases he : ε with
    | NonPolarized => exact hε he
    | Positive => simp [he] at ht
    | Negative => simp [he] at ht
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
      Finsupp.single gsingle 1
  have hgdouble_eq :
      Gene.ofRank (2 * p + 1) ε =
        (Finsupp.single gdouble 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gdouble)
    rwa [hdouble_rank, hdouble_type] at h
  have hgsingle_eq :
      Gene.ofRank (2 * p + 1) (-ε) =
        (Finsupp.single gsingle 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gsingle)
    rwa [hsingle_type, ← hrank, hdouble_rank] at h
  have hX16val :
      (X16 (le_refl p) hε).1 =
        Finsupp.single gdouble 1 + Finsupp.single gdouble 1 +
          Finsupp.single gsingle 1 := by
    rw [X16_eq, hgdouble_eq, hgsingle_eq]
  have hXeq : (X16 (le_refl p) hε).1 + restval = X.1.1 := by
    rw [hX16val]
    exact Mix2LambdaSection17.double_single_pair_add_rest
      hdouble hsingle hne
  have hY_no_gene : ∀ g : Gene, g.rank = 2 * p + 1 → Y.1.1 g = 0 := by
    intro g hgr
    by_contra hzero
    have hgY : 0 < Y.1.1 g := Nat.pos_of_ne_zero hzero
    have hpol : g.type ≠ .NonPolarized := by
      have hgodd : Odd g.rank := by rw [hgr]; exact ⟨p, rfl⟩
      have : 0 < Y.1.1.oddPart g := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hgodd]
        exact hgY
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) g
        (Finsupp.mem_support_iff.mpr this.ne')
    have hε_cases : ε = .Positive ∨ ε = .Negative := by
      cases ε with
      | NonPolarized => exact False.elim (hε rfl)
      | Positive => exact Or.inl rfl
      | Negative => exact Or.inr rfl
    rcases hε_cases with hεpos | hεneg
    · cases ht : g.type with
      | NonPolarized => exact hpol ht
      | Positive =>
          have heq : g = gdouble :=
            Gene.ext (hgr.trans hdouble_rank.symm)
              (ht.trans (hεpos.symm.trans hdouble_type.symm))
          have hle := hcommon gdouble (by omega)
          rw [heq] at hgY
          omega
      | Negative =>
          have heq : g = gsingle :=
            Gene.ext (hgr.trans hdouble_rank.symm |>.trans hrank)
              (calc
                g.type = .Negative := ht
                _ = gsingle.type := by
                  rw [hsingle_type, hεpos, GeneType.neg_positive])
          have hle := hcommon gsingle (by omega)
          rw [heq] at hgY
          omega
    · cases ht : g.type with
      | NonPolarized => exact hpol ht
      | Positive =>
          have heq : g = gsingle :=
            Gene.ext (hgr.trans hdouble_rank.symm |>.trans hrank)
              (calc
                g.type = .Positive := ht
                _ = gsingle.type := by
                  rw [hsingle_type, hεneg, GeneType.neg_negative])
          have hle := hcommon gsingle (by omega)
          rw [heq] at hgY
          omega
      | Negative =>
          have heq : g = gdouble :=
            Gene.ext (hgr.trans hdouble_rank.symm)
              (ht.trans (hεneg.symm.trans hdouble_type.symm))
          have hle := hcommon gdouble (by omega)
          rw [heq] at hgY
          omega
  have hYr_pred : Chromosome.prime^[2 * p] Y.1.1 ≠ 0 := by
    intro hzero
    have hdom := le_iff_dominates.mp hXY.le (2 * p)
    have hsource :
        ((1 : ℚ), (1 : ℚ)) ≤
          signature (Chromosome.prime^[2 * p] X.1.1) := by
      have hdecomp :
          signature (Chromosome.prime^[2 * p] X.1.1) =
            signature (Chromosome.prime^[2 * p] (X16 (le_refl p) hε).1) +
              signature (Chromosome.prime^[2 * p] restval) := by
        conv_lhs => rw [← hXeq]
        rw [iterate_map_add, map_add]
      have hsrc :
          ((1 : ℚ), (1 : ℚ)) ≤
            signature (Chromosome.prime^[2 * p] (X16 (le_refl p) hε).1) := by
        simp only [X16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
        have hone : 2 * p + 1 - 2 * p = 1 := by omega
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
  have hYr : Chromosome.prime^[2 * p + 1] Y.1.1 ≠ 0 :=
    Mix2LambdaSection17.prime_iterate_ne_zero_of_no_gene (by omega)
      hY_no_gene (by simpa only [show 2 * p + 1 - 1 = 2 * p by omega]
        using hYr_pred)
  have hle_r := le_iff_dominates.mp hXY.le (2 * p + 1)
  have hne_r :
      signature (Chromosome.prime^[2 * p + 1] X.1.1) ≠
        signature (Chromosome.prime^[2 * p + 1] Y.1.1) := by
    intro heq
    have hrank_lt := h17_1 (2 * p + 1) (by omega) hYr
    have := congr_arg (fun q : ℚ × ℚ => q.1 + q.2) heq
    simp only [signature_sum_eq_rank] at this
    exact (ne_of_lt hrank_lt) (by exact_mod_cast this)
  have hXr_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 (2 * p + 1)
  have hYr_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 (2 * p + 1)
  have hodd : ¬ Even (2 * p + 1) := Nat.not_even_iff_odd.mpr ⟨p, rfl⟩
  rw [if_neg hodd] at hXr_mem hYr_mem
  exact Mix2LambdaSection17.one_pair_add_le_of_lt_Mix_Pi_2Lambda
    hXr_mem hYr_mem hle_r hne_r

/-- At the successor level of a positive type16 move, a strict first-component
gap gives exactly the `signature (ofRank 1 Positive)` gap. -/
lemma type16_succ_gap_positive
    {N p : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hfst :
      (signature (Chromosome.prime^[2 * p + 2] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).1) :
    signature (Gene.ofRank 1 .Positive) +
        signature (Chromosome.prime^[2 * p + 2] X.1.1) ≤
      signature (Chromosome.prime^[2 * p + 2] Y.1.1) := by
  have hXk_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 (2 * p + 2)
  have hYk_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 (2 * p + 2)
  have heven : Even (2 * p + 2) := ⟨p + 1, by ring⟩
  rw [if_pos heven] at hXk_mem hYk_mem
  have hfst_gap :=
    Mix2LambdaSection17.add_one_le_fst_of_lt_Mix_2Lambda_Pi
      hXk_mem hYk_mem hfst
  have hle := le_iff_dominates.mp hXY.le (2 * p + 2)
  rw [signature_ofRank_one_positive]
  exact ⟨by simpa [Prod.fst_add, add_comm] using hfst_gap, by simpa using hle.2⟩

/-- At the successor level of a negative type16 move, a strict second-component
gap gives exactly the `signature (ofRank 1 Negative)` gap. -/
lemma type16_succ_gap_negative
    {N p : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hsnd :
      (signature (Chromosome.prime^[2 * p + 2] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).2) :
    signature (Gene.ofRank 1 .Negative) +
        signature (Chromosome.prime^[2 * p + 2] X.1.1) ≤
      signature (Chromosome.prime^[2 * p + 2] Y.1.1) := by
  have hXk_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 (2 * p + 2)
  have hYk_mem := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 (2 * p + 2)
  have heven : Even (2 * p + 2) := ⟨p + 1, by ring⟩
  rw [if_pos heven] at hXk_mem hYk_mem
  have hsnd_gap :=
    Mix2LambdaSection17.add_one_le_snd_of_lt_Mix_2Lambda_Pi
      hXk_mem hYk_mem hsnd
  have hle := le_iff_dominates.mp hXY.le (2 * p + 2)
  rw [signature_ofRank_one_negative]
  exact ⟨by simpa using hle.1, by simpa [Prod.snd_add, add_comm] using hsnd_gap⟩

/-- The diagonal type16 step for a `2+1` pair, assuming the two precise sigma
gaps where the target exceeds the source. -/
lemma exists_mutation_le_type16_diagonal
    {N p : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (gdouble gsingle : Gene)
    (hdouble_type : gdouble.type = ε)
    (hsingle_type : gsingle.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * p + 1)
    (hrank : gdouble.rank = gsingle.rank)
    (hdouble : 2 ≤ X.1.1 gdouble) (hsingle : 1 ≤ X.1.1 gsingle)
    (hgap_rank :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * p + 1] X.1.1) ≤
        signature (Chromosome.prime^[2 * p + 1] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * p + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * p + 2] Y.1.1)) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : gdouble ≠ gsingle := by
    intro h
    have ht := congrArg Gene.type h
    rw [hdouble_type, hsingle_type] at ht
    cases he : ε with
    | NonPolarized => exact hε he
    | Positive => simp [he] at ht
    | Negative => simp [he] at ht
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
      Finsupp.single gsingle 1
  have hodddouble : Odd gdouble.rank := by
    rw [hdouble_rank]
    exact ⟨p, rfl⟩
  have hoddsingle : Odd gsingle.rank := hrank ▸ hodddouble
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi
        (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hodddouble) hodddouble)
      hoddsingle
  let rest : Mix (2 • Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgdouble_eq :
      Gene.ofRank (2 * p + 1) ε =
        (Finsupp.single gdouble 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gdouble)
    rwa [hdouble_rank, hdouble_type] at h
  have hgsingle_eq :
      Gene.ofRank (2 * p + 1) (-ε) =
        (Finsupp.single gsingle 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gsingle)
    rwa [hsingle_type, ← hrank, hdouble_rank] at h
  have hX16val :
      (X16 (le_refl p) hε).1 =
        Finsupp.single gdouble 1 + Finsupp.single gdouble 1 +
          Finsupp.single gsingle 1 := by
    rw [X16_eq, hgdouble_eq, hgsingle_eq]
  have hXeq : (X16 (le_refl p) hε).1 + restval = X.1.1 := by
    rw [hX16val]
    exact Mix2LambdaSection17.double_single_pair_add_rest
      hdouble hsingle hne
  refine ⟨⟨(Y16 (le_refl p) hε).1 + restval,
      add_mem (Y16 (le_refl p) hε).2 rest_mem⟩, ?_, ?_⟩
  · exact (Subtype.ext hXeq :
      (X16 (le_refl p) hε : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
        Step.mk (X16 (le_refl p) hε) (Y16 (le_refl p) hε) rest
          (Primitive.type16 ε hε (le_refl p))
  · change (Y16 (le_refl p) hε).1 + restval ≤ Y.1.1
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp :
        signature (Chromosome.prime^[j] X.1.1) =
          signature (Chromosome.prime^[j] (X16 (le_refl p) hε).1) +
            signature (Chromosome.prime^[j] restval) := by
      conv_lhs => rw [← hXeq]
      rw [iterate_map_add, map_add]
    by_cases hj0 : j < 2 * p + 1
    · rw [type16_diagonal_signature_eq_before hj0, ← hdecomp]
      exact le_iff_dominates.mp hXY.le j
    · by_cases hj1 : j = 2 * p + 1
      · subst j
        rw [type16_diagonal_signature_at_rank]
        rw [type16_diagonal_source_at_rank, zero_add] at hdecomp
        rw [← hdecomp]
        exact hgap_rank
      · by_cases hj2 : j = 2 * p + 2
        · subst j
          rw [type16_diagonal_signature_at_succ]
          rw [type16_diagonal_source_at_succ, zero_add] at hdecomp
          rw [← hdecomp]
          exact hgap_succ
        · have hj_after : 2 * p + 2 < j := by omega
          rw [type16_diagonal_signature_eq_after hj_after, ← hdecomp]
          exact le_iff_dominates.mp hXY.le j

/-- The diagonal type16 step with the rank gap discharged from the §17 reduced
hypotheses; only the successor-level sign-specific gap remains as input. -/
lemma exists_mutation_le_type16_diagonal_of_succ_gap
    {N p : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gdouble gsingle : Gene)
    (hdouble_type : gdouble.type = ε)
    (hsingle_type : gsingle.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * p + 1)
    (hrank : gdouble.rank = gsingle.rank)
    (hdouble : 2 ≤ X.1.1 gdouble) (hsingle : 1 ≤ X.1.1 gsingle)
    (hgap_succ :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * p + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * p + 2] Y.1.1)) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_type16_diagonal hε X Y hXY
    gdouble gsingle hdouble_type hsingle_type hdouble_rank hrank
    hdouble hsingle
  · exact type16_diagonal_gap_rank hε X Y hXY hcommon h17_1
      gdouble gsingle hdouble_type hsingle_type hdouble_rank hrank
      hdouble hsingle
  · exact hgap_succ

/-- The positive repeated-sign diagonal type16 branch, reduced to the strict
first-component successor gap. -/
lemma exists_mutation_le_type16_diagonal_positive_of_fst_lt
    {N p : ℕ}
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgpos_rank : gpos.rank = 2 * p + 1)
    (hrank : gpos.rank = gneg.rank)
    (hpos : 2 ≤ X.1.1 gpos) (hneg : 1 ≤ X.1.1 gneg)
    (hfst :
      (signature (Chromosome.prime^[2 * p + 2] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_type16_diagonal_of_succ_gap
    (ε := GeneType.Positive) (by decide) X Y hXY hcommon h17_1
    gpos gneg hgpos
  · simpa using hgneg
  · exact hgpos_rank
  · exact hrank
  · exact hpos
  · exact hneg
  · exact type16_succ_gap_positive X Y hXY hfst

/-- The negative repeated-sign diagonal type16 branch, reduced to the strict
second-component successor gap. -/
lemma exists_mutation_le_type16_diagonal_negative_of_snd_lt
    {N p : ℕ}
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gpos gneg : Gene)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hneg_rank : gneg.rank = 2 * p + 1)
    (hrank : gpos.rank = gneg.rank)
    (hpos : 1 ≤ X.1.1 gpos) (hneg : 2 ≤ X.1.1 gneg)
    (hsnd :
      (signature (Chromosome.prime^[2 * p + 2] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * p + 2] Y.1.1)).2) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_type16_diagonal_of_succ_gap
    (ε := GeneType.Negative) (by decide) X Y hXY hcommon h17_1
    gneg gpos hgneg
  · simpa using hgpos
  · exact hneg_rank
  · exact hrank.symm
  · exact hneg
  · exact hpos
  · exact type16_succ_gap_negative X Y hXY hsnd

end Mix2LambdaPi
