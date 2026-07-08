import YoungDiagram.Theorem6.MixPi2Lambda.Type13
import YoungDiagram.Mutations.MixPi2Lambda.type16

/-!
# Label 4 type16 mutation wrappers (mirror of `Mix2LambdaPi.Type16`)

Parity flip: `2g^ε(2m+2)+g^{-ε}(2n+2) → 2NP(2m+1)+g^ε(2n+4)`.  Only the general
Step constructors are ported here (clean rank-substituted mirror); the boundary
window-signature lemmas are added by the §17 L4 case files with the correct
`a_i=b_i for i even` parity.
-/

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-- General type16 Step constructor. -/
lemma exists_mutation_le_type16_of_decomp
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMixPi2Lambda N) (restval : Chromosome)
    (hXeq : (X16 h_le hε).1 + restval = X.1.1)
    (hrest : restval ∈ Mix (Pi, 2 • Lambda))
    (hZle : (Y16 h_le hε).1 + restval ≤ Y.1.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let rest : Mix (Pi, 2 • Lambda) := ⟨restval, hrest⟩
  refine ⟨⟨(Y16 h_le hε).1 + restval,
      add_mem (Y16 h_le hε).2 hrest⟩, ?_, hZle⟩
  exact (Subtype.ext hXeq :
      (X16 h_le hε : Mix (Pi, 2 • Lambda)) + rest = X.1) ▸
    Step.mk (X16 h_le hε) (Y16 h_le hε) rest
      (Primitive.type16 ε hε h_le)

/-- Concrete-gene wrapper for general type16: source
`2g^ε(2m+2)+g^{-ε}(2n+2)+rest`; caller supplies the dominance bound. -/
lemma exists_mutation_le_type16_of_genes
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMixPi2Lambda N)
    (gdouble gsingle : Gene)
    (hdouble_type : gdouble.type = ε)
    (hsingle_type : gsingle.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * m + 2)
    (hsingle_rank : gsingle.rank = 2 * n + 2)
    (hdouble : 2 ≤ X.1.1 gdouble) (hsingle : 1 ≤ X.1.1 gsingle)
    (hne : gdouble ≠ gsingle)
    (hZle :
      (Y16 h_le hε).1 +
          (X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
            Finsupp.single gsingle 1) ≤ Y.1.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gdouble 1 - Finsupp.single gdouble 1 -
      Finsupp.single gsingle 1
  have hevendouble : Even gdouble.rank := by rw [hdouble_rank]; exact ⟨m + 1, by ring⟩
  have hevensingle : Even gsingle.rank := by rw [hsingle_rank]; exact ⟨n + 1, by ring⟩
  have rest_mem : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda
        (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 hevendouble) hevendouble)
      hevensingle
  have hgdouble_eq :
      Gene.ofRank (2 * m + 2) ε =
        (Finsupp.single gdouble 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gdouble)
    rwa [hdouble_rank, hdouble_type] at h
  have hgsingle_eq :
      Gene.ofRank (2 * n + 2) (-ε) =
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
    exact Mix2LambdaSection17.double_single_pair_add_rest hdouble hsingle hne
  exact exists_mutation_le_type16_of_decomp hε h_le X Y restval hXeq
    rest_mem hZle

/-! ### Window signature lemmas for the diagonal (`m = n = p`) type16 move.

Parity vs L3: polarized genes sit at even rank `2p+2`, the created nonpolarized
pair at `2p+1`, the raised `ε` gene at `2p+4`.  The "rank" (created-pair) level is
`2p+2` (even → integer signature in `Mix (Pi, 2Λ)`), and the successor level is
`2p+3` (odd → integer signature in `Mix (2Λ, Π)`). -/

private lemma type16_diagonal_signature_eq_before
    {p j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hj : j < 2 * p + 2) :
    signature (Chromosome.prime^[j] (Y16 (le_refl p) hε).1) =
      signature (Chromosome.prime^[j] (X16 (le_refl p) hε).1) := by
  by_cases hjle : j ≤ 2 * p
  · simp only [X16_eq, Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
    have h := mutation_type16_sig_eq_aux (n := p) (m := p) (ε := ε)
      ((2 * p - j) / 2) ((2 * p - j) % 2)
    have eq1 :
        2 * ((2 * p - j) / 2) + 2 + (2 * p - j) % 2 =
          2 * p + 2 - j := by omega
    have eq2 :
        2 * (((2 * p - j) / 2) + (p - p)) + 2 + (2 * p - j) % 2 =
          2 * p + 2 - j := by omega
    have eq3 :
        2 * ((2 * p - j) / 2) + 1 + (2 * p - j) % 2 =
          2 * p + 1 - j := by omega
    have eq4 :
        2 * (((2 * p - j) / 2) + (p - p)) + 4 + (2 * p - j) % 2 =
          2 * p + 4 - j := by omega
    rw [eq1, eq2, eq3, eq4] at h
    exact h.symm
  · -- boundary `j = 2p+1`: polarized genes drop to rank 1, NP genes vanish.
    have hj1 : j = 2 * p + 1 := by omega
    subst hj1
    simp only [X16_eq, Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
    have h0 : 2 * p + 1 - (2 * p + 1) = 0 := by omega
    have h1 : 2 * p + 2 - (2 * p + 1) = 1 := by omega
    have h3 : 2 * p + 4 - (2 * p + 1) = 3 := by omega
    rw [h0, h1, h3, Gene.ofRank_zero, map_zero, zero_add,
      signature_ofRank_eq₂' 1]
    have hone : (2 : ℕ) - 1 = 1 := rfl
    -- `2·sig(ofRank 1 ε)+sig(ofRank 1 (-ε)) = sig(ofRank 1 ε)+sig(ofRank 3 ε)`.
    have hpn := signature_sum_ofRank_neg_eq_rank (k := 1) (ε := ε)
    cases ε with
    | NonPolarized => exact absurd rfl hε
    | Positive =>
        simp only [GeneType.neg_positive, signature_ofRank_one_positive,
          signature_ofRank_one_negative]
        norm_num
    | Negative =>
        simp only [GeneType.neg_negative, signature_ofRank_one_positive,
          signature_ofRank_one_negative]
        norm_num

private lemma type16_diagonal_signature_at_rank
    {p : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * p + 2] (Y16 (le_refl p) hε).1) =
      ((1 : ℚ), (1 : ℚ)) := by
  simp only [Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h0 : 2 * p + 1 - (2 * p + 2) = 0 := by omega
  have h2 : 2 * p + 4 - (2 * p + 2) = 2 := by omega
  rw [h0, h2, Gene.ofRank_zero, map_zero, zero_add,
    signature_ofRank_eq₂']
  simp

private lemma type16_diagonal_source_at_rank
    {p : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * p + 2] (X16 (le_refl p) hε).1) = 0 := by
  simp [X16_eq, prime_iterate_ofRank]

private lemma type16_diagonal_signature_at_succ
    {p : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * p + 3] (Y16 (le_refl p) hε).1) =
      signature (Gene.ofRank 1 ε) := by
  simp only [Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h0 : 2 * p + 1 - (2 * p + 3) = 0 := by omega
  have h1 : 2 * p + 4 - (2 * p + 3) = 1 := by omega
  simp [h0, h1]

private lemma type16_diagonal_source_at_succ
    {p : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} :
    signature (Chromosome.prime^[2 * p + 3] (X16 (le_refl p) hε).1) = 0 := by
  simp [X16_eq, prime_iterate_ofRank]

private lemma type16_diagonal_signature_eq_after
    {p j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hj : 2 * p + 3 < j) :
    signature (Chromosome.prime^[j] (Y16 (le_refl p) hε).1) =
      signature (Chromosome.prime^[j] (X16 (le_refl p) hε).1) := by
  simp only [X16_eq, Y16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h0 : 2 * p + 1 - j = 0 := by omega
  have h1 : 2 * p + 2 - j = 0 := by omega
  have h3 : 2 * p + 4 - j = 0 := by omega
  simp [h0, h1, h3]

/-- At the successor (odd) level `2p+3` of a positive type16 move, a strict
first-component gap gives exactly the `signature (ofRank 1 Positive)` gap. -/
lemma type16_succ_gap_positive
    {N p : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hfst :
      (signature (Chromosome.prime^[2 * p + 3] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).1) :
    signature (Gene.ofRank 1 .Positive) +
        signature (Chromosome.prime^[2 * p + 3] X.1.1) ≤
      signature (Chromosome.prime^[2 * p + 3] Y.1.1) := by
  have hXk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 (2 * p + 3)
  have hYk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 (2 * p + 3)
  have hodd : ¬ Even (2 * p + 3) := Nat.not_even_iff_odd.mpr ⟨p + 1, by ring⟩
  rw [if_neg hodd] at hXk_mem hYk_mem
  have hfst_gap :=
    Mix2LambdaSection17.add_one_le_fst_of_lt_Mix_2Lambda_Pi
      hXk_mem hYk_mem hfst
  have hle := le_iff_dominates.mp hXY.le (2 * p + 3)
  rw [signature_ofRank_one_positive]
  exact ⟨by simpa [Prod.fst_add, add_comm] using hfst_gap, by simpa using hle.2⟩

/-- At the successor (odd) level `2p+3` of a negative type16 move, a strict
second-component gap gives exactly the `signature (ofRank 1 Negative)` gap. -/
lemma type16_succ_gap_negative
    {N p : ℕ} (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hsnd :
      (signature (Chromosome.prime^[2 * p + 3] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * p + 3] Y.1.1)).2) :
    signature (Gene.ofRank 1 .Negative) +
        signature (Chromosome.prime^[2 * p + 3] X.1.1) ≤
      signature (Chromosome.prime^[2 * p + 3] Y.1.1) := by
  have hXk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 (2 * p + 3)
  have hYk_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 (2 * p + 3)
  have hodd : ¬ Even (2 * p + 3) := Nat.not_even_iff_odd.mpr ⟨p + 1, by ring⟩
  rw [if_neg hodd] at hXk_mem hYk_mem
  have hsnd_gap :=
    Mix2LambdaSection17.add_one_le_snd_of_lt_Mix_2Lambda_Pi
      hXk_mem hYk_mem hsnd
  have hle := le_iff_dominates.mp hXY.le (2 * p + 3)
  rw [signature_ofRank_one_negative]
  exact ⟨by simpa using hle.1, by simpa [Prod.snd_add, add_comm] using hsnd_gap⟩

/-- The diagonal type16 step for a `2+1` pair, assuming the two precise sigma
gaps where the target exceeds the source. -/
lemma exists_mutation_le_type16_diagonal
    {N p : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (gdouble gsingle : Gene)
    (hdouble_type : gdouble.type = ε)
    (hsingle_type : gsingle.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * p + 2)
    (hrank : gdouble.rank = gsingle.rank)
    (hdouble : 2 ≤ X.1.1 gdouble) (hsingle : 1 ≤ X.1.1 gsingle)
    (hgap_rank :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * p + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * p + 2] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * p + 3] X.1.1) ≤
        signature (Chromosome.prime^[2 * p + 3] Y.1.1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
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
  have hevendouble : Even gdouble.rank := by rw [hdouble_rank]; exact ⟨p + 1, by ring⟩
  have hevensingle : Even gsingle.rank := hrank ▸ hevendouble
  have rest_mem : restval ∈ Mix (Pi, 2 • Lambda) :=
    sub_single_one_mem_Mix_Pi_2Lambda
      (sub_single_one_mem_Mix_Pi_2Lambda
        (sub_single_one_mem_Mix_Pi_2Lambda X.1.2 hevendouble) hevendouble)
      hevensingle
  let rest : Mix (Pi, 2 • Lambda) := ⟨restval, rest_mem⟩
  have hgdouble_eq :
      Gene.ofRank (2 * p + 2) ε =
        (Finsupp.single gdouble 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gdouble)
    rwa [hdouble_rank, hdouble_type] at h
  have hgsingle_eq :
      Gene.ofRank (2 * p + 2) (-ε) =
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
      (X16 (le_refl p) hε : Mix (Pi, 2 • Lambda)) + rest = X.1) ▸
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
    by_cases hj0 : j < 2 * p + 2
    · rw [type16_diagonal_signature_eq_before hj0, ← hdecomp]
      exact le_iff_dominates.mp hXY.le j
    · by_cases hj1 : j = 2 * p + 2
      · subst j
        rw [type16_diagonal_signature_at_rank]
        rw [type16_diagonal_source_at_rank, zero_add] at hdecomp
        rw [← hdecomp]
        exact hgap_rank
      · by_cases hj2 : j = 2 * p + 3
        · subst j
          rw [type16_diagonal_signature_at_succ]
          rw [type16_diagonal_source_at_succ, zero_add] at hdecomp
          rw [← hdecomp]
          exact hgap_succ
        · have hj_after : 2 * p + 3 < j := by omega
          rw [type16_diagonal_signature_eq_after hj_after, ← hdecomp]
          exact le_iff_dominates.mp hXY.le j

/-- In the diagonal type16 `2+1` situation (L4 parity), the even rank `2p+2`
where the two lower nonpolarized genes are created has the `(1,1)` gap. -/
lemma type16_diagonal_gap_rank
    {N p : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (gdouble gsingle : Gene)
    (hdouble_type : gdouble.type = ε)
    (hsingle_type : gsingle.type = -ε)
    (hdouble_rank : gdouble.rank = 2 * p + 2)
    (hrank : gdouble.rank = gsingle.rank)
    (hdouble : 2 ≤ X.1.1 gdouble) (hsingle : 1 ≤ X.1.1 gsingle) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * p + 2] X.1.1) ≤
      signature (Chromosome.prime^[2 * p + 2] Y.1.1) := by
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
      Gene.ofRank (2 * p + 2) ε =
        (Finsupp.single gdouble 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gdouble)
    rwa [hdouble_rank, hdouble_type] at h
  have hgsingle_eq :
      Gene.ofRank (2 * p + 2) (-ε) =
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
  have hY_no_gene : ∀ g : Gene, g.rank = 2 * p + 2 → Y.1.1 g = 0 := by
    intro g hgr
    by_contra hzero
    have hgY : 0 < Y.1.1 g := Nat.pos_of_ne_zero hzero
    have hpol : g.type ≠ .NonPolarized := by
      have hgeven : Even g.rank := by rw [hgr]; exact ⟨p + 1, by ring⟩
      have : 0 < Y.1.1.evenPart g := by
        rw [evenPart_eq, Finsupp.filter_apply, if_pos hgeven]
        exact hgY
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.1) g
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
  have hYr_pred : Chromosome.prime^[2 * p + 1] Y.1.1 ≠ 0 := by
    intro hzero
    have hdom := le_iff_dominates.mp hXY.le (2 * p + 1)
    have hsource :
        ((1 : ℚ), (1 : ℚ)) ≤
          signature (Chromosome.prime^[2 * p + 1] X.1.1) := by
      have hdecomp :
          signature (Chromosome.prime^[2 * p + 1] X.1.1) =
            signature (Chromosome.prime^[2 * p + 1] (X16 (le_refl p) hε).1) +
              signature (Chromosome.prime^[2 * p + 1] restval) := by
        conv_lhs => rw [← hXeq]
        rw [iterate_map_add, map_add]
      have hsrc :
          ((1 : ℚ), (1 : ℚ)) ≤
            signature (Chromosome.prime^[2 * p + 1] (X16 (le_refl p) hε).1) := by
        simp only [X16_eq, iterate_map_add, prime_iterate_ofRank, map_add]
        have hone : 2 * p + 2 - (2 * p + 1) = 1 := by omega
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
  have hYr : Chromosome.prime^[2 * p + 2] Y.1.1 ≠ 0 :=
    Mix2LambdaSection17.prime_iterate_ne_zero_of_no_gene (by omega)
      hY_no_gene (by simpa only [show 2 * p + 2 - 1 = 2 * p + 1 by omega]
        using hYr_pred)
  have hle_r := le_iff_dominates.mp hXY.le (2 * p + 2)
  have hne_r :
      signature (Chromosome.prime^[2 * p + 2] X.1.1) ≠
        signature (Chromosome.prime^[2 * p + 2] Y.1.1) := by
    intro heq
    have hrank_lt := h17_1 (2 * p + 2) (by omega) hYr
    have := congr_arg (fun q : ℚ × ℚ => q.1 + q.2) heq
    simp only [signature_sum_eq_rank] at this
    exact (ne_of_lt hrank_lt) (by exact_mod_cast this)
  have hXr_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 (2 * p + 2)
  have hYr_mem := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 (2 * p + 2)
  have heven : Even (2 * p + 2) := ⟨p + 1, by ring⟩
  rw [if_pos heven] at hXr_mem hYr_mem
  exact Mix2LambdaSection17.one_pair_add_le_of_lt_Mix_Pi_2Lambda
    hXr_mem hYr_mem hle_r hne_r

end MixPi2Lambda
