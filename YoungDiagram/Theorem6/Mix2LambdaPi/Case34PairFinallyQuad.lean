import YoungDiagram.Theorem6.Mix2LambdaPi.Case34PairFinallyOne
import YoungDiagram.Theorem6.Mix2LambdaPi.Type13

/-!
# §17 "Finally m = 1" pair case: quadruple (type13) boundary move

This file packages the `X ⊃ g⁻(k)` branch of Djoković's §17 "Finally m = 1"
rank-one pair case.  Here `X` carries the rank-one pair `g⁺(1) + g⁻(1)` together
with *both* rank-`k` polarized genes `g⁺(k)` and `g⁻(k)` (`k = 2n+1`, odd, `≥ 3`).
The four-gene off-diagonal type13 move

  `g⁺(1) + g⁻(1) + g⁺(k) + g⁻(k) → 2 g(k+1)`

is dominated by `Y`: on the middle window `1 ≤ j ≤ k` the type13 target exceeds
the source by exactly `(1,1)`, which is supplied by `pair_finally_gap`; at the
levels `j = 0` and `j > k` source and target agree and dominance follows from
`X ≤ Y`.
-/

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

variable {N : ℕ}

/-- Four-gene single decomposition (all four genes pairwise distinct, each
present at least once). -/
private lemma single_quad_add_rest {X : Chromosome} {g h k l : Gene}
    (hg : 1 ≤ X g) (hh : 1 ≤ X h) (hk : 1 ≤ X k) (hl : 1 ≤ X l)
    (hgh : g ≠ h) (hgk : g ≠ k) (hgl : g ≠ l)
    (hhk : h ≠ k) (hhl : h ≠ l) (hkl : k ≠ l) :
    Finsupp.single g 1 + Finsupp.single h 1 + Finsupp.single k 1 +
        Finsupp.single l 1 +
      (X - Finsupp.single g 1 - Finsupp.single h 1 - Finsupp.single k 1 -
        Finsupp.single l 1) = X := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hxg : g = x
  · subst hxg; simp [hgh.symm, hgk.symm, hgl.symm]; omega
  · by_cases hxh : h = x
    · subst hxh; simp [hgh, hhk.symm, hhl.symm]; omega
    · by_cases hxk : k = x
      · subst hxk; simp [hgk, hhk, hkl.symm]; omega
      · by_cases hxl : l = x
        · subst hxl; simp [hgl, hhl, hkl]; omega
        · simp [hxg, hxh, hxk, hxl]

/-- Signature of the `m = 0` type13 source at any level: the rank-one pair
vanishes for `j ≥ 1`, leaving the rank-`2n+1` polarized pair, whose signature
sums to `(2n+1-j, 2n+1-j)`. -/
private lemma type13_zero_X_sig {n j : ℕ} (hj : 0 < j) :
    signature (Chromosome.prime^[j] (X13 (Nat.zero_le n)).1) =
      (((2 * n + 1 - j : ℕ) : ℚ), ((2 * n + 1 - j : ℕ) : ℚ)) := by
  simp only [X13_eq, iterate_map_add, prime_iterate_ofRank, map_add,
    show 2 * 0 + 1 - j = 0 by omega, Gene.ofRank_zero, zero_add]
  have hP := signature_sum_ofRank_neg_eq_rank (k := 2 * n + 1 - j)
    (ε := GeneType.Positive)
  rw [GeneType.neg_positive] at hP
  rw [hP]; rfl

/-- Signature of the `m = 0` type13 target at any level `1 ≤ j`: the two rank-`0`
copies vanish, leaving two rank-`2n+2` nonpolarized copies with signature summing
to `(2n+2-j, 2n+2-j)`. -/
private lemma type13_zero_Y_sig {n j : ℕ} (hj : 0 < j) :
    signature (Chromosome.prime^[j] (Y13 (Nat.zero_le n)).1) =
      (((2 * n + 2 - j : ℕ) : ℚ), ((2 * n + 2 - j : ℕ) : ℚ)) := by
  simp only [Y13_eq, iterate_map_add, prime_iterate_ofRank, map_add,
    show 2 * 0 - j = 0 by omega, Gene.ofRank_zero,
    zero_add, signature_ofRank_nonPolarized, Prod.mk_add_mk]
  norm_num

/-- Level-`0` agreement of the `m = 0` type13 source and target signatures. -/
private lemma type13_zero_signature_at_zero {n : ℕ} :
    signature (Chromosome.prime^[0] (Y13 (Nat.zero_le n)).1) =
      signature (Chromosome.prime^[0] (X13 (Nat.zero_le n)).1) := by
  simp only [Function.iterate_zero, id_eq, X13_eq, Y13_eq]
  exact (mutation_type13_signature_eq (m := 0) (n := n)).symm

/-- Middle-window relation for the `m = 0` type13 move: for `1 ≤ j ≤ 2n+1` the
target exceeds the source by exactly `(1,1)`. -/
private lemma type13_zero_signature_mid {n j : ℕ} (hjlo : 0 < j)
    (hjhi : j ≤ 2 * n + 1) :
    signature (Chromosome.prime^[j] (Y13 (Nat.zero_le n)).1) =
      ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[j] (X13 (Nat.zero_le n)).1) := by
  rw [type13_zero_X_sig hjlo, type13_zero_Y_sig hjlo]
  ext <;>
    simp only [Prod.fst_add, Prod.snd_add] <;>
    rw [Nat.cast_sub (by omega : j ≤ 2 * n + 2),
      Nat.cast_sub (by omega : j ≤ 2 * n + 1)] <;>
    push_cast <;> ring

/-- After the window `j > 2n+1`, the `m = 0` type13 source and target agree. -/
private lemma type13_zero_signature_after {n j : ℕ} (hj : 2 * n + 1 < j) :
    signature (Chromosome.prime^[j] (Y13 (Nat.zero_le n)).1) =
      signature (Chromosome.prime^[j] (X13 (Nat.zero_le n)).1) := by
  simp only [X13_eq, Y13_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  rw [show 2 * 0 + 1 - j = 0 by omega, show 2 * 0 - j = 0 by omega,
    show 2 * n + 1 - j = 0 by omega, show 2 * n + 2 - j = 0 by omega]
  simp [Gene.ofRank_zero]

/-- §17 "Finally m = 1" quadruple boundary: given the rank-one pair
`g⁺(1) + g⁻(1)` (both of multiplicity one), both rank-`k` polarized genes
`g⁺(k), g⁻(k)` present (`k = 2n+1`, `n ≥ 1`), and the value-`(1,1)` window gap
on `1 ≤ j ≤ k`, the off-diagonal type13 move reduces `X` below `Y`. -/
lemma exists_mutation_le_pair_finally_quad {n : ℕ} (X Y : nMix2LambdaPi N)
    (hXY : X.1 < Y.1) (hn : 1 ≤ n)
    {gpos gneg gkp gkn : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgkp_rank : gkp.rank = 2 * n + 1) (hgkn_rank : gkn.rank = 2 * n + 1)
    (hgkp : gkp.type = .Positive) (hgkn : gkn.type = .Negative)
    (hpos1 : 1 ≤ X.1.1 gpos) (hneg1 : 1 ≤ X.1.1 gneg)
    (hkp1 : 1 ≤ X.1.1 gkp) (hkn1 : 1 ≤ X.1.1 gkn)
    (hgap : ∀ j, 0 < j → j ≤ 2 * n + 1 →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1)) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  -- Pairwise distinctness of the four genes.
  have hne_pos_neg : gpos ≠ gneg := fun h => by
    have := congrArg Gene.type h; rw [hgpos, hgneg] at this; exact absurd this (by decide)
  have hne_kp_kn : gkp ≠ gkn := fun h => by
    have := congrArg Gene.type h; rw [hgkp, hgkn] at this; exact absurd this (by decide)
  have hne_pos_kp : gpos ≠ gkp := fun h => by
    have := congrArg Gene.rank h; rw [hgpos1, hgkp_rank] at this; omega
  have hne_pos_kn : gpos ≠ gkn := fun h => by
    have := congrArg Gene.rank h; rw [hgpos1, hgkn_rank] at this; omega
  have hne_neg_kp : gneg ≠ gkp := fun h => by
    have := congrArg Gene.rank h; rw [hgneg1, hgkp_rank] at this; omega
  have hne_neg_kn : gneg ≠ gkn := fun h => by
    have := congrArg Gene.rank h; rw [hgneg1, hgkn_rank] at this; omega
  -- The residue `restval` and its membership.
  set restval : Chromosome :=
    X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1 -
      Finsupp.single gkp 1 - Finsupp.single gkn 1 with hrestval
  have hodd_gpos : Odd gpos.rank := by rw [hgpos1]; exact ⟨0, rfl⟩
  have hodd_gneg : Odd gneg.rank := by rw [hgneg1]; exact ⟨0, rfl⟩
  have hodd_gkp : Odd gkp.rank := by rw [hgkp_rank]; exact ⟨n, rfl⟩
  have hodd_gkn : Odd gkn.rank := by rw [hgkn_rank]; exact ⟨n, rfl⟩
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi
        (sub_single_one_mem_Mix_2Lambda_Pi
          (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hodd_gpos) hodd_gneg)
          hodd_gkp) hodd_gkn
  -- `X13` as an explicit sum of the four single genes.
  have hgpos_of :
      Gene.ofRank (2 * 0 + 1) GeneType.Positive =
        (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos); rw [hgpos1, hgpos] at h; exact h
  have hgneg_of :
      Gene.ofRank (2 * 0 + 1) GeneType.Negative =
        (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg); rw [hgneg1, hgneg] at h; exact h
  have hgkp_of :
      Gene.ofRank (2 * n + 1) GeneType.Positive =
        (Finsupp.single gkp 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gkp); rw [hgkp_rank, hgkp] at h; exact h
  have hgkn_of :
      Gene.ofRank (2 * n + 1) GeneType.Negative =
        (Finsupp.single gkn 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gkn); rw [hgkn_rank, hgkn] at h; exact h
  have hX13val :
      (X13 (Nat.zero_le n)).1 =
        Finsupp.single gpos 1 + Finsupp.single gneg 1 +
          Finsupp.single gkp 1 + Finsupp.single gkn 1 := by
    rw [X13_eq, hgpos_of, hgneg_of, hgkp_of, hgkn_of]
  have hXeq : (X13 (Nat.zero_le n)).1 + restval = X.1.1 := by
    rw [hX13val, hrestval]
    exact single_quad_add_rest hpos1 hneg1 hkp1 hkn1 hne_pos_neg hne_pos_kp
      hne_pos_kn hne_neg_kp hne_neg_kn hne_kp_kn
  -- Dominance of the type13 target plus residue.
  have hZle : (Y13 (Nat.zero_le n)).1 + restval ≤ Y.1.1 := by
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp :
        signature (Chromosome.prime^[j] X.1.1) =
          signature (Chromosome.prime^[j] (X13 (Nat.zero_le n)).1) +
            signature (Chromosome.prime^[j] restval) := by
      conv_lhs => rw [← hXeq]
      rw [iterate_map_add, map_add]
    by_cases hj0 : j = 0
    · subst hj0
      rw [type13_zero_signature_at_zero, ← hdecomp]
      exact le_iff_dominates.mp hXY.le 0
    · by_cases hjmid : j ≤ 2 * n + 1
      · rw [type13_zero_signature_mid (by omega) hjmid]
        calc
          ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] (X13 (Nat.zero_le n)).1) +
              signature (Chromosome.prime^[j] restval)
              = ((1 : ℚ), (1 : ℚ)) +
                (signature (Chromosome.prime^[j] (X13 (Nat.zero_le n)).1) +
                  signature (Chromosome.prime^[j] restval)) := by abel
          _ = ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[j] Y.1.1) := hgap j (by omega) hjmid
      · rw [type13_zero_signature_after (by omega), ← hdecomp]
        exact le_iff_dominates.mp hXY.le j
  exact exists_mutation_le_type13_of_decomp (Nat.zero_le n) X Y restval hXeq
    rest_mem hZle

end Mix2LambdaPi
