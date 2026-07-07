import YoungDiagram.Theorem6.Mix2LambdaPi.Case34PairFinallyOne
import YoungDiagram.Theorem6.Mix2LambdaPi.Type12
import YoungDiagram.Theorem6.Mix2LambdaPi.Type16

/-!
# §17 "Finally m = 1" pair case: triple (type12) boundary move

This file packages the `X ⊅ g⁻(k)` branch of Djoković's §17 "Finally m = 1"
rank-one pair case.  Here `X` carries the rank-one pair `g⁺(1) + g⁻(1)` together
with the minimal rank-`k` polarized gene `gᵉ(k)` (`k = 2n+1`, odd, `≥ 3`) but
*not* its opposite-sign partner `g⁻ᵉ(k)`.  The three-gene type12 move

  `g⁺(1) + g⁻(1) + gᵉ(k) → gᵉ(k+2)`   (for `ε = +`; symmetric for `ε = -`)

is dominated by `Y`: on the middle window `1 ≤ j ≤ k` the type12 target exceeds
the source by `(1,1)` (from `pair_finally_gap`); at the successor level `k+1` the
target adds `sig(ofRank 1 ε)`, which is supplied by a charge-edge argument at the
even boundary level (the same `D-2` drop bookkeeping as in `Case34SecondDouble`,
but removing the rank-one pair rather than a single doubled gene).
-/

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise
open Mix2LambdaSection17

namespace Mix2LambdaPi

variable {N : ℕ}

/-- Total multiplicity of `prime^[2n-1] X` equals `D - 2` for the rank-one pair
configuration: the two rank-one genes are annihilated by level `2n-1 ≥ 1`, and
all surviving genes (of rank `≥ k = 2n+1 > 2n-1`) keep their full multiplicity. -/
private lemma pair_totalMult_pred {n : ℕ} (X : nMix2LambdaPi N) (hn : 1 ≤ n)
    {gpos gneg : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1) (hne : gpos ≠ gneg)
    (hpos1 : X.1.1 gpos = 1) (hneg1 : X.1.1 gneg = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support,
      2 * n + 1 ≤ g.rank) :
    (Chromosome.prime^[2 * n - 1] X.1.1).sum (fun _ m => (m : ℚ)) =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
  have hgneg_rest_one :
      (X.1.1 - Finsupp.single gpos 1 : Chromosome) gneg = 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, hneg1]; rfl
  have hprime_eq :
      Chromosome.prime^[2 * n - 1] X.1.1 =
        Chromosome.prime^[2 * n - 1]
          (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1) := by
    rw [prime_iterate_eq_sub_single_of_rank_le hpos1 (by rw [hgpos1]; omega),
      prime_iterate_eq_sub_single_of_rank_le hgneg_rest_one (by rw [hgneg1]; omega)]
  have htot_nat :
      (Chromosome.prime^[2 * n - 1] X.1.1).sum (fun _ m => m) + 2 =
        X.1.1.sum (fun _ m => m) := by
    rw [hprime_eq,
      Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
        (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1) (2 * n - 1)
        (by intro g hg; have := h2nd g hg; omega)]
    exact totalMult_sub_two_single_one hpos1 hgneg_rest_one
  rw [← totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1]
  exact totalMult_cast_eq_sub_two_of_nat_add_two htot_nat

/-- §17 "Finally m = 1" triple boundary: given the rank-one pair
`g⁺(1) + g⁻(1)` (both of multiplicity one), the minimal rank-`k` polarized gene
`gᵉ(k)` (`k = 2n+1`, `n ≥ 1`), the level-one seed strictness, the value-`(1,1)`
window gap on `1 ≤ j ≤ k`, the residue-rank bound, and that every rank-`k` gene
of `X` has sign `ε`, the type12 move reduces `X` below `Y`. -/
lemma exists_mutation_le_pair_finally_triple {n : ℕ} {ε : GeneType}
    (hε : ε ≠ .NonPolarized) (X Y : nMix2LambdaPi N)
    (hXY : X.1 < Y.1) (hn : 1 ≤ n)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gpos gneg gk : Gene}
    (hgpos1 : gpos.rank = 1) (hgneg1 : gneg.rank = 1)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgk_rank : gk.rank = 2 * n + 1) (hgk : gk.type = ε)
    (hpos1 : X.1.1 gpos = 1) (hneg1 : X.1.1 gneg = 1) (hk1 : 1 ≤ X.1.1 gk)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1).support,
      2 * n + 1 ≤ g.rank)
    (hlow : ∀ g : Gene, 0 < X.1.1 g → g.rank = 2 * n + 1 → g.type = ε)
    (hgap : ∀ j, 0 < j → j ≤ 2 * n + 1 →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1)) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne_pos_neg : gpos ≠ gneg := fun h => by
    have := congrArg Gene.type h; rw [hgpos, hgneg] at this; exact absurd this (by decide)
  have hne_pos_k : gpos ≠ gk := fun h => by
    have := congrArg Gene.rank h; rw [hgpos1, hgk_rank] at this; omega
  have hne_neg_k : gneg ≠ gk := fun h => by
    have := congrArg Gene.rank h; rw [hgneg1, hgk_rank] at this; omega
  have hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank := by
    have hx := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
    have hy := @signature_sum_eq_rank (Chromosome.prime^[1] Y.1.1)
    have : ((Chromosome.prime^[1] X.1.1).rank : ℚ) <
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
      rw [← hx, ← hy]; linarith [hseed1.1, hseed1.2]
    exact_mod_cast this
  -- Total multiplicity of the predecessor iterate.
  have htotQ := pair_totalMult_pred X hn hgpos1 hgneg1 hne_pos_neg hpos1 hneg1 h2nd
  -- Strict `(1,1)` gap at the even predecessor level `2n = k-1`.
  have hpred_gap := hgap (2 * n) (by omega) (by omega)
  -- The middle-window gap in the type12 shape.
  have hgap_mid : ∀ j, 2 * 0 < j → j ≤ 2 * n + 1 →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi; exact hgap j (by omega) hjhi
  -- The successor gap at level `2n+2 = k+1`.
  have hgap_succ :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[2 * n + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * n + 2] Y.1.1) := by
    cases htype : ε with
    | NonPolarized => exact absurd htype hε
    | Positive =>
        subst htype
        -- Charge-edge X-drop bookkeeping: every gene of the predecessor iterate
        -- has rank `≥ 2`, and the rank-`2` ones are positive.
        have hW : ∀ z ∈ (Chromosome.prime^[2 * n - 1] X.1.1).support,
            2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
          intro z hz
          have hzpos : 0 < (Chromosome.prime^[2 * n - 1] X.1.1) z :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
          let z0 : Gene :=
            ⟨z.rank + (2 * n - 1), z.type, Nat.le_add_right_of_le z.rank_pos⟩
          have hz0X : 0 < X.1.1 z0 := by
            have hcoeff := prime_iterate_coeff (2 * n - 1) X.1.1 z
            change (Chromosome.prime^[2 * n - 1] X.1.1) z = X.1.1 z0 at hcoeff
            rwa [← hcoeff]
          have hz0_ne_pos : z0 ≠ gpos := fun h => by
            have hr : z0.rank = 1 := by rw [h, hgpos1]
            have : z0.rank = z.rank + (2 * n - 1) := rfl
            have := z.rank_pos; omega
          have hz0_ne_neg : z0 ≠ gneg := fun h => by
            have hr : z0.rank = 1 := by rw [h, hgneg1]
            have : z0.rank = z.rank + (2 * n - 1) := rfl
            have := z.rank_pos; omega
          have hz0_rest :
              0 < (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1 :
                Chromosome) z0 := by
            rw [Finsupp.tsub_apply, Finsupp.tsub_apply,
              Finsupp.single_apply, Finsupp.single_apply,
              if_neg (Ne.symm hz0_ne_pos), if_neg (Ne.symm hz0_ne_neg)]
            omega
          have hz0_rank_ge := h2nd z0
            (Finsupp.mem_support_iff.mpr (ne_of_gt hz0_rest))
          have hz0r : 2 * n + 1 ≤ z.rank + (2 * n - 1) := hz0_rank_ge
          refine ⟨by omega, ?_⟩
          intro hz_rank
          have hz0_rank_eq : z0.rank = 2 * n + 1 := by
            have : z0.rank = z.rank + (2 * n - 1) := rfl; omega
          have := hlow z0 hz0X hz0_rank_eq
          exact this
        have hXdrop_raw :=
          edge_drop_fst_eq_totalMult_positive_iterate (W := X.1.1)
            (i := 2 * n - 1) hW
        have hXdrop :
            (Sigma.sigma X.1.1 (2 * n)).1 - (Sigma.sigma X.1.1 (2 * n + 2)).1 =
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
          rw [show (1 : ℕ) + (2 * n - 1) = 2 * n by omega,
            show (3 : ℕ) + (2 * n - 1) = 2 * n + 2 by omega] at hXdrop_raw
          rw [hXdrop_raw, htotQ]
        have hYdrop := case4_Ydrop_fst_strong_even (i := 2 * n) X Y hseed1
          ⟨n, by ring⟩
        have hfst_succ :
            (signature (Chromosome.prime^[2 * n + 2] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * n + 2] Y.1.1)).1 := by
          have hpred_fst : (signature (Chromosome.prime^[2 * n] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * n] Y.1.1)).1 := by
            have := hpred_gap.1
            simp only [Prod.fst_add, Prod.fst_one] at this; linarith
          simp only [Sigma.sigma] at hXdrop hYdrop hpred_fst ⊢
          linarith
        simpa [signature_ofRank_one_positive] using
          type16_succ_gap_positive X Y hXY (p := n) hfst_succ
    | Negative =>
        subst htype
        have hW : ∀ z ∈ (Chromosome.prime^[2 * n - 1] X.1.1).support,
            2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
          intro z hz
          have hzpos : 0 < (Chromosome.prime^[2 * n - 1] X.1.1) z :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
          let z0 : Gene :=
            ⟨z.rank + (2 * n - 1), z.type, Nat.le_add_right_of_le z.rank_pos⟩
          have hz0X : 0 < X.1.1 z0 := by
            have hcoeff := prime_iterate_coeff (2 * n - 1) X.1.1 z
            change (Chromosome.prime^[2 * n - 1] X.1.1) z = X.1.1 z0 at hcoeff
            rwa [← hcoeff]
          have hz0_ne_pos : z0 ≠ gpos := fun h => by
            have hr : z0.rank = 1 := by rw [h, hgpos1]
            have : z0.rank = z.rank + (2 * n - 1) := rfl
            have := z.rank_pos; omega
          have hz0_ne_neg : z0 ≠ gneg := fun h => by
            have hr : z0.rank = 1 := by rw [h, hgneg1]
            have : z0.rank = z.rank + (2 * n - 1) := rfl
            have := z.rank_pos; omega
          have hz0_rest :
              0 < (X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1 :
                Chromosome) z0 := by
            rw [Finsupp.tsub_apply, Finsupp.tsub_apply,
              Finsupp.single_apply, Finsupp.single_apply,
              if_neg (Ne.symm hz0_ne_pos), if_neg (Ne.symm hz0_ne_neg)]
            omega
          have hz0_rank_ge := h2nd z0
            (Finsupp.mem_support_iff.mpr (ne_of_gt hz0_rest))
          have hz0r : 2 * n + 1 ≤ z.rank + (2 * n - 1) := hz0_rank_ge
          refine ⟨by omega, ?_⟩
          intro hz_rank
          have hz0_rank_eq : z0.rank = 2 * n + 1 := by
            have : z0.rank = z.rank + (2 * n - 1) := rfl; omega
          have := hlow z0 hz0X hz0_rank_eq
          exact this
        have hXdrop_raw :=
          edge_drop_snd_eq_totalMult_negative_iterate (W := X.1.1)
            (i := 2 * n - 1) hW
        have hXdrop :
            (Sigma.sigma X.1.1 (2 * n)).2 - (Sigma.sigma X.1.1 (2 * n + 2)).2 =
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
          rw [show (1 : ℕ) + (2 * n - 1) = 2 * n by omega,
            show (3 : ℕ) + (2 * n - 1) = 2 * n + 2 by omega] at hXdrop_raw
          rw [hXdrop_raw, htotQ]
        have hYdrop := case4_Ydrop_snd_strong_even (i := 2 * n) X Y hseed1
          ⟨n, by ring⟩
        have hsnd_succ :
            (signature (Chromosome.prime^[2 * n + 2] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * n + 2] Y.1.1)).2 := by
          have hpred_snd : (signature (Chromosome.prime^[2 * n] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * n] Y.1.1)).2 := by
            have := hpred_gap.2
            simp only [Prod.snd_add, Prod.snd_one] at this; linarith
          simp only [Sigma.sigma] at hXdrop hYdrop hpred_snd ⊢
          linarith
        simpa [signature_ofRank_one_negative] using
          type16_succ_gap_negative X Y hXY (p := n) hsnd_succ
  exact exists_mutation_le_type12 hε (Nat.zero_le n) X Y hXY gpos gneg gk
    hgpos hgneg hgk (by omega) (by rw [hgpos1, hgneg1]) hgk_rank
    (by omega) (by omega) (by omega) hne_pos_k hne_neg_k hgap_mid hgap_succ

end Mix2LambdaPi
