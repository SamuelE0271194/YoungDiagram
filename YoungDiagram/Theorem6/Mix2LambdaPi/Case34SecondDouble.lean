import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Seed
import YoungDiagram.Theorem6.Mix2LambdaPi.Type16
import YoungDiagram.Theorem6.Mix2LambdaPi.Type10

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

set_option maxHeartbeats 1000000 in
/-- §17 Case 4, the `k = t` subcase: the second gene `g₂` (rank `2q₂+3`) already
has multiplicity `≥ 2`, so the diagonal double mutation
`2g₂ → g₂^-(2q₂+1) + g₂^+(2q₂+5)` works.  The rank-one gene `g` stays in the rest.

The interior window strictness comes from `Case34Seed`; the mid/succ boundary
gaps mirror the §17 Case-1 (`RankGeThree`) argument, but with the drop lowered by
one because `g = g^±(1)` is annihilated by level `2q₂+1`. -/
lemma exists_mutation_le_second_double
    {m q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene)
    (hg_one : X.1.1 g = 1) (hg_rank_one : g.rank = 1)
    (hg₂min : ∀ g' : Gene,
      0 < (X.1.1 - Finsupp.single g 1 : Chromosome) g' → g₂.rank ≤ g'.rank)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hg₂_two : 2 ≤ X.1.1 g₂) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXg₂ : 0 < X.1.1 g₂ := by omega
  have h2nd : ∀ g' ∈ (X.1.1 - Finsupp.single g 1).support, 2 * q₂ + 3 ≤ g'.rank := by
    intro g' hg'
    have := hg₂min g' (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'))
    rwa [hg₂_rank_q] at this
  have hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank := by
    have hx := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
    have hy := @signature_sum_eq_rank (Chromosome.prime^[1] Y.1.1)
    have : ((Chromosome.prime^[1] X.1.1).rank : ℚ) <
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
      rw [← hx, ← hy]; linarith [hseed1.1, hseed1.2]
    exact_mod_cast this
  -- The exact `X` first/second drops at the boundary equal `D - 1`.
  have htot_nat :
      (Chromosome.prime^[2 * q₂ + 1] X.1.1).sum (fun _ n => n) + 1 =
        X.1.1.sum (fun _ n => n) := by
    rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by omega),
      Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
        (X.1.1 - Finsupp.single g 1) (2 * q₂ + 1)
        (by intro g' hg'; have := h2nd g' hg'; omega)]
    exact totalMult_sub_single_one hg_one
  have hcellsX :
      X.1.1.sum (fun _ n => (n : ℚ)) =
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      simpa [Sigma.sigma] using (@signature_sum_eq_rank X.1.1)
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
      simpa [Sigma.sigma, Function.iterate_one] using this
    have hcells := MixLambdaPi.cells (Z := X.1.1)
    have hcells' :
        (X.1.1.rank : ℚ) - ((Chromosome.prime^[1] X.1.1).rank : ℚ) =
          X.1.1.sum (fun _ n => (n : ℚ)) := by
      simpa [Function.iterate_one] using hcells
    linarith
  have htotQ :
      (Chromosome.prime^[2 * q₂ + 1] X.1.1).sum (fun _ n => (n : ℚ)) =
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
    have hnat : ((Chromosome.prime^[2 * q₂ + 1] X.1.1).sum (fun _ n => (n : ℚ))) + 1 =
        X.1.1.sum (fun _ n => (n : ℚ)) := by exact_mod_cast htot_nat
    rw [← hcellsX]; linarith
  -- Assemble the three gaps.
  have hgap_pred :
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[2 * q₂ + 2] X.1.1) ≤
        signature (Gene.ofRank 1 g₂.type) +
          signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1) := by
    cases htype : g₂.type with
    | NonPolarized => exact absurd htype hg₂_pol
    | Positive =>
        refine type10_pred_gap_positive X Y hXY ?_
        have hw := case4_window_snd X Y hXY hr1 hseed1 hg_one h2nd (by omega) q₂ (by omega)
        simpa [Sigma.sigma, show 2 + 2 * q₂ = 2 * q₂ + 2 by omega] using hw
    | Negative =>
        refine type10_pred_gap_negative X Y hXY ?_
        have hw := case4_window_fst X Y hXY hr1 hseed1 hg_one h2nd (by omega) q₂ (by omega)
        simpa [Sigma.sigma, show 2 + 2 * q₂ = 2 * q₂ + 2 by omega] using hw
  have hgap_mid : ∀ j, 2 * q₂ + 3 ≤ j → j ≤ 2 * q₂ + 3 →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi
    have hj : j = 2 * q₂ + 3 := by omega
    subst j
    refine type10_mid_gap_odd_of_Y_ne X Y h17_1
      (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by ring⟩) (by omega) ?_
    -- prime^[2q₂+3] Y ≠ 0
    intro hYzero
    have hYrank : ∀ h : Gene, 0 < Y.1.1 h → h.rank ≤ 2 * q₂ + 3 := by
      intro h hh
      have hall :=
        (Chromosome.prime_iterate_eq_zero_rank_le (X := Y.1.1) (k := 2 * q₂ + 3)).2 hYzero
      exact hall h (Finsupp.mem_support_iff.mpr (ne_of_gt hh))
    have hYpol_top : ∀ h : Gene, 0 < Y.1.1 h → h.rank = 2 * q₂ + 3 →
        h.type ≠ GeneType.NonPolarized := by
      intro h hh hhrank
      have hhodd : Odd h.rank := by rw [hhrank]; exact ⟨q₂ + 1, by ring⟩
      have hodd_part : 0 < Y.1.1.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]; exact hh
      exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
        (Finsupp.mem_support_iff.mpr hodd_part.ne')
    cases htype : g₂.type with
    | NonPolarized => exact absurd htype hg₂_pol
    | Positive =>
        have hno_pos : Y.1.1 ⟨2 * q₂ + 3, GeneType.Positive, by omega⟩ = 0 := by
          have htop_eq_g : (⟨2 * q₂ + 3, GeneType.Positive, by omega⟩ : Gene) = g₂ :=
            Gene.ext (by dsimp; rw [hg₂_rank_q]) htype.symm
          have hle := hcommon g₂ hXg₂
          rw [htop_eq_g]; omega
        have hYfst0 :=
          signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
            (W := Y.1.1) (p := q₂ + 1) hYpol_top hYrank hno_pos
        have hYfst0' : (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1 = 0 := by
          simpa [show 2 * (q₂ + 1) = 2 * q₂ + 2 by omega] using hYfst0
        have hXfst1 :=
          one_le_signature_prime_pred_fst_of_positive (X := X.1.1) (gpos := g₂) htype hXg₂
        have hXfst1' : 1 ≤ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 := by
          simpa [hg₂_rank_q, show 2 * q₂ + 3 - 1 = 2 * q₂ + 2 by omega] using hXfst1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).1
        linarith
    | Negative =>
        have hno_neg : Y.1.1 ⟨2 * q₂ + 3, GeneType.Negative, by omega⟩ = 0 := by
          have htop_eq_g : (⟨2 * q₂ + 3, GeneType.Negative, by omega⟩ : Gene) = g₂ :=
            Gene.ext (by dsimp; rw [hg₂_rank_q]) htype.symm
          have hle := hcommon g₂ hXg₂
          rw [htop_eq_g]; omega
        have hYsnd0 :=
          signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
            (W := Y.1.1) (p := q₂ + 1) hYpol_top hYrank hno_neg
        have hYsnd0' : (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2 = 0 := by
          simpa [show 2 * (q₂ + 1) = 2 * q₂ + 2 by omega] using hYsnd0
        have hXsnd1 :=
          one_le_signature_prime_pred_snd_of_negative (X := X.1.1) (gneg := g₂) htype hXg₂
        have hXsnd1' : 1 ≤ (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 := by
          simpa [hg₂_rank_q, show 2 * q₂ + 3 - 1 = 2 * q₂ + 2 by omega] using hXsnd1
        have hdom := (le_iff_dominates.mp hXY.le (2 * q₂ + 2)).2
        linarith
  have hgap_succ :
      signature (Gene.ofRank 1 g₂.type) +
          signature (Chromosome.prime^[2 * q₂ + 4] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1) := by
    cases htype : g₂.type with
    | NonPolarized => exact absurd htype hg₂_pol
    | Positive =>
        have hW : ∀ z ∈ (Chromosome.prime^[2 * q₂ + 1] X.1.1).support,
            2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
          intro z hz
          have hzpos : 0 < (Chromosome.prime^[2 * q₂ + 1] X.1.1) z :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
          let z0 : Gene := ⟨z.rank + (2 * q₂ + 1), z.type, Nat.le_add_right_of_le z.rank_pos⟩
          have hz0X : 0 < X.1.1 z0 := by
            have hcoeff := prime_iterate_coeff (2 * q₂ + 1) X.1.1 z
            change (Chromosome.prime^[2 * q₂ + 1] X.1.1) z = X.1.1 z0 at hcoeff
            rwa [← hcoeff]
          have hz0_ne_g : z0 ≠ g := by
            intro h
            have hcontra : z0.rank = 1 := by rw [← hg_rank_one]; exact congrArg Gene.rank h
            have hz0rk : z0.rank = z.rank + (2 * q₂ + 1) := rfl
            have := z.rank_pos; omega
          have hz0_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) z0 := by
            rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hz0_ne_g)]; omega
          have hz0_rank_ge := hg₂min z0 hz0_rest
          rw [hg₂_rank_q] at hz0_rank_ge
          have hz0r : 2 * q₂ + 3 ≤ z.rank + (2 * q₂ + 1) := hz0_rank_ge
          refine ⟨by omega, ?_⟩
          intro hz_rank
          have hz0_support : z0 ∈ X.1.1.support := Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
          have hz0_rank_eq : z0.rank = g₂.rank := by
            have hz0r2 : z0.rank = z.rank + (2 * q₂ + 1) := rfl; omega
          cases hz_type : z.type with
          | NonPolarized =>
              have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
              exact absurd (hz_type) hpol0
          | Positive => rfl
          | Negative =>
              exact absurd (hno_pair ⟨g₂, z0, hz0_rank_eq.symm, htype,
                hz_type, hXg₂, hz0X⟩) not_false
        have hXdrop_raw :=
          edge_drop_fst_eq_totalMult_positive_iterate (W := X.1.1) (i := 2 * q₂ + 1) hW
        have hXdrop :
            (Sigma.sigma X.1.1 (2 * q₂ + 2)).1 - (Sigma.sigma X.1.1 (2 * q₂ + 4)).1 =
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
          rw [show (1 : ℕ) + (2 * q₂ + 1) = 2 * q₂ + 2 by omega,
            show (3 : ℕ) + (2 * q₂ + 1) = 2 * q₂ + 4 by omega] at hXdrop_raw
          rw [hXdrop_raw, htotQ]
        have hKEY_Y := KEY_Y_fst X Y hr1 (i := 2 * q₂ + 2) ⟨q₂ + 1, by ring⟩
        have hwin := case4_window_fst X Y hXY hr1 hseed1 hg_one h2nd (by omega) q₂ (by omega)
        have hfst_succ :
            (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).1 := by
          simp only [Sigma.sigma, show 2 + 2 * q₂ = 2 * q₂ + 2 by omega] at hXdrop hKEY_Y hwin ⊢
          linarith
        simpa [show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using
          type16_succ_gap_positive X Y hXY (p := q₂ + 1)
            (by simpa [show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using hfst_succ)
    | Negative =>
        have hW : ∀ z ∈ (Chromosome.prime^[2 * q₂ + 1] X.1.1).support,
            2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
          intro z hz
          have hzpos : 0 < (Chromosome.prime^[2 * q₂ + 1] X.1.1) z :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
          let z0 : Gene := ⟨z.rank + (2 * q₂ + 1), z.type, Nat.le_add_right_of_le z.rank_pos⟩
          have hz0X : 0 < X.1.1 z0 := by
            have hcoeff := prime_iterate_coeff (2 * q₂ + 1) X.1.1 z
            change (Chromosome.prime^[2 * q₂ + 1] X.1.1) z = X.1.1 z0 at hcoeff
            rwa [← hcoeff]
          have hz0_ne_g : z0 ≠ g := by
            intro h
            have hcontra : z0.rank = 1 := by rw [← hg_rank_one]; exact congrArg Gene.rank h
            have hz0rk : z0.rank = z.rank + (2 * q₂ + 1) := rfl
            have := z.rank_pos; omega
          have hz0_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) z0 := by
            rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hz0_ne_g)]; omega
          have hz0_rank_ge := hg₂min z0 hz0_rest
          rw [hg₂_rank_q] at hz0_rank_ge
          have hz0r : 2 * q₂ + 3 ≤ z.rank + (2 * q₂ + 1) := hz0_rank_ge
          refine ⟨by omega, ?_⟩
          intro hz_rank
          have hz0_support : z0 ∈ X.1.1.support := Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
          have hz0_rank_eq : z0.rank = g₂.rank := by
            have hz0r2 : z0.rank = z.rank + (2 * q₂ + 1) := rfl; omega
          cases hz_type : z.type with
          | NonPolarized =>
              have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
              exact absurd (hz_type) hpol0
          | Negative => rfl
          | Positive =>
              exact absurd (hno_pair ⟨z0, g₂, hz0_rank_eq, hz_type,
                htype, hz0X, hXg₂⟩) not_false
        have hXdrop_raw :=
          edge_drop_snd_eq_totalMult_negative_iterate (W := X.1.1) (i := 2 * q₂ + 1) hW
        have hXdrop :
            (Sigma.sigma X.1.1 (2 * q₂ + 2)).2 - (Sigma.sigma X.1.1 (2 * q₂ + 4)).2 =
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
          rw [show (1 : ℕ) + (2 * q₂ + 1) = 2 * q₂ + 2 by omega,
            show (3 : ℕ) + (2 * q₂ + 1) = 2 * q₂ + 4 by omega] at hXdrop_raw
          rw [hXdrop_raw, htotQ]
        have hKEY_Y := KEY_Y_snd X Y hr1 (i := 2 * q₂ + 2) ⟨q₂ + 1, by ring⟩
        have hwin := case4_window_snd X Y hXY hr1 hseed1 hg_one h2nd (by omega) q₂ (by omega)
        have hsnd_succ :
            (signature (Chromosome.prime^[2 * q₂ + 4] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1)).2 := by
          simp only [Sigma.sigma, show 2 + 2 * q₂ = 2 * q₂ + 2 by omega] at hXdrop hKEY_Y hwin ⊢
          linarith
        simpa [show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using
          type16_succ_gap_negative X Y hXY (p := q₂ + 1)
            (by simpa [show 2 * (q₂ + 1) + 2 = 2 * q₂ + 4 by omega] using hsnd_succ)
  have hZle :
      (Y10 (le_refl q₂) hg₂_pol hg₂_pol).1 +
          (X.1.1 - Finsupp.single g₂ 1 - Finsupp.single g₂ 1) ≤ Y.1.1 :=
    type10_double_target_add_rest_le_of_gaps hg₂_pol X Y hXY g₂ rfl hg₂_rank_q hg₂_two
      hgap_pred hgap_mid hgap_succ
  exact exists_mutation_le_type10_of_double hg₂_pol X Y g₂ rfl hg₂_rank_q hg₂_two hZle

end Mix2LambdaPi
