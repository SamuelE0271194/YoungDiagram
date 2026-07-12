import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleOpposite

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Preferred Case 1 endpoint

The ordinary odd window stops immediately before the selected second gene.
This module computes the final two-step X-drop exactly and closes the
sign-aligned successor component required by Type10.
-/

/-- In the level-one preferred branch, the successor component aligned with
the selected minimum remainder gene is strict. -/
lemma no_pair_rank_two_single_preferred_succ_aligned
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene) (hg_rank : g.rank = 2)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hXg₂ : 0 < X.1.1 g₂)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
      2 * q₂ + 4 ≤ h.rank)
    (hpreferred :
      (g.type = GeneType.Positive ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) ∨
      (g.type = GeneType.Negative ∧
        (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1)) :
    (g₂.type = GeneType.Positive ∧
      (signature (Chromosome.prime^[2 * q₂ + 5] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q₂ + 5] Y.1.1)).1) ∨
    (g₂.type = GeneType.Negative ∧
      (signature (Chromosome.prime^[2 * q₂ + 5] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q₂ + 5] Y.1.1)).2) := by
  have hWtop : ∀ z ∈ (Chromosome.prime^[2 * q₂ + 2] X.1.1).support,
      2 ≤ z.rank ∧ (z.rank = 2 → z.type = g₂.type) := by
    intro z hz
    let z0 : Gene :=
      ⟨z.rank + (2 * q₂ + 2), z.type,
        Nat.le_add_right_of_le z.rank_pos⟩
    have hz0X : 0 < X.1.1 z0 := by
      have hcoeff := prime_iterate_coeff (2 * q₂ + 2) X.1.1 z
      change (Chromosome.prime^[2 * q₂ + 2] X.1.1) z = X.1.1 z0 at hcoeff
      rw [← hcoeff]
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
    have hz0_ne_g : z0 ≠ g := by
      intro hzg
      have hrank := congrArg Gene.rank hzg
      dsimp [z0] at hrank
      rw [hg_rank] at hrank
      have hzpos := z.rank_pos
      omega
    have hz0_rest : 0 < (X.1.1 - Finsupp.single g 1 : Chromosome) z0 := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply,
        if_neg (fun h => hz0_ne_g h.symm)]
      exact hz0X
    have hz0_rank_le := h2nd z0
      (Finsupp.mem_support_iff.mpr (ne_of_gt hz0_rest))
    constructor
    · dsimp [z0] at hz0_rank_le
      omega
    · intro hz_rank
      have hz0_support : z0 ∈ X.1.1.support :=
        Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
      have hz0_rank_eq : z0.rank = g₂.rank := by
        dsimp [z0]
        rw [hz_rank, hg₂_rank]
        omega
      have hz0_pol := Chromosome.IsPolarized_def'.mp hXpol z0 hz0_support
      cases hz_type : z.type with
      | NonPolarized =>
          exact False.elim (hz0_pol (by simpa [z0] using hz_type))
      | Positive =>
          cases hg₂_type : g₂.type with
          | NonPolarized => exact False.elim (hg₂_pol hg₂_type)
          | Positive => rfl
          | Negative =>
              exact False.elim (hno_pair ⟨z0, g₂, hz0_rank_eq,
                by simpa [z0] using hz_type, hg₂_type, hz0X, hXg₂⟩)
      | Negative =>
          cases hg₂_type : g₂.type with
          | NonPolarized => exact False.elim (hg₂_pol hg₂_type)
          | Positive =>
              exact False.elim (hno_pair ⟨g₂, z0, hz0_rank_eq.symm,
                hg₂_type, by simpa [z0] using hz_type, hXg₂, hz0X⟩)
          | Negative => rfl
  have hWsum_nat :
      (Chromosome.prime^[2 * q₂ + 2] X.1.1).sum (fun _ n => n) =
        (X.1.1 - Finsupp.single g 1 : Chromosome).sum (fun _ n => n) := by
    rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by rw [hg_rank]; omega)]
    exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
      (X.1.1 - Finsupp.single g 1 : Chromosome) (2 * q₂ + 2) (by
        intro h hh
        have hle := h2nd h hh
        omega)
  have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
  have hWsum :
      (Chromosome.prime^[2 * q₂ + 2] X.1.1).sum (fun _ n => (n : ℚ)) =
        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
    have hcast := totalMult_cast_eq_of_nat_eq hWsum_nat
    have hrest := totalMult_sub_single_one_cast hg_one
    rw [hcast, hrest, hD]
  have hpred := no_pair_rank_two_single_preferred_odd_mid_gap
    X Y hXY hr1 g hg_rank hg_one h2nd (by omega) hpreferred
  cases hg₂_type : g₂.type with
  | NonPolarized => exact False.elim (hg₂_pol hg₂_type)
  | Positive =>
      left
      refine ⟨rfl, ?_⟩
      have hWpos : ∀ z ∈ (Chromosome.prime^[2 * q₂ + 2] X.1.1).support,
          2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
        intro z hz
        refine ⟨(hWtop z hz).1, ?_⟩
        intro hzrank
        rw [(hWtop z hz).2 hzrank, hg₂_type]
      have hXdrop := edge_drop_fst_eq_totalMult_positive_iterate
        (W := X.1.1) (i := 2 * q₂ + 2) hWpos
      rw [show 1 + (2 * q₂ + 2) = 2 * q₂ + 3 by omega,
        show 3 + (2 * q₂ + 2) = 2 * q₂ + 5 by omega, hWsum] at hXdrop
      have hYdrop := KEY_Y_fst_odd X Y hr1
        (i := 2 * q₂ + 3)
        (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by omega⟩)
      have hpred_fst :
          (signature (Chromosome.prime^[2 * q₂ + 3] X.1.1)).1 <
            (signature (Chromosome.prime^[2 * q₂ + 3] Y.1.1)).1 := by
        have h := (hpred (2 * q₂ + 3) (by omega) (by omega)
          (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by omega⟩)).1
        simp only [Prod.fst_add] at h
        linarith
      simp only [Sigma.sigma,
        show 2 * q₂ + 3 + 2 = 2 * q₂ + 5 by omega] at hXdrop hYdrop
      linarith
  | Negative =>
      right
      refine ⟨rfl, ?_⟩
      have hWneg : ∀ z ∈ (Chromosome.prime^[2 * q₂ + 2] X.1.1).support,
          2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
        intro z hz
        refine ⟨(hWtop z hz).1, ?_⟩
        intro hzrank
        rw [(hWtop z hz).2 hzrank, hg₂_type]
      have hXdrop := edge_drop_snd_eq_totalMult_negative_iterate
        (W := X.1.1) (i := 2 * q₂ + 2) hWneg
      rw [show 1 + (2 * q₂ + 2) = 2 * q₂ + 3 by omega,
        show 3 + (2 * q₂ + 2) = 2 * q₂ + 5 by omega, hWsum] at hXdrop
      have hYdrop := KEY_Y_snd_odd X Y hr1
        (i := 2 * q₂ + 3)
        (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by omega⟩)
      have hpred_snd :
          (signature (Chromosome.prime^[2 * q₂ + 3] X.1.1)).2 <
            (signature (Chromosome.prime^[2 * q₂ + 3] Y.1.1)).2 := by
        have h := (hpred (2 * q₂ + 3) (by omega) (by omega)
          (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by omega⟩)).2
        simp only [Prod.snd_add] at h
        linarith
      simp only [Sigma.sigma,
        show 2 * q₂ + 3 + 2 = 2 * q₂ + 5 by omega] at hXdrop hYdrop
      linarith

/-- Complete callback-free preferred Case 1 solver. -/
lemma exists_mutation_le_no_pair_rank_two_single_preferred
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ h : Gene, 0 < X.1.1 h → Y.1.1 h ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene) (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg_one : X.1.1 g = 1) (hXg₂ : 0 < X.1.1 g₂)
    (hne : g ≠ g₂)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
      2 * q₂ + 4 ≤ h.rank)
    (hpreferred :
      (g.type = GeneType.Positive ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) ∨
      (g.type = GeneType.Negative ∧
        (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hYtop := no_pair_rank_two_single_Y_iterate_ne_at_common_free_gene_rank
    X Y hXY hcommon g₂ hXg₂ hg₂_rank hg₂_pol
  have hsucc := no_pair_rank_two_single_preferred_succ_aligned
    X Y hXY hr1 hXpol hno_pair g g₂ hg_rank hg₂_rank hg_one hXg₂
      hg₂_pol h2nd hpreferred
  exact exists_mutation_le_no_pair_rank_two_single_preferred_of_endpoint_component_gaps
    X Y hXY h17_1 hr1 g g₂ hg_pol hg₂_pol hg_rank hg₂_rank hg_one
      (by omega) hne h2nd hpreferred hYtop hsucc

end MixPi2Lambda
