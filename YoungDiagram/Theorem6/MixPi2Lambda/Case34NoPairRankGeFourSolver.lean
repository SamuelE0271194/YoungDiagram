import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankGeFour
import YoungDiagram.Theorem6.MixPi2Lambda.Case34Gaps

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Label 4 no-pair rank-ge-four solver (§17 Case 1)

The Label 4 (`Mix (Pi, 2 • Lambda)`) analogue of
`Mix2LambdaPi.exists_mutation_le_no_pair_rank_ge_three`: the minimal polarized
gene has even rank `2*p+2` with `0 < p`, i.e. rank `≥ 4`.  Parity roles are
flipped relative to Label 3 (polarized genes at even rank; reduced §17 symmetric
level even).  All gap/window infrastructure it needs already exists in the
Label 4 `Window` / `Case34Gaps` / `Case34Helpers` layer with the same names as
Label 3 (except `edge_drop_*_eq_total` → `edge_drop_*_eq_totalMult_positive/…`
and `type10_of_double` → `exists_mutation_le_type10_of_double`).

STATUS: dispatcher + the diagonal branch (`_double`, min gene multiplicity ≥ 2,
Label-3 lines 51–313) are PROVEN.  The multiplicity-one branch (`_single`,
Label-3 lines 314–938, the two-gene type10 move) is still `sorry`.

IMPLEMENTATION NOTE (the one non-obvious pitfall when porting the branch bodies):
the gap lemmas (`type10_pred_gap_positive`, `seed_*`, `window_even_*`, …) are
stated with exponents of the shape `2 * p + 1` / `2 * p`.  The branch proofs
carry concrete offsets like `2*q+3`, `2*q+4`, `2*q+5`, `2*q+2`.  Applying a
`2*p+c` lemma directly to a `2*q+d` goal makes Lean try to unify
`2 * ?p + c =?= 2 * q + d`, which is NOT defeq for the variable `q` and sends
the elaborator into an unbounded `whnf` loop (deterministic heartbeat timeout —
raising `maxHeartbeats` does NOT help).  Fix mechanically at every such site:
first normalize the exponent to the lemma's shape, e.g.
`rw [show (2*q+3 : ℕ) = 2*(q+1)+1 from by ring] at hseed ⊢`, then apply the
lemma with the index passed EXPLICITLY: `type10_pred_gap_positive (p := q+1) …`.
Never let a `2*?p+c =?= 2*q+d` unification be attempted. -/

set_option maxHeartbeats 800000 in
lemma exists_mutation_le_no_pair_rank_ge_four_double
    {m p : ℕ} (X Y : nMixPi2Lambda (m + 2))
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
    (hXne : X.1.1 ≠ 0)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hg_rank : g.rank = 2 * p + 2) (hp : 0 < p)
    (hg_two : 2 ≤ X.1.1 g) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨q, hg_rank_q, hmin_rank, hXprime1_ne, hYprime1_ne, hr1⟩ :=
    no_pair_rank_ge_four_window_data X Y hXY h17_1 g hgX hgmin hg_rank hp
  have hg_rank' : g.rank = 2 * (q + 1) + 2 := by rw [hg_rank_q]; ring
  -- The X-drop over the window uses that every gene of `X` has rank ≥ 2q+4.
  cases htype : g.type with
  | NonPolarized => exact absurd htype hg_pol
  | Positive =>
      -- successor strictness at level 2q+5 via the edge drop
      have hsucc : (signature (Chromosome.prime^[2 * (q + 1) + 3] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * (q + 1) + 3] Y.1.1)).1 := by
        have hWpos : ∀ z ∈ (Chromosome.prime^[2 * q + 2] X.1.1).support,
            2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
          intro z hz
          have hzpos : 0 < (Chromosome.prime^[2 * q + 2] X.1.1) z :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
          let z0 : Gene :=
            ⟨z.rank + (2 * q + 2), z.type, Nat.le_add_right_of_le z.rank_pos⟩
          have hz0X : 0 < X.1.1 z0 := by
            have hcoeff := prime_iterate_coeff (2 * q + 2) X.1.1 z
            change (Chromosome.prime^[2 * q + 2] X.1.1) z = X.1.1 z0 at hcoeff
            rwa [← hcoeff]
          have hz0_rank_le := hgmin z0 hz0X
          refine ⟨?_, ?_⟩
          · dsimp [z0] at hz0_rank_le; rw [hg_rank_q] at hz0_rank_le; omega
          · intro hz_rank
            have hz0_support : z0 ∈ X.1.1.support :=
              Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
            have hz0_rank_eq : z0.rank = g.rank := by
              dsimp [z0]; rw [hz_rank, hg_rank_q]; omega
            cases hz_type : z.type with
            | NonPolarized =>
                have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
                exact absurd (by simpa [z0] using hz_type) hpol0
            | Positive => rfl
            | Negative =>
                exact absurd ⟨g, z0, hz0_rank_eq.symm, htype,
                  by simpa [z0] using hz_type, hgX, hz0X⟩ hno_pair
        have hXdrop_raw :=
          edge_drop_fst_eq_totalMult_positive_iterate (W := X.1.1) (i := 2 * q + 2) hWpos
        have hWsum_nat :
            (Chromosome.prime^[2 * q + 2] X.1.1).sum (fun _ n => n) =
              X.1.1.sum (fun _ n => n) :=
          Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
            X.1.1 (2 * q + 2) (by
              intro h hh; have hle := hmin_rank h hh; omega)
        have hWsum := totalMult_cast_eq_of_nat_eq hWsum_nat
        have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
        have hXdrop :
            (Sigma.sigma X.1.1 (2 * q + 3)).1 - (Sigma.sigma X.1.1 (2 * q + 5)).1 =
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
          rw [show 1 + (2 * q + 2) = 2 * q + 3 by omega,
            show 3 + (2 * q + 2) = 2 * q + 5 by omega] at hXdrop_raw
          linarith
        have hdom := (le_iff_dominates.mp hXY.le (2 * q + 3)).1
        have hs := seed_fst_lt_odd X Y hr1 (i := 2 * q + 3)
          (Nat.not_even_iff_odd.mpr ⟨q + 1, by ring⟩) hXdrop hdom
        simpa [Sigma.sigma, show 2 * q + 3 + 2 = 2 * (q + 1) + 3 by ring] using hs
      -- the mid level is nonzero on `Y` because the successor level is
      have hY5 : Chromosome.prime^[2 * (q + 1) + 3] Y.1.1 ≠ 0 := by
        intro hz
        rw [hz, map_zero] at hsucc
        have hnn := (signature_nonneg (Chromosome.prime^[2 * (q + 1) + 3] X.1.1)).1
        simp only [Prod.fst_zero] at hsucc hnn
        linarith
      have hYmid : Chromosome.prime^[2 * (q + 1) + 2] Y.1.1 ≠ 0 := by
        intro hz
        apply hY5
        rw [show 2 * (q + 1) + 3 = (2 * (q + 1) + 2) + 1 by ring,
          Function.iterate_succ_apply', hz, map_zero]
      have hεP : GeneType.Positive ≠ GeneType.NonPolarized := by decide
      have hZle :
          (Y10 (le_refl (q + 1)) hεP hεP).1 +
              (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) ≤ Y.1.1 := by
        refine type10_double_target_add_rest_le_of_gaps hεP X Y hXY g htype
          hg_rank' hg_two ?_ ?_ ?_
        · -- pred gap at 2q+3
          refine type10_pred_gap_positive (p := q + 1) X Y hXY ?_
          have hXdrop := KEY_X_full_snd X hmin_rank (i := 2 * q + 1) (by omega)
          have hdom := (le_iff_dominates.mp hXY.le (2 * q + 1)).2
          have hs := seed_snd_lt_odd X Y hr1 (i := 2 * q + 1)
            (Nat.not_even_iff_odd.mpr ⟨q, by ring⟩) hXdrop hdom
          simpa [Sigma.sigma, show 2 * q + 1 + 2 = 2 * (q + 1) + 1 by ring] using hs
        · -- mid gap at 2q+4
          intro j hjlo hjhi
          have hj : j = 2 * (q + 1) + 2 := by omega
          subst hj
          exact type10_mid_gap_even_of_Y_ne X Y h17_1 ⟨q + 2, by ring⟩ (by omega) hYmid
        · -- succ gap at 2q+5
          exact type10_succ_gap_positive (q := q + 1) X Y hXY hsucc
      exact exists_mutation_le_type10_of_double hεP X Y g htype hg_rank' hg_two hZle
  | Negative =>
      have hsucc : (signature (Chromosome.prime^[2 * (q + 1) + 3] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * (q + 1) + 3] Y.1.1)).2 := by
        have hWneg : ∀ z ∈ (Chromosome.prime^[2 * q + 2] X.1.1).support,
            2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
          intro z hz
          have hzpos : 0 < (Chromosome.prime^[2 * q + 2] X.1.1) z :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
          let z0 : Gene :=
            ⟨z.rank + (2 * q + 2), z.type, Nat.le_add_right_of_le z.rank_pos⟩
          have hz0X : 0 < X.1.1 z0 := by
            have hcoeff := prime_iterate_coeff (2 * q + 2) X.1.1 z
            change (Chromosome.prime^[2 * q + 2] X.1.1) z = X.1.1 z0 at hcoeff
            rwa [← hcoeff]
          have hz0_rank_le := hgmin z0 hz0X
          refine ⟨?_, ?_⟩
          · dsimp [z0] at hz0_rank_le; rw [hg_rank_q] at hz0_rank_le; omega
          · intro hz_rank
            have hz0_support : z0 ∈ X.1.1.support :=
              Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
            have hz0_rank_eq : z0.rank = g.rank := by
              dsimp [z0]; rw [hz_rank, hg_rank_q]; omega
            cases hz_type : z.type with
            | NonPolarized =>
                have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
                exact absurd (by simpa [z0] using hz_type) hpol0
            | Positive =>
                exact absurd ⟨z0, g, hz0_rank_eq, by simpa [z0] using hz_type,
                  htype, hz0X, hgX⟩ hno_pair
            | Negative => rfl
        have hXdrop_raw :=
          edge_drop_snd_eq_totalMult_negative_iterate (W := X.1.1) (i := 2 * q + 2) hWneg
        have hWsum_nat :
            (Chromosome.prime^[2 * q + 2] X.1.1).sum (fun _ n => n) =
              X.1.1.sum (fun _ n => n) :=
          Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
            X.1.1 (2 * q + 2) (by
              intro h hh; have hle := hmin_rank h hh; omega)
        have hWsum := totalMult_cast_eq_of_nat_eq hWsum_nat
        have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
        have hXdrop :
            (Sigma.sigma X.1.1 (2 * q + 3)).2 - (Sigma.sigma X.1.1 (2 * q + 5)).2 =
              (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
          rw [show 1 + (2 * q + 2) = 2 * q + 3 by omega,
            show 3 + (2 * q + 2) = 2 * q + 5 by omega] at hXdrop_raw
          linarith
        have hdom := (le_iff_dominates.mp hXY.le (2 * q + 3)).2
        have hs := seed_snd_lt_odd X Y hr1 (i := 2 * q + 3)
          (Nat.not_even_iff_odd.mpr ⟨q + 1, by ring⟩) hXdrop hdom
        simpa [Sigma.sigma, show 2 * q + 3 + 2 = 2 * (q + 1) + 3 by ring] using hs
      have hY5 : Chromosome.prime^[2 * (q + 1) + 3] Y.1.1 ≠ 0 := by
        intro hz
        rw [hz, map_zero] at hsucc
        have hnn := (signature_nonneg (Chromosome.prime^[2 * (q + 1) + 3] X.1.1)).2
        simp only [Prod.snd_zero] at hsucc hnn
        linarith
      have hYmid : Chromosome.prime^[2 * (q + 1) + 2] Y.1.1 ≠ 0 := by
        intro hz
        apply hY5
        rw [show 2 * (q + 1) + 3 = (2 * (q + 1) + 2) + 1 by ring,
          Function.iterate_succ_apply', hz, map_zero]
      have hεN : GeneType.Negative ≠ GeneType.NonPolarized := by decide
      have hZle :
          (Y10 (le_refl (q + 1)) hεN hεN).1 +
              (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) ≤ Y.1.1 := by
        refine type10_double_target_add_rest_le_of_gaps hεN X Y hXY g htype
          hg_rank' hg_two ?_ ?_ ?_
        · refine type10_pred_gap_negative (p := q + 1) X Y hXY ?_
          have hXdrop := KEY_X_full_fst X hmin_rank (i := 2 * q + 1) (by omega)
          have hdom := (le_iff_dominates.mp hXY.le (2 * q + 1)).1
          have hs := seed_fst_lt_odd X Y hr1 (i := 2 * q + 1)
            (Nat.not_even_iff_odd.mpr ⟨q, by ring⟩) hXdrop hdom
          simpa [Sigma.sigma, show 2 * q + 1 + 2 = 2 * (q + 1) + 1 by ring] using hs
        · intro j hjlo hjhi
          have hj : j = 2 * (q + 1) + 2 := by omega
          subst hj
          exact type10_mid_gap_even_of_Y_ne X Y h17_1 ⟨q + 2, by ring⟩ (by omega) hYmid
        · exact type10_succ_gap_negative (q := q + 1) X Y hXY hsucc
      exact exists_mutation_le_type10_of_double hεN X Y g htype hg_rank' hg_two hZle

set_option maxHeartbeats 800000 in
lemma exists_mutation_le_no_pair_rank_ge_four_single
    {m p : ℕ} (X Y : nMixPi2Lambda (m + 2))
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
    (hXne : X.1.1 ≠ 0)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hg_rank : g.rank = 2 * p + 2) (hp : 0 < p)
    (hg_two : ¬ 2 ≤ X.1.1 g) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

set_option maxHeartbeats 800000 in
lemma exists_mutation_le_no_pair_rank_ge_four
    {m p : ℕ} (X Y : nMixPi2Lambda (m + 2))
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
    (hXne : X.1.1 ≠ 0)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hg_rank : g.rank = 2 * p + 2) (hp : 0 < p) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hg_two : 2 ≤ X.1.1 g
  · exact exists_mutation_le_no_pair_rank_ge_four_double X Y hXY hcommon h17_1
      hXpol hno_pair hXne g hgX hgmin hg_pol hg_rank hp hg_two
  · exact exists_mutation_le_no_pair_rank_ge_four_single X Y hXY hcommon h17_1
      hXpol hno_pair hXne g hgX hgmin hg_pol hg_rank hp hg_two

end MixPi2Lambda
