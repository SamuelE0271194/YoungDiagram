import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

set_option maxHeartbeats 800000 in
-- The rank-ge-three no-pair branch still contains the long type10 window proof;
-- keep its former local heartbeat budget after extracting it from the dispatcher.
lemma exists_mutation_le_no_pair_rank_ge_three
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
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
    (hp : g.rank = 2 * p + 1) (hp0 : ¬ p = 0) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let q := p - 1
  have hpq : p = q + 1 := by omega
  have hg_rank_q : g.rank = 2 * q + 3 := by omega
  have hg_ne_np : g.type ≠ GeneType.NonPolarized := hg_pol
  have hXprime1_ne : Chromosome.prime^[1] X.1.1 ≠ 0 := by
    change X.1.1.prime ≠ 0
    apply prime_ne_zero_of_rank_ge_two hXne
    intro h hh
    have hhpos : 0 < X.1.1 h :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have hle := hgmin h hhpos
    rw [hg_rank_q] at hle
    omega
  have hYprime1_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
    intro hYzero
    have hle := le_iff_dominates.mp hXY.le 1
    rw [hYzero, map_zero] at hle
    exact hXprime1_ne (signature_eq_zero (le_antisymm hle (signature_nonneg _)))
  have hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank :=
    h17_1 1 (by omega) hYprime1_ne
  by_cases hg_two : 2 ≤ X.1.1 g
  · -- The diagonal subcase `2g^ε(2q+3) → g^ε(2q+1)+g^ε(2q+5)`.
    have hmin_rank : ∀ h ∈ X.1.1.support, 2 * q + 3 ≤ h.rank := by
      intro h hh
      have hhpos : 0 < X.1.1 h :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      have hle := hgmin h hhpos
      rw [hg_rank_q] at hle
      exact hle
    have hZle :
        (Y10 (le_refl q) hg_ne_np hg_ne_np).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) ≤ Y.1.1 := by
      have hgap_pred :
          ((1 : ℚ), (1 : ℚ)) +
              signature (Chromosome.prime^[2 * q + 2] X.1.1) ≤
            signature (Gene.ofRank 1 g.type) +
              signature (Chromosome.prime^[2 * q + 2] Y.1.1) := by
        cases htype : g.type with
        | NonPolarized => exact False.elim (hg_ne_np htype)
        | Positive =>
            exact type10_pred_gap_positive X Y hXY (by
              have hXdrop := KEY_X_full_snd X hmin_rank
                (i := 2 * q) (by omega)
              have hdom := (le_iff_dominates.mp hXY.le (2 * q)).2
              simpa [Sigma.sigma, show 2 * q + 2 = 2 * q + 2 by rfl] using
                seed_snd_lt X Y hr1 (i := 2 * q)
                  (hi := ⟨q, by ring⟩) hXdrop hdom)
        | Negative =>
            exact type10_pred_gap_negative X Y hXY (by
              have hXdrop := KEY_X_full_fst X hmin_rank
                (i := 2 * q) (by omega)
              have hdom := (le_iff_dominates.mp hXY.le (2 * q)).1
              simpa [Sigma.sigma, show 2 * q + 2 = 2 * q + 2 by rfl] using
                seed_fst_lt X Y hr1 (i := 2 * q)
                  (hi := ⟨q, by ring⟩) hXdrop hdom)
      have hgap_mid : ∀ j, 2 * q + 3 ≤ j → j ≤ 2 * q + 3 →
          ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1) := by
        intro j hjlo hjhi
        have hj : j = 2 * q + 3 := by omega
        subst j
        exact type10_mid_gap_odd_of_Y_ne X Y h17_1
          (Nat.not_even_iff_odd.mpr ⟨q + 1, by ring⟩) (by omega) (by
            intro hYzero
            have hYrank :
                ∀ h : Gene, 0 < Y.1.1 h → h.rank ≤ 2 * (q + 1) + 1 := by
              intro h hh
              have hall :=
                (Chromosome.prime_iterate_eq_zero_rank_le
                  (X := Y.1.1) (k := 2 * q + 3)).2 hYzero
              have hle := hall h (Finsupp.mem_support_iff.mpr (ne_of_gt hh))
              omega
            have hYpol_top :
                ∀ h : Gene, 0 < Y.1.1 h → h.rank = 2 * (q + 1) + 1 →
                  h.type ≠ GeneType.NonPolarized := by
              intro h hh hhrank
              have hhodd : Odd h.rank := by
                rw [hhrank]
                exact ⟨q + 1, by ring⟩
              have hodd_part : 0 < Y.1.1.oddPart h := by
                rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]
                exact hh
              exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
                (Finsupp.mem_support_iff.mpr hodd_part.ne')
            cases htype : g.type with
            | NonPolarized => exact False.elim (hg_ne_np htype)
            | Positive =>
                have hno_pos :
                    Y.1.1 ⟨2 * (q + 1) + 1, GeneType.Positive, by omega⟩ = 0 := by
                  have htop_eq_g :
                      ⟨2 * (q + 1) + 1, GeneType.Positive, by omega⟩ = g := by
                    have hrank_top :
                        (⟨2 * (q + 1) + 1, GeneType.Positive, by omega⟩ : Gene).rank =
                          g.rank := by
                      dsimp
                      rw [hg_rank_q]
                      omega
                    exact Gene.ext hrank_top htype.symm
                  have hle := hcommon g hgX
                  rw [htop_eq_g]
                  omega
                have hYfst0 :=
                  signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
                    (W := Y.1.1) (p := q + 1) hYpol_top hYrank hno_pos
                have hYfst0' :
                    (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 = 0 := by
                  simpa [show 2 * (q + 1) = 2 * q + 2 by omega] using hYfst0
                have hXfst1 :=
                  one_le_signature_prime_pred_fst_of_positive
                    (X := X.1.1) (gpos := g) htype hgX
                have hXfst1' :
                    1 ≤ (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 := by
                  simpa [hg_rank_q, show 2 * q + 3 - 1 = 2 * q + 2 by omega]
                    using hXfst1
                have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).1
                linarith
            | Negative =>
                have hno_neg :
                    Y.1.1 ⟨2 * (q + 1) + 1, GeneType.Negative, by omega⟩ = 0 := by
                  have htop_eq_g :
                      ⟨2 * (q + 1) + 1, GeneType.Negative, by omega⟩ = g := by
                    have hrank_top :
                        (⟨2 * (q + 1) + 1, GeneType.Negative, by omega⟩ : Gene).rank =
                          g.rank := by
                      dsimp
                      rw [hg_rank_q]
                      omega
                    exact Gene.ext hrank_top htype.symm
                  have hle := hcommon g hgX
                  rw [htop_eq_g]
                  omega
                have hYsnd0 :=
                  signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
                    (W := Y.1.1) (p := q + 1) hYpol_top hYrank hno_neg
                have hYsnd0' :
                    (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 = 0 := by
                  simpa [show 2 * (q + 1) = 2 * q + 2 by omega] using hYsnd0
                have hXsnd1 :=
                  one_le_signature_prime_pred_snd_of_negative
                    (X := X.1.1) (gneg := g) htype hgX
                have hXsnd1' :
                    1 ≤ (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 := by
                  simpa [hg_rank_q, show 2 * q + 3 - 1 = 2 * q + 2 by omega]
                    using hXsnd1
                have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).2
                linarith)
      have hgap_succ :
          signature (Gene.ofRank 1 g.type) +
              signature (Chromosome.prime^[2 * q + 4] X.1.1) ≤
            signature (Chromosome.prime^[2 * q + 4] Y.1.1) := by
        cases htype : g.type with
        | NonPolarized => exact False.elim (hg_ne_np htype)
        | Positive =>
            simpa [htype, show 2 * (q + 1) + 2 = 2 * q + 4 by omega] using
              type16_succ_gap_positive X Y hXY (p := q + 1) (by
                have hWpos :
                    ∀ z ∈ (Chromosome.prime^[2 * q + 1] X.1.1).support,
                      2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
                  intro z hz
                  have hzpos : 0 < (Chromosome.prime^[2 * q + 1] X.1.1) z :=
                    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
                  let z0 : Gene :=
                    ⟨z.rank + (2 * q + 1), z.type,
                      Nat.le_add_right_of_le z.rank_pos⟩
                  have hz0X : 0 < X.1.1 z0 := by
                    have hcoeff := prime_iterate_coeff (2 * q + 1) X.1.1 z
                    change (Chromosome.prime^[2 * q + 1] X.1.1) z = X.1.1 z0 at hcoeff
                    rwa [← hcoeff]
                  have hz0_rank_le := hgmin z0 hz0X
                  constructor
                  · dsimp [z0] at hz0_rank_le
                    rw [hg_rank_q] at hz0_rank_le
                    omega
                  · intro hz_rank
                    have hz0_support : z0 ∈ X.1.1.support :=
                      Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
                    have hz0_rank_eq : z0.rank = g.rank := by
                      dsimp [z0]
                      rw [hz_rank, hg_rank_q]
                      omega
                    cases hz_type : z.type with
                    | NonPolarized =>
                        have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
                        exact False.elim (hpol0 (by simpa [z0] using hz_type))
                    | Positive => rfl
                    | Negative =>
                        exact False.elim (hno_pair ⟨g, z0, hz0_rank_eq.symm,
                          htype, by simpa [z0] using hz_type, hgX, hz0X⟩)
                have hXdrop_raw :=
                  edge_drop_fst_eq_totalMult_positive_iterate
                    (W := X.1.1) (i := 2 * q + 1) hWpos
                have hWsum_nat :
                    (Chromosome.prime^[2 * q + 1] X.1.1).sum (fun _ n => n) =
                      X.1.1.sum (fun _ n => n) := by
                  exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
                    X.1.1 (2 * q + 1) (by
                      intro h hh
                      have hle := hmin_rank h hh
                      omega)
                have hWsum :
                    (Chromosome.prime^[2 * q + 1] X.1.1).sum (fun _ n => (n : ℚ)) =
                      X.1.1.sum (fun _ n => (n : ℚ)) := by
                  exact_mod_cast hWsum_nat
                have hD :
                    X.1.1.sum (fun _ n => (n : ℚ)) =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
                  have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
                      (X.1.1.rank : ℚ) := by
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
                have hXdrop :
                    (Sigma.sigma X.1.1 (2 * q + 2)).1 -
                        (Sigma.sigma X.1.1 (2 * q + 4)).1 =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
                    have htmp := hXdrop_raw
                    rw [show 1 + (2 * q + 1) = 2 * q + 2 by omega,
                      show 3 + (2 * q + 1) = 2 * q + 4 by omega] at htmp
                    linarith
                have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).1
                have hsucc :
                    (signature (Chromosome.prime^[2 * (q + 1) + 2] X.1.1)).1 <
                      (signature (Chromosome.prime^[2 * (q + 1) + 2] Y.1.1)).1 := by
                  simpa [Sigma.sigma, show 2 * q + 2 + 2 = 2 * (q + 1) + 2 by omega] using
                    seed_fst_lt X Y hr1 (i := 2 * q + 2)
                      (hi := ⟨q + 1, by ring⟩) hXdrop hdom
                exact hsucc)
        | Negative =>
            simpa [htype, show 2 * (q + 1) + 2 = 2 * q + 4 by omega] using
              type16_succ_gap_negative X Y hXY (p := q + 1) (by
                have hWneg :
                    ∀ z ∈ (Chromosome.prime^[2 * q + 1] X.1.1).support,
                      2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
                  intro z hz
                  have hzpos : 0 < (Chromosome.prime^[2 * q + 1] X.1.1) z :=
                    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
                  let z0 : Gene :=
                    ⟨z.rank + (2 * q + 1), z.type,
                      Nat.le_add_right_of_le z.rank_pos⟩
                  have hz0X : 0 < X.1.1 z0 := by
                    have hcoeff := prime_iterate_coeff (2 * q + 1) X.1.1 z
                    change (Chromosome.prime^[2 * q + 1] X.1.1) z = X.1.1 z0 at hcoeff
                    rwa [← hcoeff]
                  have hz0_rank_le := hgmin z0 hz0X
                  constructor
                  · dsimp [z0] at hz0_rank_le
                    rw [hg_rank_q] at hz0_rank_le
                    omega
                  · intro hz_rank
                    have hz0_support : z0 ∈ X.1.1.support :=
                      Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
                    have hz0_rank_eq : z0.rank = g.rank := by
                      dsimp [z0]
                      rw [hz_rank, hg_rank_q]
                      omega
                    cases hz_type : z.type with
                    | NonPolarized =>
                        have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
                        exact False.elim (hpol0 (by simpa [z0] using hz_type))
                    | Positive =>
                        exact False.elim (hno_pair ⟨z0, g, hz0_rank_eq,
                          by simpa [z0] using hz_type, htype, hz0X, hgX⟩)
                    | Negative => rfl
                have hXdrop_raw :=
                  edge_drop_snd_eq_totalMult_negative_iterate
                    (W := X.1.1) (i := 2 * q + 1) hWneg
                have hWsum_nat :
                    (Chromosome.prime^[2 * q + 1] X.1.1).sum (fun _ n => n) =
                      X.1.1.sum (fun _ n => n) := by
                  exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
                    X.1.1 (2 * q + 1) (by
                      intro h hh
                      have hle := hmin_rank h hh
                      omega)
                have hWsum :
                    (Chromosome.prime^[2 * q + 1] X.1.1).sum (fun _ n => (n : ℚ)) =
                      X.1.1.sum (fun _ n => (n : ℚ)) := by
                  exact_mod_cast hWsum_nat
                have hD :
                    X.1.1.sum (fun _ n => (n : ℚ)) =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
                  have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
                      (X.1.1.rank : ℚ) := by
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
                have hXdrop :
                    (Sigma.sigma X.1.1 (2 * q + 2)).2 -
                        (Sigma.sigma X.1.1 (2 * q + 4)).2 =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
                    have htmp := hXdrop_raw
                    rw [show 1 + (2 * q + 1) = 2 * q + 2 by omega,
                      show 3 + (2 * q + 1) = 2 * q + 4 by omega] at htmp
                    linarith
                have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).2
                have hsucc :
                    (signature (Chromosome.prime^[2 * (q + 1) + 2] X.1.1)).2 <
                      (signature (Chromosome.prime^[2 * (q + 1) + 2] Y.1.1)).2 := by
                  simpa [Sigma.sigma, show 2 * q + 2 + 2 = 2 * (q + 1) + 2 by omega] using
                    seed_snd_lt X Y hr1 (i := 2 * q + 2)
                      (hi := ⟨q + 1, by ring⟩) hXdrop hdom
                exact hsucc)
      exact type10_double_target_add_rest_le_of_gaps hg_ne_np X Y hXY
        g rfl hg_rank_q hg_two hgap_pred hgap_mid hgap_succ
    exact exists_mutation_le_type10_of_double hg_ne_np X Y g rfl hg_rank_q hg_two hZle
  · -- Multiplicity-one subcase: choose the next gene of minimal rank in
    -- `X - g`, and use the two-gene type10 move.
    have hg_one : X.1.1 g = 1 := by omega
    let restAfterG : Chromosome := X.1.1 - Finsupp.single g 1
    have hrest_ne : restAfterG ≠ 0 := by
      -- If no second gene remains, the level-1 strict rank gap from (17.1)
      -- contradicts the fact that priming a single rank-`2q+3` gene drops
      -- rank by exactly one.
      intro hrest_zero
      have hsingle : X.1.1 = Finsupp.single g 1 := by
        ext h
        by_cases hh : h = g
        · subst hh
          simp [hg_one]
        · have hz : restAfterG h = 0 := by rw [hrest_zero]; rfl
          dsimp [restAfterG] at hz
          rw [Finsupp.single_apply, if_neg (fun heq => hh heq.symm)] at hz
          rw [Finsupp.single_apply, if_neg (fun heq => hh heq.symm)]
          omega
      have hXprime_rank :
          (Chromosome.prime^[1] X.1.1).rank = g.rank - 1 := by
        rw [Function.iterate_one, hsingle, prime_single, one_nsmul,
          rank_ofRank]
      have hXprime_ne : Chromosome.prime^[1] X.1.1 ≠ 0 := by
        have hval :
            Chromosome.prime^[1] X.1.1 = Gene.ofRank (g.rank - 1) g.type := by
          rw [Function.iterate_one, hsingle, prime_single, one_nsmul]
        have hpos : g.rank - 1 ≠ 0 := by
          rw [hg_rank_q]
          omega
        rw [hval, Gene.ofRank_eq_gene' hpos]
        simp
      have hYprime_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
        intro hYzero
        have hle := le_iff_dominates.mp hXY.le 1
        rw [hYzero, map_zero] at hle
        exact hXprime_ne (signature_eq_zero (le_antisymm hle (signature_nonneg _)))
      have hstrict := h17_1 1 (by omega) hYprime_ne
      have hYprime_lt_rank :
          (Chromosome.prime^[1] Y.1.1).rank < Y.1.1.rank :=
        prime_iterate_rank_lt_of_ne_zero (by omega) hYprime_ne
      have hYrank_eq_g : Y.1.1.rank = g.rank := by
        have hXrank_eq_g : X.1.1.rank = g.rank := by
          rw [hsingle, rank_single, one_smul]
        rw [Y.2, ← X.2, hXrank_eq_g]
      rw [hXprime_rank] at hstrict
      rw [hYrank_eq_g] at hYprime_lt_rank
      omega
    obtain ⟨g₂, hg₂_rest, hg₂min⟩ :=
      Mix2LambdaSection17.exists_min_rank_gene hrest_ne
    have hXg₂ : 0 < X.1.1 g₂ := by
      dsimp [restAfterG] at hg₂_rest
      exact lt_of_lt_of_le hg₂_rest (by
        exact Nat.sub_le _ _)
    have hg₂_pol : g₂.type ≠ GeneType.NonPolarized :=
      IsPolarized_def'.mp hXpol g₂ (Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂))
    have hg₂_odd : Odd g₂.rank :=
      Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
        X.1.2 hXg₂ hg₂_pol
    obtain ⟨n, hg₂_rank_raw⟩ := hg₂_odd
    have hq_succ_le_n : q + 1 ≤ n := by
      have hg_le_g₂ := hgmin g₂ hXg₂
      rw [hg_rank_q, hg₂_rank_raw] at hg_le_g₂
      omega
    have hg₂_rank_q : g₂.rank = 2 * n + 1 := hg₂_rank_raw
    -- The previous witness is off by one for type10, so choose the actual
    -- type10 parameter explicitly.
    let n10 := n - 1
    have hn10 : n = n10 + 1 := by omega
    have hq_le_n10 : q ≤ n10 := by omega
    have hg₂_rank_n10 : g₂.rank = 2 * n10 + 3 := by omega
    have hne_g_g₂ : g ≠ g₂ := by
      intro h
      subst h
      dsimp [restAfterG] at hg₂_rest
      simp [hg_one] at hg₂_rest
    have hq_lt_n10 : q < n10 := by
      by_contra hnot
      have hn10q : n10 = q := by omega
      have hrank_eq : g.rank = g₂.rank := by
        rw [hg_rank_q, hg₂_rank_n10, hn10q]
      cases hg_type : g.type <;> cases hg₂_type : g₂.type
      · exact False.elim (hg_ne_np hg_type)
      · exact False.elim (hg_ne_np hg_type)
      · exact False.elim (hg_ne_np hg_type)
      · exact False.elim (hg₂_pol hg₂_type)
      · exact hne_g_g₂ (Gene.ext hrank_eq (by rw [hg_type, hg₂_type]))
      · exact hno_pair ⟨g, g₂, hrank_eq, hg_type, hg₂_type, hgX, hXg₂⟩
      · exact False.elim (hg₂_pol hg₂_type)
      · exact hno_pair ⟨g₂, g, hrank_eq.symm, hg₂_type, hg_type, hXg₂, hgX⟩
      · exact hne_g_g₂ (Gene.ext hrank_eq (by rw [hg_type, hg₂_type]))
    have hmin_rank : ∀ h ∈ X.1.1.support, 2 * q + 3 ≤ h.rank := by
      intro h hh
      have hhpos : 0 < X.1.1 h :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      have hle := hgmin h hhpos
      rw [hg_rank_q] at hle
      exact hle
    have h2nd_rank : ∀ h ∈ restAfterG.support, 2 * n10 + 3 ≤ h.rank := by
      intro h hh
      have hhpos : 0 < restAfterG h :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      have hle := hg₂min h hhpos
      rw [hg₂_rank_n10] at hle
      exact hle
    have hZle :
        (Y10 hq_le_n10 hg_ne_np hg₂_pol).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1) ≤ Y.1.1 := by
      have hgap_pred :
          ((1 : ℚ), (1 : ℚ)) +
              signature (Chromosome.prime^[2 * q + 2] X.1.1) ≤
            signature (Gene.ofRank 1 g.type) +
              signature (Chromosome.prime^[2 * q + 2] Y.1.1) := by
        cases htype : g.type with
        | NonPolarized => exact False.elim (hg_ne_np htype)
        | Positive =>
            exact type10_pred_gap_positive X Y hXY (by
              have hXdrop := KEY_X_full_snd X hmin_rank
                (i := 2 * q) (by omega)
              have hdom := (le_iff_dominates.mp hXY.le (2 * q)).2
              simpa [Sigma.sigma, show 2 * q + 2 = 2 * q + 2 by rfl] using
                seed_snd_lt X Y hr1 (i := 2 * q)
                  (hi := ⟨q, by ring⟩) hXdrop hdom)
        | Negative =>
            exact type10_pred_gap_negative X Y hXY (by
              have hXdrop := KEY_X_full_fst X hmin_rank
                (i := 2 * q) (by omega)
              have hdom := (le_iff_dominates.mp hXY.le (2 * q)).1
              simpa [Sigma.sigma, show 2 * q + 2 = 2 * q + 2 by rfl] using
                seed_fst_lt X Y hr1 (i := 2 * q)
                  (hi := ⟨q, by ring⟩) hXdrop hdom)
      have hfst_base_top :
          (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 <
            (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1 := by
        cases htype : g.type with
        | NonPolarized => exact False.elim (hg_ne_np htype)
        | Positive =>
            have hXdrop := KEY_X_edge_fst_positive X
              (m := 2 * q + 3) (k := 2 * n10 + 3) (gm := g)
              hg_rank_q htype hg_one h2nd_rank (by omega)
            have hXdrop' :
                (Sigma.sigma X.1.1 (2 * q + 2)).1 -
                    (Sigma.sigma X.1.1 (2 * q + 4)).1 =
                  (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                    ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
              simpa [show 2 * q + 3 - 1 = 2 * q + 2 by omega,
                show 2 * q + 3 + 1 = 2 * q + 4 by omega] using hXdrop
            have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).1
            simpa [Sigma.sigma, show 2 * q + 2 + 2 = 2 * q + 4 by omega] using
              seed_fst_lt X Y hr1 (i := 2 * q + 2)
                (hi := ⟨q + 1, by ring⟩) hXdrop' hdom
        | Negative =>
            have hseed :
                (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
                  (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 := by
              have hXdrop := KEY_X_full_fst X hmin_rank
                (i := 2 * q) (by omega)
              have hdom := (le_iff_dominates.mp hXY.le (2 * q)).1
              simpa [Sigma.sigma, show 2 * q + 2 = 2 * q + 2 by rfl] using
                seed_fst_lt X Y hr1 (i := 2 * q)
                  (hi := ⟨q, by ring⟩) hXdrop hdom
            have hwin_one : 2 * q + 2 + 2 * 1 ≤ 2 * n10 + 3 := by omega
            have hstep :=
              window_even_fst_lt X Y hr1 (k := 2 * n10 + 3) (gm := g)
                hg_one h2nd_rank (2 * q + 2) 1 ⟨q + 1, by ring⟩
                hwin_one hseed
            simpa [Sigma.sigma, show 2 * q + 2 + 2 * 1 = 2 * q + 4 by ring]
              using hstep 1 (by omega)
      have hsnd_base_top :
          (signature (Chromosome.prime^[2 * q + 4] X.1.1)).2 <
            (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2 := by
        cases htype : g.type with
        | NonPolarized => exact False.elim (hg_ne_np htype)
        | Positive =>
            have hseed :
                (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
                  (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 := by
              have hXdrop := KEY_X_full_snd X hmin_rank
                (i := 2 * q) (by omega)
              have hdom := (le_iff_dominates.mp hXY.le (2 * q)).2
              simpa [Sigma.sigma, show 2 * q + 2 = 2 * q + 2 by rfl] using
                seed_snd_lt X Y hr1 (i := 2 * q)
                  (hi := ⟨q, by ring⟩) hXdrop hdom
            have hwin_one : 2 * q + 2 + 2 * 1 ≤ 2 * n10 + 3 := by omega
            have hstep :=
              window_even_snd_lt X Y hr1 (k := 2 * n10 + 3) (gm := g)
                hg_one h2nd_rank (2 * q + 2) 1 ⟨q + 1, by ring⟩
                hwin_one hseed
            simpa [Sigma.sigma, show 2 * q + 2 + 2 * 1 = 2 * q + 4 by ring]
              using hstep 1 (by omega)
        | Negative =>
            have hXdrop := KEY_X_edge_snd_negative X
              (m := 2 * q + 3) (k := 2 * n10 + 3) (gm := g)
              hg_rank_q htype hg_one h2nd_rank (by omega)
            have hXdrop' :
                (Sigma.sigma X.1.1 (2 * q + 2)).2 -
                    (Sigma.sigma X.1.1 (2 * q + 4)).2 =
                  (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                    ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
              simpa [show 2 * q + 3 - 1 = 2 * q + 2 by omega,
                show 2 * q + 3 + 1 = 2 * q + 4 by omega] using hXdrop
            have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).2
            simpa [Sigma.sigma, show 2 * q + 2 + 2 = 2 * q + 4 by omega] using
              seed_snd_lt X Y hr1 (i := 2 * q + 2)
                (hi := ⟨q + 1, by ring⟩) hXdrop' hdom
      have hfst_top_even :
          (signature (Chromosome.prime^[2 * n10 + 2] X.1.1)).1 <
            (signature (Chromosome.prime^[2 * n10 + 2] Y.1.1)).1 := by
        let d := n10 - q - 1
        have hwin : 2 * q + 4 + 2 * d ≤ 2 * n10 + 3 := by
          dsimp [d]
          omega
        have hstep :=
          window_even_fst_lt X Y hr1 (k := 2 * n10 + 3) (gm := g)
            hg_one h2nd_rank (2 * q + 4) d ⟨q + 2, by ring⟩ hwin hfst_base_top
        have hidx : 2 * q + 4 + 2 * d = 2 * n10 + 2 := by
          dsimp [d]
          omega
        simpa [Sigma.sigma, hidx] using hstep d (le_refl d)
      have hsnd_top_even :
          (signature (Chromosome.prime^[2 * n10 + 2] X.1.1)).2 <
            (signature (Chromosome.prime^[2 * n10 + 2] Y.1.1)).2 := by
        let d := n10 - q - 1
        have hwin : 2 * q + 4 + 2 * d ≤ 2 * n10 + 3 := by
          dsimp [d]
          omega
        have hstep :=
          window_even_snd_lt X Y hr1 (k := 2 * n10 + 3) (gm := g)
            hg_one h2nd_rank (2 * q + 4) d ⟨q + 2, by ring⟩ hwin hsnd_base_top
        have hidx : 2 * q + 4 + 2 * d = 2 * n10 + 2 := by
          dsimp [d]
          omega
        simpa [Sigma.sigma, hidx] using hstep d (le_refl d)
      have hgap_even_top :
          ((1 : ℚ), (1 : ℚ)) +
              signature (Chromosome.prime^[2 * n10 + 2] X.1.1) ≤
            signature (Chromosome.prime^[2 * n10 + 2] Y.1.1) :=
        Mix2LambdaSection17.one_one_le_of_both_lt X.1.2 Y.1.2
          hfst_top_even hsnd_top_even
      have hgap_mid : ∀ j, 2 * q + 3 ≤ j → j ≤ 2 * n10 + 3 →
          ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1) := by
        intro j hjlo hjhi
        by_cases hjeven : Even j
        · -- Even middle levels: propagate the two strict component gaps
          -- through the window using `h2nd_rank`.
          have hfst_base :
              (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 <
                (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1 := by
            cases htype : g.type with
            | NonPolarized => exact False.elim (hg_ne_np htype)
            | Positive =>
                have hXdrop := KEY_X_edge_fst_positive X
                  (m := 2 * q + 3) (k := 2 * n10 + 3) (gm := g)
                  hg_rank_q htype hg_one h2nd_rank (by omega)
                have hXdrop' :
                    (Sigma.sigma X.1.1 (2 * q + 2)).1 -
                        (Sigma.sigma X.1.1 (2 * q + 4)).1 =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
                  simpa [show 2 * q + 3 - 1 = 2 * q + 2 by omega,
                    show 2 * q + 3 + 1 = 2 * q + 4 by omega] using hXdrop
                have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).1
                simpa [Sigma.sigma, show 2 * q + 2 + 2 = 2 * q + 4 by omega] using
                  seed_fst_lt X Y hr1 (i := 2 * q + 2)
                    (hi := ⟨q + 1, by ring⟩) hXdrop' hdom
            | Negative =>
                have hseed :
                    (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
                      (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 := by
                  have hXdrop := KEY_X_full_fst X hmin_rank
                    (i := 2 * q) (by omega)
                  have hdom := (le_iff_dominates.mp hXY.le (2 * q)).1
                  simpa [Sigma.sigma, show 2 * q + 2 = 2 * q + 2 by rfl] using
                    seed_fst_lt X Y hr1 (i := 2 * q)
                      (hi := ⟨q, by ring⟩) hXdrop hdom
                have hwin_one : 2 * q + 2 + 2 * 1 ≤ 2 * n10 + 3 := by omega
                have hstep :=
                  window_even_fst_lt X Y hr1 (k := 2 * n10 + 3) (gm := g)
                    hg_one h2nd_rank (2 * q + 2) 1 ⟨q + 1, by ring⟩
                    hwin_one hseed
                simpa [Sigma.sigma, show 2 * q + 2 + 2 * 1 = 2 * q + 4 by ring]
                  using hstep 1 (by omega)
          have hsnd_base :
              (signature (Chromosome.prime^[2 * q + 4] X.1.1)).2 <
                (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2 := by
            cases htype : g.type with
            | NonPolarized => exact False.elim (hg_ne_np htype)
            | Positive =>
                have hseed :
                    (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
                      (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 := by
                  have hXdrop := KEY_X_full_snd X hmin_rank
                    (i := 2 * q) (by omega)
                  have hdom := (le_iff_dominates.mp hXY.le (2 * q)).2
                  simpa [Sigma.sigma, show 2 * q + 2 = 2 * q + 2 by rfl] using
                    seed_snd_lt X Y hr1 (i := 2 * q)
                      (hi := ⟨q, by ring⟩) hXdrop hdom
                have hwin_one : 2 * q + 2 + 2 * 1 ≤ 2 * n10 + 3 := by omega
                have hstep :=
                  window_even_snd_lt X Y hr1 (k := 2 * n10 + 3) (gm := g)
                    hg_one h2nd_rank (2 * q + 2) 1 ⟨q + 1, by ring⟩
                    hwin_one hseed
                simpa [Sigma.sigma, show 2 * q + 2 + 2 * 1 = 2 * q + 4 by ring]
                  using hstep 1 (by omega)
            | Negative =>
                have hXdrop := KEY_X_edge_snd_negative X
                  (m := 2 * q + 3) (k := 2 * n10 + 3) (gm := g)
                  hg_rank_q htype hg_one h2nd_rank (by omega)
                have hXdrop' :
                    (Sigma.sigma X.1.1 (2 * q + 2)).2 -
                        (Sigma.sigma X.1.1 (2 * q + 4)).2 =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
                  simpa [show 2 * q + 3 - 1 = 2 * q + 2 by omega,
                    show 2 * q + 3 + 1 = 2 * q + 4 by omega] using hXdrop
                have hdom := (le_iff_dominates.mp hXY.le (2 * q + 2)).2
                simpa [Sigma.sigma, show 2 * q + 2 + 2 = 2 * q + 4 by omega] using
                  seed_snd_lt X Y hr1 (i := 2 * q + 2)
                    (hi := ⟨q + 1, by ring⟩) hXdrop' hdom
          rcases hjeven with ⟨u, hu⟩
          let t := u - (q + 2)
          have hj_eq : j = 2 * q + 4 + 2 * t := by
            rw [hu]
            dsimp [t]
            omega
          let d := n10 - q - 1
          have hwin : 2 * q + 4 + 2 * d ≤ 2 * n10 + 3 := by
            dsimp [d]
            omega
          have ht_le : t ≤ d := by
            rw [hu] at hjhi
            dsimp [t, d]
            omega
          have hfst_window :=
            window_even_fst_lt X Y hr1 (k := 2 * n10 + 3) (gm := g)
              hg_one h2nd_rank (2 * q + 4) d ⟨q + 2, by ring⟩ hwin hfst_base
          have hsnd_window :=
            window_even_snd_lt X Y hr1 (k := 2 * n10 + 3) (gm := g)
              hg_one h2nd_rank (2 * q + 4) d ⟨q + 2, by ring⟩ hwin hsnd_base
          exact Mix2LambdaSection17.one_one_le_of_both_lt X.1.2 Y.1.2
            (by simpa [Sigma.sigma, hj_eq] using hfst_window t ht_le)
            (by simpa [Sigma.sigma, hj_eq] using hsnd_window t ht_le)
        · exact type10_mid_gap_odd_of_Y_ne X Y h17_1 hjeven (by omega) (by
            -- Odd middle levels reduce to the nonvanishing side condition for
            -- applying (17.1).
            by_cases hjtop : j = 2 * n10 + 3
            · subst j
              intro hYzero
              have hYtop_rank_le :
                  (Chromosome.prime^[2 * n10 + 2] Y.1.1).rank ≤
                    Y.1.1.rank - Y.1.1.prime.rank := by
                have hdrop :=
                  Mix2LambdaSection17.rank_prime_iterate_drop_le_zero
                    Y.1.1 (2 * n10 + 2)
                simpa [show 2 * n10 + 2 + 1 = 2 * n10 + 3 by omega,
                  hYzero] using hdrop
              have hrank_top_gap :
                  (Chromosome.prime^[2 * n10 + 2] X.1.1).rank + 2 ≤
                    (Chromosome.prime^[2 * n10 + 2] Y.1.1).rank := by
                have hsumX :
                    (signature (Chromosome.prime^[2 * n10 + 2] X.1.1)).1 +
                        (signature (Chromosome.prime^[2 * n10 + 2] X.1.1)).2 =
                      ((Chromosome.prime^[2 * n10 + 2] X.1.1).rank : ℚ) :=
                  signature_sum_eq_rank
                have hsumY :
                    (signature (Chromosome.prime^[2 * n10 + 2] Y.1.1)).1 +
                        (signature (Chromosome.prime^[2 * n10 + 2] Y.1.1)).2 =
                      ((Chromosome.prime^[2 * n10 + 2] Y.1.1).rank : ℚ) :=
                  signature_sum_eq_rank
                have hfst := hgap_even_top.1
                have hsnd := hgap_even_top.2
                simp only [Prod.fst_add, Prod.snd_add] at hfst hsnd
                have hq :
                    ((Chromosome.prime^[2 * n10 + 2] X.1.1).rank : ℚ) + 2 ≤
                      ((Chromosome.prime^[2 * n10 + 2] Y.1.1).rank : ℚ) := by
                  linarith
                exact_mod_cast hq
              have hXtop_eq_rest :
                  Chromosome.prime^[2 * n10 + 2] X.1.1 =
                    Chromosome.prime^[2 * n10 + 2] restAfterG := by
                exact prime_iterate_eq_sub_single_of_rank_le hg_one (by
                  rw [hg_rank_q]
                  omega)
              have hrest_total_survives :
                  (Chromosome.prime^[2 * n10 + 2] restAfterG).sum (fun _ n => n) =
                    restAfterG.sum (fun _ n => n) := by
                exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
                  restAfterG (2 * n10 + 2) (by
                    intro h hh
                    have hle := h2nd_rank h hh
                    omega)
              have hXtop_total :
                  (Chromosome.prime^[2 * n10 + 2] X.1.1).sum (fun _ n => n) =
                    X.1.1.sum (fun _ n => n) - 1 := by
                rw [hXtop_eq_rest, hrest_total_survives]
                have hrest := totalMult_sub_single_one hg_one
                rw [← hrest]
                change restAfterG.sum (fun _ n => n) =
                  (restAfterG.sum (fun _ n => n) + 1) - 1
                omega
              have hXtop_rank_ge :
                  X.1.1.sum (fun _ n => n) - 1 ≤
                    (Chromosome.prime^[2 * n10 + 2] X.1.1).rank := by
                have hle :=
                  totalMult_le_rank (Chromosome.prime^[2 * n10 + 2] X.1.1)
                rwa [hXtop_total] at hle
              have hXtotal_eq_drop :
                  X.1.1.sum (fun _ n => n) =
                    X.1.1.rank - X.1.1.prime.rank := by
                have h := Mix2LambdaSection17.rank_eq_prime_rank_add_totalMult X.1.1
                omega
              have hr1' : X.1.1.prime.rank < Y.1.1.prime.rank := by
                simpa [Function.iterate_one] using hr1
              have hrank_eq : X.1.1.rank = Y.1.1.rank := by
                rw [X.2, Y.2]
              have hdrop_gap :
                  Y.1.1.rank - Y.1.1.prime.rank + 1 ≤
                    X.1.1.rank - X.1.1.prime.rank := by
                omega
              omega
            · have hjlt : j < 2 * n10 + 3 := by omega
              have hXj_ne : Chromosome.prime^[j] X.1.1 ≠ 0 := by
                intro hzero
                have hall :=
                  (Chromosome.prime_iterate_eq_zero_rank_le
                    (X := X.1.1) (k := j)).2 hzero
                have hg₂_support : g₂ ∈ X.1.1.support :=
                  Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂)
                have hle_g₂ := hall g₂ hg₂_support
                rw [hg₂_rank_n10] at hle_g₂
                omega
              intro hYzero
              have hle := le_iff_dominates.mp hXY.le j
              rw [hYzero, map_zero] at hle
              exact hXj_ne
                (signature_eq_zero (le_antisymm hle (signature_nonneg _))))
      have hgap_succ :
          signature (Gene.ofRank 1 g₂.type) +
              signature (Chromosome.prime^[2 * n10 + 4] X.1.1) ≤
            signature (Chromosome.prime^[2 * n10 + 4] Y.1.1) := by
        cases htype : g₂.type with
        | NonPolarized => exact False.elim (hg₂_pol htype)
        | Positive =>
            simpa [htype, show 2 * (n10 + 1) + 2 = 2 * n10 + 4 by omega] using
              type16_succ_gap_positive X Y hXY (p := n10 + 1) (by
                have hWpos :
                    ∀ z ∈ (Chromosome.prime^[2 * n10 + 1] X.1.1).support,
                      2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
                  intro z hz
                  have hzpos : 0 < (Chromosome.prime^[2 * n10 + 1] X.1.1) z :=
                    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
                  let z0 : Gene :=
                    ⟨z.rank + (2 * n10 + 1), z.type,
                      Nat.le_add_right_of_le z.rank_pos⟩
                  have hz0X : 0 < X.1.1 z0 := by
                    have hcoeff := prime_iterate_coeff (2 * n10 + 1) X.1.1 z
                    change (Chromosome.prime^[2 * n10 + 1] X.1.1) z = X.1.1 z0 at hcoeff
                    rwa [← hcoeff]
                  have hz0_ne_g : z0 ≠ g := by
                    intro hzg
                    have hrank := congrArg Gene.rank hzg
                    dsimp [z0] at hrank
                    rw [hg_rank_q] at hrank
                    have zpos := z.rank_pos
                    omega
                  have hz0_rest : 0 < restAfterG z0 := by
                    dsimp [restAfterG]
                    simp [hz0_ne_g.symm, hz0X]
                  have hz0_rank_le :=
                    h2nd_rank z0 (Finsupp.mem_support_iff.mpr (ne_of_gt hz0_rest))
                  constructor
                  · dsimp [z0] at hz0_rank_le
                    omega
                  · intro hz_rank
                    have hz0_support : z0 ∈ X.1.1.support :=
                      Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
                    have hz0_rank_eq : z0.rank = g₂.rank := by
                      dsimp [z0]
                      rw [hz_rank, hg₂_rank_n10]
                      omega
                    cases hz_type : z.type with
                    | NonPolarized =>
                        have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
                        exact False.elim (hpol0 (by simpa [z0] using hz_type))
                    | Positive => rfl
                    | Negative =>
                        exact False.elim (hno_pair ⟨g₂, z0, hz0_rank_eq.symm,
                          htype, by simpa [z0] using hz_type, hXg₂, hz0X⟩)
                have hXdrop_raw :=
                  edge_drop_fst_eq_totalMult_positive_iterate
                    (W := X.1.1) (i := 2 * n10 + 1) hWpos
                have hWsum_nat :
                    (Chromosome.prime^[2 * n10 + 1] X.1.1).sum (fun _ n => n) =
                      restAfterG.sum (fun _ n => n) := by
                  rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by
                    rw [hg_rank_q]
                    omega)]
                  exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
                    restAfterG (2 * n10 + 1) (by
                      intro h hh
                      have hle := h2nd_rank h hh
                      omega)
                have hWsum :
                    (Chromosome.prime^[2 * n10 + 1] X.1.1).sum (fun _ n => (n : ℚ)) =
                      restAfterG.sum (fun _ n => (n : ℚ)) := by
                  exact_mod_cast hWsum_nat
                have hrest :
                    restAfterG.sum (fun _ n => (n : ℚ)) =
                      X.1.1.sum (fun _ n => (n : ℚ)) - 1 := by
                  have hrest_nat := totalMult_sub_single_one hg_one
                  have hrest_q := congrArg (fun t : ℕ => (t : ℚ)) hrest_nat
                  norm_num at hrest_q
                  linarith
                have hD :
                    X.1.1.sum (fun _ n => (n : ℚ)) =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
                  have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
                      (X.1.1.rank : ℚ) := by
                    simpa [Sigma.sigma] using (@signature_sum_eq_rank X.1.1)
                  have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
                      (X.1.1.prime.rank : ℚ) := by
                    have := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
                    simpa [Sigma.sigma, Function.iterate_one] using this
                  have hcells := MixLambdaPi.cells (Z := X.1.1)
                  linarith
                have hXdrop :
                    (Sigma.sigma X.1.1 (2 * n10 + 2)).1 -
                        (Sigma.sigma X.1.1 (2 * n10 + 4)).1 =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
                  have htmp := hXdrop_raw
                  rw [show 1 + (2 * n10 + 1) = 2 * n10 + 2 by omega,
                    show 3 + (2 * n10 + 1) = 2 * n10 + 4 by omega] at htmp
                  linarith
                have hYdrop :=
                  KEY_Y_fst X Y hr1 (i := 2 * n10 + 2) ⟨n10 + 1, by ring⟩
                have hsucc :
                    (signature (Chromosome.prime^[2 * n10 + 4] X.1.1)).1 <
                      (signature (Chromosome.prime^[2 * n10 + 4] Y.1.1)).1 := by
                  have htop :
                      (Sigma.sigma X.1.1 (2 * n10 + 2)).1 <
                        (Sigma.sigma Y.1.1 (2 * n10 + 2)).1 := by
                    simpa [Sigma.sigma] using hfst_top_even
                  have hYdrop' :
                      (Sigma.sigma Y.1.1 (2 * n10 + 2)).1 -
                          (Sigma.sigma Y.1.1 (2 * n10 + 4)).1 ≤
                        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
                    simpa [show 2 * n10 + 2 + 2 = 2 * n10 + 4 by omega] using hYdrop
                  simpa [Sigma.sigma] using (by
                    linarith : (Sigma.sigma X.1.1 (2 * n10 + 4)).1 <
                      (Sigma.sigma Y.1.1 (2 * n10 + 4)).1)
                simpa [show 2 * (n10 + 1) + 2 = 2 * n10 + 4 by omega] using hsucc)
        | Negative =>
            simpa [htype, show 2 * (n10 + 1) + 2 = 2 * n10 + 4 by omega] using
              type16_succ_gap_negative X Y hXY (p := n10 + 1) (by
                have hWneg :
                    ∀ z ∈ (Chromosome.prime^[2 * n10 + 1] X.1.1).support,
                      2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
                  intro z hz
                  have hzpos : 0 < (Chromosome.prime^[2 * n10 + 1] X.1.1) z :=
                    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
                  let z0 : Gene :=
                    ⟨z.rank + (2 * n10 + 1), z.type,
                      Nat.le_add_right_of_le z.rank_pos⟩
                  have hz0X : 0 < X.1.1 z0 := by
                    have hcoeff := prime_iterate_coeff (2 * n10 + 1) X.1.1 z
                    change (Chromosome.prime^[2 * n10 + 1] X.1.1) z = X.1.1 z0 at hcoeff
                    rwa [← hcoeff]
                  have hz0_ne_g : z0 ≠ g := by
                    intro hzg
                    have hrank := congrArg Gene.rank hzg
                    dsimp [z0] at hrank
                    rw [hg_rank_q] at hrank
                    have zpos := z.rank_pos
                    omega
                  have hz0_rest : 0 < restAfterG z0 := by
                    dsimp [restAfterG]
                    simp [hz0_ne_g.symm, hz0X]
                  have hz0_rank_le :=
                    h2nd_rank z0 (Finsupp.mem_support_iff.mpr (ne_of_gt hz0_rest))
                  constructor
                  · dsimp [z0] at hz0_rank_le
                    omega
                  · intro hz_rank
                    have hz0_support : z0 ∈ X.1.1.support :=
                      Finsupp.mem_support_iff.mpr (ne_of_gt hz0X)
                    have hz0_rank_eq : z0.rank = g₂.rank := by
                      dsimp [z0]
                      rw [hz_rank, hg₂_rank_n10]
                      omega
                    cases hz_type : z.type with
                    | NonPolarized =>
                        have hpol0 := IsPolarized_def'.mp hXpol z0 hz0_support
                        exact False.elim (hpol0 (by simpa [z0] using hz_type))
                    | Positive =>
                        exact False.elim (hno_pair ⟨z0, g₂, hz0_rank_eq,
                          by simpa [z0] using hz_type, htype, hz0X, hXg₂⟩)
                    | Negative => rfl
                have hXdrop_raw :=
                  edge_drop_snd_eq_totalMult_negative_iterate
                    (W := X.1.1) (i := 2 * n10 + 1) hWneg
                have hWsum_nat :
                    (Chromosome.prime^[2 * n10 + 1] X.1.1).sum (fun _ n => n) =
                      restAfterG.sum (fun _ n => n) := by
                  rw [prime_iterate_eq_sub_single_of_rank_le hg_one (by
                    rw [hg_rank_q]
                    omega)]
                  exact Mix2LambdaSection17.totalMult_prime_iterate_eq_of_lt_minRank
                    restAfterG (2 * n10 + 1) (by
                      intro h hh
                      have hle := h2nd_rank h hh
                      omega)
                have hWsum :
                    (Chromosome.prime^[2 * n10 + 1] X.1.1).sum (fun _ n => (n : ℚ)) =
                      restAfterG.sum (fun _ n => (n : ℚ)) := by
                  exact_mod_cast hWsum_nat
                have hrest :
                    restAfterG.sum (fun _ n => (n : ℚ)) =
                      X.1.1.sum (fun _ n => (n : ℚ)) - 1 := by
                  have hrest_nat := totalMult_sub_single_one hg_one
                  have hrest_q := congrArg (fun t : ℕ => (t : ℚ)) hrest_nat
                  norm_num at hrest_q
                  linarith
                have hD :
                    X.1.1.sum (fun _ n => (n : ℚ)) =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
                  have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
                      (X.1.1.rank : ℚ) := by
                    simpa [Sigma.sigma] using (@signature_sum_eq_rank X.1.1)
                  have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
                      (X.1.1.prime.rank : ℚ) := by
                    have := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
                    simpa [Sigma.sigma, Function.iterate_one] using this
                  have hcells := MixLambdaPi.cells (Z := X.1.1)
                  linarith
                have hXdrop :
                    (Sigma.sigma X.1.1 (2 * n10 + 2)).2 -
                        (Sigma.sigma X.1.1 (2 * n10 + 4)).2 =
                      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
                  have htmp := hXdrop_raw
                  rw [show 1 + (2 * n10 + 1) = 2 * n10 + 2 by omega,
                    show 3 + (2 * n10 + 1) = 2 * n10 + 4 by omega] at htmp
                  linarith
                have hYdrop :=
                  KEY_Y_snd X Y hr1 (i := 2 * n10 + 2) ⟨n10 + 1, by ring⟩
                have hsucc :
                    (signature (Chromosome.prime^[2 * n10 + 4] X.1.1)).2 <
                      (signature (Chromosome.prime^[2 * n10 + 4] Y.1.1)).2 := by
                  have htop :
                      (Sigma.sigma X.1.1 (2 * n10 + 2)).2 <
                        (Sigma.sigma Y.1.1 (2 * n10 + 2)).2 := by
                    simpa [Sigma.sigma] using hsnd_top_even
                  have hYdrop' :
                      (Sigma.sigma Y.1.1 (2 * n10 + 2)).2 -
                          (Sigma.sigma Y.1.1 (2 * n10 + 4)).2 ≤
                        (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                          ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
                    simpa [show 2 * n10 + 2 + 2 = 2 * n10 + 4 by omega] using hYdrop
                  simpa [Sigma.sigma] using (by
                    linarith : (Sigma.sigma X.1.1 (2 * n10 + 4)).2 <
                      (Sigma.sigma Y.1.1 (2 * n10 + 4)).2)
                simpa [show 2 * (n10 + 1) + 2 = 2 * n10 + 4 by omega] using hsucc)
      exact type10_pair_target_add_rest_le_of_gaps hg_ne_np hg₂_pol hq_le_n10
        X Y hXY g g₂ rfl rfl hg_rank_q hg₂_rank_n10 (by omega) (by omega)
        hne_g_g₂ hgap_pred hgap_mid hgap_succ
    exact exists_mutation_le_type10_of_genes hg_ne_np hg₂_pol hq_le_n10
      X Y g g₂ rfl rfl hg_rank_q hg₂_rank_n10 (by omega) (by omega) hne_g_g₂ hZle


end Mix2LambdaPi
