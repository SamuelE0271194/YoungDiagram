import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankGeFour
import YoungDiagram.Theorem6.MixPi2Lambda.Case34Gaps

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Label 4 no-pair rank-ge-four solver

The Label 4 (`Mix (Pi, 2 • Lambda)`) analogue of
`Mix2LambdaPi.exists_mutation_le_no_pair_rank_ge_three`, i.e. §17 Case 1
(minimal polarized gene has even rank `2*p+2` with `0 < p`, so rank `≥ 4`).
Parity roles are flipped relative to Label 3: polarized genes sit at even rank
and the reduced §17 symmetric level is even.  All gap/window infrastructure it
needs already exists in the Label 4 `Window` / `Case34Gaps` / `Case34Helpers`
layer with the same names as Label 3.

The Label-3 proof is one ~930-line block that branches on `2 ≤ X g`; we mirror
that split into a diagonal branch and a multiplicity-one branch. -/

-- Diagonal branch of §17 Case 1 for Label 4: the minimal polarized gene has
-- multiplicity `≥ 2`, so we use the diagonal move
-- `2 g^ε(2q+4) → g^ε(2q+2) + g^ε(2q+6)`.
-- Mirrors lines 51–313 of Label-3 `exists_mutation_le_no_pair_rank_ge_three`.
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
  sorry

-- Multiplicity-one branch of §17 Case 1 for Label 4: the minimal polarized
-- gene has multiplicity `1`; extract the next minimal-rank gene `g₂` and use
-- the type10 pair move.
-- Mirrors lines 314–938 of Label-3 `exists_mutation_le_no_pair_rank_ge_three`.
set_option maxHeartbeats 1200000 in
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
  obtain ⟨q, hg_rank_q, hmin_rank, hXprime1_ne, hYprime1_ne, hr1⟩ :=
    no_pair_rank_ge_four_window_data X Y hXY h17_1 g hgX hgmin hg_rank hp
  have hg_one : X.1.1 g = 1 := by omega
  let restAfterG : Chromosome := X.1.1 - Finsupp.single g 1
  have hrest_ne : restAfterG ≠ 0 := by
    intro hrest_zero
    have hsingle : X.1.1 = Finsupp.single g 1 := by
      ext h
      by_cases hh : h = g
      · subst hh; simp [hg_one]
      · have hz : restAfterG h = 0 := by rw [hrest_zero]; rfl
        dsimp [restAfterG] at hz
        rw [Finsupp.single_apply, if_neg (fun heq => hh heq.symm)] at hz
        rw [Finsupp.single_apply, if_neg (fun heq => hh heq.symm)]
        omega
    have hXprime_rank : (Chromosome.prime^[1] X.1.1).rank = g.rank - 1 := by
      rw [Function.iterate_one, hsingle, prime_single, one_nsmul, rank_ofRank]
    have hstrict := h17_1 1 (by omega) hYprime1_ne
    have hYprime_lt_rank : (Chromosome.prime^[1] Y.1.1).rank < Y.1.1.rank :=
      prime_iterate_rank_lt_of_ne_zero (by omega) hYprime1_ne
    have hYrank_eq_g : Y.1.1.rank = g.rank := by
      rw [Y.2, ← X.2, hsingle, rank_single, one_smul]
    rw [hXprime_rank] at hstrict
    rw [hYrank_eq_g] at hYprime_lt_rank
    omega
  obtain ⟨g₂, hg₂_rest, hg₂min⟩ :=
    Mix2LambdaSection17.exists_min_rank_gene hrest_ne
  have hXg₂ : 0 < X.1.1 g₂ := by
    dsimp [restAfterG] at hg₂_rest
    exact lt_of_lt_of_le hg₂_rest (Nat.sub_le _ _)
  have hg₂_pol : g₂.type ≠ GeneType.NonPolarized :=
    IsPolarized_def'.mp hXpol g₂ (Finsupp.mem_support_iff.mpr (ne_of_gt hXg₂))
  have hg₂_even : Even g₂.rank :=
    Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
      X.1.2 hXg₂ hg₂_pol
  obtain ⟨n, hg₂_rank_raw⟩ := hg₂_even
  have hg₂_rank_2n : g₂.rank = 2 * n := by omega
  have hq_succ_le_n : q + 2 ≤ n := by
    have hg_le_g₂ := hgmin g₂ hXg₂
    rw [hg_rank_q, hg₂_rank_2n] at hg_le_g₂
    omega
  let n10 := n - 2
  have hn10 : n = n10 + 2 := by omega
  have hq_le_n10 : q ≤ n10 := by
    have hg_le_g₂ := hgmin g₂ hXg₂
    rw [hg_rank_q, hg₂_rank_2n] at hg_le_g₂
    omega
  have hg₂_rank_n10 : g₂.rank = 2 * n10 + 4 := by
    rw [hg₂_rank_2n, hn10]
    ring
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
    · exact False.elim (hg_pol hg_type)
    · exact False.elim (hg_pol hg_type)
    · exact False.elim (hg_pol hg_type)
    · exact False.elim (hg₂_pol hg₂_type)
    · exact hne_g_g₂ (Gene.ext hrank_eq (by rw [hg_type, hg₂_type]))
    · exact hno_pair ⟨g, g₂, hrank_eq, hg_type, hg₂_type, hgX, hXg₂⟩
    · exact False.elim (hg₂_pol hg₂_type)
    · exact hno_pair ⟨g₂, g, hrank_eq.symm, hg₂_type, hg_type, hXg₂, hgX⟩
    · exact hne_g_g₂ (Gene.ext hrank_eq (by rw [hg_type, hg₂_type]))
  have h2nd_rank : ∀ h ∈ restAfterG.support, 2 * n10 + 4 ≤ h.rank := by
    intro h hh
    have hhpos : 0 < restAfterG h :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have hle := hg₂min h hhpos
    rwa [hg₂_rank_n10] at hle
  have hZle :
      (Y10 (show q + 1 ≤ n10 + 1 from by omega) hg_pol hg₂_pol).1 +
          (X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1) ≤ Y.1.1 := by
    have hgap_pred :
        ((1 : ℚ), (1 : ℚ)) +
            signature (Chromosome.prime^[2 * q + 3] X.1.1) ≤
          signature (Gene.ofRank 1 g.type) +
            signature (Chromosome.prime^[2 * q + 3] Y.1.1) := by
      cases htype : g.type with
      | NonPolarized => exact False.elim (hg_pol htype)
      | Positive =>
          have hXdrop_snd : (Sigma.sigma X.1.1 (2 * q + 1)).2 -
              (Sigma.sigma X.1.1 (2 * q + 3)).2 =
            (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
              ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) :=
            KEY_X_full_snd X hmin_rank (i := 2 * q + 1) (by omega)
          have hdom_snd : (Sigma.sigma X.1.1 (2 * q + 1)).2 ≤
            (Sigma.sigma Y.1.1 (2 * q + 1)).2 :=
            (le_iff_dominates.mp hXY.le (2 * q + 1)).2
          have hodd : ¬ Even (2 * q + 1) :=
            Nat.not_even_iff_odd.mpr ⟨q, by ring⟩
          have hseed : (signature (Chromosome.prime^[2 * q + 3] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).2 := by
            have := seed_snd_lt_odd X Y hr1 (i := 2 * q + 1) hodd
              hXdrop_snd hdom_snd
            simpa [Sigma.sigma] using this
          exact type10_pred_gap_positive X Y hXY hseed
      | Negative =>
          have hXdrop_fst : (Sigma.sigma X.1.1 (2 * q + 1)).1 -
              (Sigma.sigma X.1.1 (2 * q + 3)).1 =
            (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
              ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) :=
            KEY_X_full_fst X hmin_rank (i := 2 * q + 1) (by omega)
          have hdom_fst : (Sigma.sigma X.1.1 (2 * q + 1)).1 ≤
            (Sigma.sigma Y.1.1 (2 * q + 1)).1 :=
            (le_iff_dominates.mp hXY.le (2 * q + 1)).1
          have hodd : ¬ Even (2 * q + 1) :=
            Nat.not_even_iff_odd.mpr ⟨q, by ring⟩
          have hseed : (signature (Chromosome.prime^[2 * q + 3] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * q + 3] Y.1.1)).1 := by
            have := seed_fst_lt_odd X Y hr1 (i := 2 * q + 1) hodd
              hXdrop_fst hdom_fst
            simpa [Sigma.sigma] using this
          exact type10_pred_gap_negative X Y hXY hseed
    have hfst_base_top :
        (signature (Chromosome.prime^[2 * q + 4] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).1 := by
      cases htype : g.type with
      | NonPolarized => exact False.elim (hg_pol htype)
      | Positive =>
          have hXdrop := KEY_X_edge_fst_positive X
            (m := 2 * q + 4) (k := 2 * n10 + 4) (gm := g)
            hg_rank_q htype hg_one h2nd_rank (by omega)
          have hXdrop' :
              (Sigma.sigma X.1.1 (2 * q + 3)).1 -
                  (Sigma.sigma X.1.1 (2 * q + 5)).1 =
                (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                  ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
            simpa [show 2 * q + 4 - 1 = 2 * q + 3 by omega,
              show 2 * q + 4 + 1 = 2 * q + 5 by omega] using hXdrop
          have hdom := (le_iff_dominates.mp hXY.le (2 * q + 3)).1
          simpa [Sigma.sigma, show 2 * q + 3 + 2 = 2 * q + 5 by omega] using
            seed_fst_lt X Y hr1 (i := 2 * q + 3)
              (hi := ⟨q + 2, by ring⟩) hXdrop' hdom
      | Negative =>
          have hseed :
              (signature (Chromosome.prime^[2 * q + 2] X.1.1)).1 <
                (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).1 := by
            have hXdrop := KEY_X_full_fst X hmin_rank
              (i := 2 * q) (by omega)
            have hdom := (le_iff_dominates.mp hXY.le (2 * q)).1
            simpa [Sigma.sigma] using
              seed_fst_lt X Y hr1 (i := 2 * q)
                (hi := ⟨q, by ring⟩) hXdrop hdom
          have hwin_one : 2 * q + 2 + 2 * 1 ≤ 2 * n10 + 4 := by omega
          have hstep :=
            window_even_fst_lt X Y hr1 (k := 2 * n10 + 4) (gm := g)
              hg_one h2nd_rank (2 * q + 2) 1 ⟨q + 1, by ring⟩
              hwin_one hseed
          simpa [Sigma.sigma, show 2 * q + 2 + 2 * 1 = 2 * q + 4 by ring]
            using hstep 1 (by omega)
    have hsnd_base_top :
        (signature (Chromosome.prime^[2 * q + 4] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * q + 4] Y.1.1)).2 := by
      cases htype : g.type with
      | NonPolarized => exact False.elim (hg_pol htype)
      | Positive =>
          have hseed :
              (signature (Chromosome.prime^[2 * q + 2] X.1.1)).2 <
                (signature (Chromosome.prime^[2 * q + 2] Y.1.1)).2 := by
            have hXdrop := KEY_X_full_snd X hmin_rank
              (i := 2 * q) (by omega)
            have hdom := (le_iff_dominates.mp hXY.le (2 * q)).2
            simpa [Sigma.sigma] using
              seed_snd_lt X Y hr1 (i := 2 * q)
                (hi := ⟨q, by ring⟩) hXdrop hdom
          have hwin_one : 2 * q + 2 + 2 * 1 ≤ 2 * n10 + 4 := by omega
          have hstep :=
            window_even_snd_lt X Y hr1 (k := 2 * n10 + 4) (gm := g)
              hg_one h2nd_rank (2 * q + 2) 1 ⟨q + 1, by ring⟩
              hwin_one hseed
          simpa [Sigma.sigma, show 2 * q + 2 + 2 * 1 = 2 * q + 4 by ring]
            using hstep 1 (by omega)
      | Negative =>
          have hXdrop := KEY_X_edge_snd_negative X
            (m := 2 * q + 4) (k := 2 * n10 + 4) (gm := g)
            hg_rank_q htype hg_one h2nd_rank (by omega)
          have hXdrop' :
              (Sigma.sigma X.1.1 (2 * q + 3)).2 -
                  (Sigma.sigma X.1.1 (2 * q + 5)).2 =
                (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
                  ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
            simpa [show 2 * q + 4 - 1 = 2 * q + 3 by omega,
              show 2 * q + 4 + 1 = 2 * q + 5 by omega] using hXdrop
          have hdom := (le_iff_dominates.mp hXY.le (2 * q + 3)).2
          simpa [Sigma.sigma, show 2 * q + 3 + 2 = 2 * q + 5 by omega] using
            seed_snd_lt X Y hr1 (i := 2 * q + 3)
              (hi := ⟨q + 2, by ring⟩) hXdrop' hdom
    have hfst_top_even :
        (signature (Chromosome.prime^[2 * n10 + 4] X.1.1)).1 <
          (signature (Chromosome.prime^[2 * n10 + 4] Y.1.1)).1 := by
      let d := n10 - q - 1
      have hwin : 2 * q + 4 + 2 * d ≤ 2 * n10 + 4 := by
        dsimp [d]
        omega
      have hstep :=
        window_even_fst_lt X Y hr1 (k := 2 * n10 + 4) (gm := g)
          hg_one h2nd_rank (2 * q + 4) d ⟨q + 2, by ring⟩ hwin hfst_base_top
      have hidx : 2 * q + 4 + 2 * d = 2 * n10 + 4 := by
        dsimp [d]
        omega
      simpa [Sigma.sigma, hidx] using hstep d (le_refl d)
    have hsnd_top_even :
        (signature (Chromosome.prime^[2 * n10 + 4] X.1.1)).2 <
          (signature (Chromosome.prime^[2 * n10 + 4] Y.1.1)).2 := by
      let d := n10 - q - 1
      have hwin : 2 * q + 4 + 2 * d ≤ 2 * n10 + 4 := by
        dsimp [d]
        omega
      have hstep :=
        window_even_snd_lt X Y hr1 (k := 2 * n10 + 4) (gm := g)
          hg_one h2nd_rank (2 * q + 4) d ⟨q + 2, by ring⟩ hwin hsnd_base_top
      have hidx : 2 * q + 4 + 2 * d = 2 * n10 + 4 := by
        dsimp [d]
        omega
      simpa [Sigma.sigma, hidx] using hstep d (le_refl d)
    have hgap_even_top :
        ((1 : ℚ), (1 : ℚ)) +
            signature (Chromosome.prime^[2 * n10 + 4] X.1.1) ≤
          signature (Chromosome.prime^[2 * n10 + 4] Y.1.1) :=
      Mix2LambdaSection17.one_one_le_of_both_lt X.1.2 Y.1.2
        hfst_top_even hsnd_top_even
    sorry
  exact exists_mutation_le_type10_of_genes hg_pol hg₂_pol
    (show q + 1 ≤ n10 + 1 from by omega) X Y g g₂ rfl rfl
    (by simpa [show 2 * (q + 1) + 2 = 2 * q + 4 by omega] using hg_rank_q)
    (by simpa [show 2 * (n10 + 1) + 2 = 2 * n10 + 4 by omega] using hg₂_rank_n10)
    (by omega) (by omega) hne_g_g₂ hZle

-- §17 Case 1 (rank `≥ 4`) solver for Label 4, dispatching on the multiplicity
-- of the minimal polarized gene.
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
