import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPair

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair rank-ge-four setup

This is the first reusable slice of the Label 4 analogue of
`Mix2LambdaPi.Case34NoPairRankGeThree`: after the minimal polarized gene is known
to have rank at least `4`, the reduced §17 hypothesis gives the first strict
rank gap at level `1`.
-/

/-- First nonvanishing and strict-rank gap for the Label 4 no-pair rank-ge-four
branch.  The minimal polarized gene has rank `2*p+2` with `0<p`, hence every
gene of `X` has rank at least `4`; in particular `prime^[1] X` is nonzero.
Dominance transfers nonvanishing to `prime^[1] Y`, and (17.1) gives the strict
rank gap. -/
lemma no_pair_rank_ge_four_first_gap
    {m p : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_rank : g.rank = 2 * p + 2) (hp : 0 < p) :
    Chromosome.prime^[1] X.1.1 ≠ 0 ∧
      Chromosome.prime^[1] Y.1.1 ≠ 0 ∧
      (Chromosome.prime^[1] X.1.1).rank <
        (Chromosome.prime^[1] Y.1.1).rank := by
  have hXne : X.1.1 ≠ 0 := by
    intro hzero
    have : X.1.1 g = 0 := by rw [hzero]; rfl
    omega
  have hmin_ge_four : 4 ≤ g.rank :=
    no_pair_min_gene_rank_ge_four (X := X) hg_rank hp
  have hXprime1_ne : Chromosome.prime^[1] X.1.1 ≠ 0 := by
    change X.1.1.prime ≠ 0
    apply prime_ne_zero_of_rank_ge_two hXne
    intro h hh
    have hhpos : 0 < X.1.1 h :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have hle := hgmin h hhpos
    omega
  have hYprime1_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
    intro hYzero
    have hle := le_iff_dominates.mp hXY.le 1
    rw [hYzero, map_zero] at hle
    exact hXprime1_ne (signature_eq_zero (le_antisymm hle (signature_nonneg _)))
  exact ⟨hXprime1_ne, hYprime1_ne, h17_1 1 (by omega) hYprime1_ne⟩

/-- Normalized window data for the Label 4 no-pair rank-ge-four branch.

The minimal rank is rewritten from `2*p+2` with `0<p` to `2*q+4`, matching the
natural Label 4 window endpoints.  The lemma also packages the minimal-rank
lower bound for every support gene of `X` and the first strict rank gap from
`no_pair_rank_ge_four_first_gap`. -/
lemma no_pair_rank_ge_four_window_data
    {m p : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_rank : g.rank = 2 * p + 2) (hp : 0 < p) :
    ∃ q : ℕ,
      g.rank = 2 * q + 4 ∧
      (∀ h ∈ X.1.1.support, 2 * q + 4 ≤ h.rank) ∧
      Chromosome.prime^[1] X.1.1 ≠ 0 ∧
      Chromosome.prime^[1] Y.1.1 ≠ 0 ∧
      (Chromosome.prime^[1] X.1.1).rank <
        (Chromosome.prime^[1] Y.1.1).rank := by
  let q := p - 1
  have hpq : p = q + 1 := by omega
  have hg_rank_q : g.rank = 2 * q + 4 := by
    rw [hg_rank, hpq]
    ring
  have hmin_rank : ∀ h ∈ X.1.1.support, 2 * q + 4 ≤ h.rank := by
    intro h hh
    have hhpos : 0 < X.1.1 h :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
    have hle := hgmin h hhpos
    rwa [hg_rank_q] at hle
  obtain ⟨hX1, hY1, hr1⟩ :=
    no_pair_rank_ge_four_first_gap X Y hXY h17_1 g hgX hgmin hg_rank hp
  exact ⟨q, hg_rank_q, hmin_rank, hX1, hY1, hr1⟩

end MixPi2Lambda
