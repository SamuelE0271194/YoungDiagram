import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankGeFour

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair rank split

This dispatcher-ready setup keeps the minimal-gene bookkeeping out of the final
no-pair proof.  The real mutation branches remain separate: rank `2` is the
Label 4 boundary branch, while rank at least `4` enters the shifted window
analysis.
-/

/-- Dispatcher-ready rank split for the Label 4 no-pair tree.

For polarized `X`, choose a minimal support gene.  Either it has the minimal
Label 4 polarized rank `2`, or it has rank `2*q+4`; in the latter case the
support lower bound and the first strict rank gap are already packaged. -/
lemma no_pair_min_gene_rank_split {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized) :
    (∃ g : Gene,
      0 < X.1.1 g ∧
      (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) ∧
      g.type ≠ GeneType.NonPolarized ∧
      g.rank = 2) ∨
    (∃ (g : Gene) (q : ℕ),
      0 < X.1.1 g ∧
      (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) ∧
      g.type ≠ GeneType.NonPolarized ∧
      g.rank = 2 * q + 4 ∧
      (∀ h ∈ X.1.1.support, 2 * q + 4 ≤ h.rank) ∧
      Chromosome.prime^[1] X.1.1 ≠ 0 ∧
      Chromosome.prime^[1] Y.1.1 ≠ 0 ∧
      (Chromosome.prime^[1] X.1.1).rank <
        (Chromosome.prime^[1] Y.1.1).rank) := by
  obtain ⟨g, p, hgX, hgmin, hg_pol, hg_rank, hp_or⟩ :=
    no_pair_min_gene_data X hXpol
  rcases hp_or with hp0 | hp_pos
  · left
    refine ⟨g, hgX, hgmin, hg_pol, ?_⟩
    rw [hg_rank, hp0]
  · right
    obtain ⟨q, hg_rank_q, hmin_rank, hX1, hY1, hr1⟩ :=
      no_pair_rank_ge_four_window_data X Y hXY h17_1 g hgX hgmin hg_rank hp_pos
    exact ⟨g, q, hgX, hgmin, hg_pol, hg_rank_q, hmin_rank, hX1, hY1, hr1⟩

end MixPi2Lambda
