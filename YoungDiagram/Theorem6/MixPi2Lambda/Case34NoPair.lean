import YoungDiagram.Theorem6.MixPi2Lambda.Case34Gaps

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair setup

This file starts the batch-C no-pair tree without wiring it into the final
`polarized_remaining` hole.  The first reusable fact is the Label 4 replacement
for the Label 3 rank-one/rank-ge-three split: polarized genes have even rank, so
the minimal polarized gene has rank `2` or at least `4`.
-/

/-- Minimal-gene data for the Label 4 no-pair tree.

For a polarized `X : nMixPi2Lambda (m+2)`, choose a support gene of minimal rank.
Its type is polarized and its rank has the form `2*p+2`; the cases `p=0` and
`0<p` are the rank-`2` boundary and the rank-`≥4` branch, respectively. -/
lemma no_pair_min_gene_data {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
    (hXpol : X.1.1.IsPolarized) :
    ∃ (g : Gene) (p : ℕ),
      0 < X.1.1 g ∧
      (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) ∧
      g.type ≠ GeneType.NonPolarized ∧
      g.rank = 2 * p + 2 ∧
      (p = 0 ∨ 0 < p) := by
  have hXne : X.1.1 ≠ 0 := by
    intro hzero
    have := X.2
    rw [hzero, map_zero] at this
    omega
  obtain ⟨g, hgX, hgmin⟩ :=
    Mix2LambdaSection17.exists_min_rank_gene hXne
  have hgsupp : g ∈ X.1.1.support :=
    Finsupp.mem_support_iff.mpr (ne_of_gt hgX)
  have hg_pol : g.type ≠ GeneType.NonPolarized :=
    IsPolarized_def'.mp hXpol g hgsupp
  have hg_even : Even g.rank :=
    Mix2LambdaSection17.even_rank_of_polarized_gene_mem_Mix_Pi_2Lambda
      X.1.2 hgX hg_pol
  obtain ⟨r, hr⟩ := hg_even
  cases r with
  | zero =>
      have hpos := g.rank_pos
      omega
  | succ p =>
      refine ⟨g, p, hgX, hgmin, hg_pol, ?_, Nat.eq_zero_or_pos p⟩
      rw [hr]
      ring

/-- The positive-index side of `no_pair_min_gene_data` gives the rank-ge-four
branch explicitly. -/
lemma no_pair_min_gene_rank_ge_four {m p : ℕ} {X : nMixPi2Lambda (m + 2)}
    {g : Gene}
    (hg_rank : g.rank = 2 * p + 2)
    (hp : 0 < p) :
    4 ≤ g.rank := by
  rw [hg_rank]
  omega

end MixPi2Lambda
