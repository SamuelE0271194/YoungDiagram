import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairSplit

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair dispatcher

This file is intentionally only the glue layer: it consumes the rank split from
`Case34NoPairSplit` and delegates the two real mutation proofs to branch
solvers supplied by later modules.
-/

/-- Dispatcher glue for the Label 4 no-pair tree.

Once the rank-`2` boundary solver and the rank-ge-four window solver are
available, this lemma turns them into the no-pair conclusion without repeating
the minimal-gene bookkeeping. -/
lemma exists_mutation_le_no_pair_of_rank_branches (m : ℕ)
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (_hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (_hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (rank_two :
      ∀ g : Gene,
        0 < X.1.1 g →
        (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) →
        g.type ≠ GeneType.NonPolarized →
        g.rank = 2 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (rank_ge_four :
      ∀ (g : Gene) (q : ℕ),
        0 < X.1.1 g →
        (∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank) →
        g.type ≠ GeneType.NonPolarized →
        g.rank = 2 * q + 4 →
        (∀ h ∈ X.1.1.support, 2 * q + 4 ≤ h.rank) →
        Chromosome.prime^[1] X.1.1 ≠ 0 →
        Chromosome.prime^[1] Y.1.1 ≠ 0 →
        (Chromosome.prime^[1] X.1.1).rank <
          (Chromosome.prime^[1] Y.1.1).rank →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  rcases no_pair_min_gene_rank_split X Y hXY h17_1 hXpol with
    ⟨g, hgX, hgmin, hg_pol, hg_rank⟩ |
    ⟨g, q, hgX, hgmin, hg_pol, hg_rank, hmin_rank, hX1, hY1, hr1⟩
  · exact rank_two g hgX hgmin hg_pol hg_rank
  · exact rank_ge_four g q hgX hgmin hg_pol hg_rank hmin_rank hX1 hY1 hr1

end MixPi2Lambda
