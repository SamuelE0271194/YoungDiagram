import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankGeFour
import YoungDiagram.Theorem6.MixPi2Lambda.Case34Gaps

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Label 4 no-pair rank-ge-four solver

The Label 4 (`Mix (Pi, 2 • Lambda)`) analogue of
`Mix2LambdaPi.exists_mutation_le_no_pair_rank_ge_three`, i.e. §17 Case 1
(`m ≥ 3` in the paper's numbering, here the minimal polarized gene has even
rank `2*p+2` with `0 < p`, so rank `≥ 4`).  The parity roles are flipped
relative to Label 3: polarized genes sit at even rank and the reduced §17
symmetric level is even.  All gap/window infrastructure it needs already
exists in the Label 4 `Window` / `Case34Gaps` / `Case34Helpers` layer with the
same names as Label 3. -/

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
  sorry

end MixPi2Lambda
