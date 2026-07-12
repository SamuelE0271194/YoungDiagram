import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairDispatcher
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankGeFourSolver
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleComplete
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDoubleRest
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDoubleEmpty

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Label 4 no-pair solver (assembled)

Hypothesis-free assembly of the §17 no-pair branch for `Mix (Pi, 2 • Lambda)`:
the minimal polarized gene has rank `2` (single/double) or `≥ 4` (window solver).
The rank-`2` single case is closed by `single_complete`; the rank-`≥4` case by
`exists_mutation_le_no_pair_rank_ge_four` (with `p := q+1`); the rank-`2` double
case is closed via `double_of_rank_split` with `double_empty` supplied and the
two second-gene double leaves (`same_gene`, `double_rank_ge_four`) as the only
remaining frontier. -/

set_option maxHeartbeats 800000 in
lemma exists_mutation_le_no_pair (m : ℕ)
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  refine exists_mutation_le_no_pair_of_rank_branches m X Y hXY hcommon h17_1
    hXpol hno_pair ?_ ?_
  · -- minimal polarized gene of rank 2
    intro g hgX hgmin hg_pol hg_rank
    by_cases hg_two : 2 ≤ X.1.1 g
    · -- rank-2 double case
      refine exists_mutation_le_no_pair_rank_two_double_of_rank_split
        X Y hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_two
        (fun hneg restD hrestD hrest_zero hXeq hm2 hsigX hX3 =>
          exists_mutation_le_no_pair_rank_two_double_empty X Y hXY h17_1 g hgX
            hgmin hg_pol hg_rank hneg restD hrestD hrest_zero hXeq hm2 hsigX hX3)
        ?_ ?_
      · -- second gene equals `g` (double same-gene) — remaining frontier
        sorry
      · -- second gene distinct of rank `2*q₂+4` — remaining frontier
        sorry
    · -- rank-2 single case
      have hg_one : X.1.1 g = 1 := by omega
      exact exists_mutation_le_no_pair_rank_two_single_complete X Y hXY hcommon
        h17_1 hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_one
  · -- minimal polarized gene of rank ≥ 4
    intro g q hgX hgmin hg_pol hg_rank hmin_rank hX1 hY1 hr1
    have hXne : X.1.1 ≠ 0 := fun h => by simp [h] at hgX
    exact exists_mutation_le_no_pair_rank_ge_four X Y hXY hcommon h17_1 hXpol
      hno_pair hXne g hgX hgmin hg_pol (show g.rank = 2 * (q + 1) + 2 by omega)
      (by omega)

end MixPi2Lambda
