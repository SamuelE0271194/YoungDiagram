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

STATUS: statements + dispatcher done; the two branch bodies are ported from the
Label-3 lines 51–313 (diagonal) and 314–938 (multiplicity-one) but currently
left as `sorry`.

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
  sorry

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
