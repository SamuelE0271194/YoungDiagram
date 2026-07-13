import YoungDiagram.Theorem6.Mix2LambdaPi.Case34NoPairRankOne
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34NoPairRankGeThree

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

set_option maxHeartbeats 800000 in
-- The no-pair dispatcher elaborates several nested window decompositions; keep
-- the local budget high while the remaining branches are split into lemmas.
/-- No-equal-rank-pair dispatcher (§17 final block).  Let `m` be the minimum
rank of a gene of the polarized `X`; in Label 3 every polarized gene is
odd-rank, so `m` is odd and the paper's Case 2 (`m = 2`) does not occur.  We
split on `m ≥ 3` (Case 1) versus `m = 1` (Cases 3/4). -/
lemma exists_mutation_le_no_pair (m : ℕ)
    (X Y : nMix2LambdaPi (m + 2))
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
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  -- `X ≠ 0`, so it has a gene of minimal rank.
  have hXne : X.1.1 ≠ 0 := by
    intro hzero
    have := X.2
    rw [hzero, map_zero] at this
    omega
  obtain ⟨g, hgX, hgmin⟩ :=
    Mix2LambdaSection17.exists_min_rank_gene hXne
  -- The minimal gene is polarized (so odd rank in Label 3).
  have hg_pol : g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp hXpol g (Finsupp.mem_support_iff.mpr (ne_of_gt hgX))
  have hg_odd : Odd g.rank :=
    Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
      X.1.2 hgX hg_pol
  -- `m ≥ 3` (Case 1) or `m = 1` (Cases 3/4); `m = 2` cannot occur (m is odd).
  obtain ⟨p, hp⟩ := hg_odd
  by_cases hp0 : p = 0
  · -- `g.rank = 1`: Cases 3/4 of §17 (the `m = 1` minimum-rank analysis).
    exact exists_mutation_le_no_pair_rank_one X Y hXY hcommon h17_1
      hXpol hno_pair g hgX hgmin hg_pol hp hp0
  · -- `g.rank = 2p+1 ≥ 3`: Case 1 of §17.
    exact exists_mutation_le_no_pair_rank_ge_three X Y hXY hcommon h17_1
      hXpol hno_pair hXne g hgX hgmin hg_pol hp hp0

end Mix2LambdaPi
