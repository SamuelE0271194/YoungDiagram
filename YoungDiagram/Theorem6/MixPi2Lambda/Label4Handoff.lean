/-!
# Handoff: Close Label 4 (`Mix (Pi, 2 • Lambda)`) — Theorem 6, Section 17

This is a documentation-only file (no declarations). It records the port plan for
closing the last project-wide `sorry`:
`YoungDiagram/Theorem6/MixPi2Lambda/Case34.lean` :
`MixPi2Lambda.exists_mutation_le_polarized_remaining`
= the ENTIRE Section 17 polarized-mutation classification for Label 4 (both the
"pair" part and the "no-pair" part). Labels 0,1,2,3 are complete.

## Discipline
Verify each file with a per-module build; keep the project green
(`lake build YoungDiagram.Theorem6.MixPi2Lambda` = 0 errors). Port bottom-up in the
dependency order below. Do not wire a new file into the sorry until its
dependencies are green. Integration edits `Case34.lean` last.

## 0. Already done (do not redo)
* Joint induction (`Mix2LambdaJoint.lean`): rank 0/1, shared-gene, and the (17.1)
  sigma-agreement reduction are shared L3/L4 and DONE. There is NO duality shortcut;
  the Section 17 mutation classification is strictly per-variety.
* Raw mutation defs `Mutations/MixPi2Lambda/type9..type17`: ALL complete and green
  (`X_k`, `Y_k`, `X_k_eq`, `Y_k_eq`, `Primitive.type_k`,
  `mutation_type_k_iterate_signature_eq`, `mutation_type_k_le`).
* L4 scaffolding: `MixPi2Lambda/Prelim.lean`, `Case1.lean`, `Type9.lean`,
  `Type13.lean`, and the `exists_mutation_le_reduced` dispatcher in `Case34.lean`
  (nonpolarized + double-pair branches done; only `polarized_remaining` = sorry).
* Added and verified (run 3fe6d6b5): `MixPi2Lambda/Type14.lean` and `Type16.lean`
  general Step constructors (`exists_mutation_le_type{14,16}_of_decomp` and
  `_of_genes`). These two files still need their window-signature lemmas added.

## 1. Mirror dictionary (L3 `Mix2LambdaPi` -> L4 `MixPi2Lambda`)
Parity flip of gene ranks:
* L3 polarized at ODD rank `2m+1` -> L4 polarized at EVEN rank `2m+2`.
* L3 NP at EVEN rank `2m` -> L4 NP at ODD rank `2m+1`; `2n+2`->`2n+3`, `2n+3`->`2n+4`.
* Section 17 symmetric-signature level: L3 "a_i=b_i for i ODD" -> L4 "for i EVEN".
* Integrality: L4 `prime^[odd]` lands in `Mix (2Lambda, Pi)`, `prime^[even]` in
  `Mix (Pi, 2Lambda)`; both give integer signature components. Odd/even case roles
  SWAP vs L3.
* Renames: namespace `Mix2LambdaPi`->`MixPi2Lambda`; variety
  `Mix (2Lambda, Pi)`->`Mix (Pi, 2Lambda)`; `nMix2LambdaPi`->`nMixPi2Lambda`;
  `sub_single_one_mem_Mix_2Lambda_Pi` (odd) -> `sub_single_one_mem_Mix_Pi_2Lambda`
  (even); `cond_15_6/7_Mix_2Lambda_Pi` -> `cond_15_6/7_Mix_Pi_2Lambda`;
  `prime_mem_Mix_2Lambda_Pi_iterate` -> `prime_mem_Mix_Pi_2Lambda_iterate`;
  `Mix.tLambda_Pi_neg_val` -> `Mix.Pi_2Lambda_neg_val`.
* Variety-agnostic (reuse as-is): `MixLambdaPi.twostep/twostep_snd/cells`,
  `Mix2LambdaSection17.{single_pair_add_rest, double_pair_add_rest,
  double_single_pair_add_rest, single_triple_add_rest, prime_iterate_ne_zero_of_no_gene,
  one_one_le_of_both_lt}`, `prime_iterate_coeff`, `signature_ofRank_*`.

## 2. STRUCTURAL DIVERGENCE — NOT a line-by-line copy
L4's minimal polarized rank is 2 (even), and L4 has rank-1 NP genes (odd) at the
bottom, which L3 does not. Consequences:
* The general `of_decomp`/`of_genes` (m<=n) wrappers ARE clean rank-substituted
  mirrors (safe to textual-mirror).
* The rank-boundary window lemmas (`typeN_rank_one_*`, the `m=0` specializations) and
  the whole Case34 boundary/rank-minimal tree (`PairFinally*`, `NoPairRankOne*`,
  `NegPartner`, `RemainderDouble`, ...) must be RE-DERIVED against L4 parity. The
  "Finally m=1" family becomes "m=2 / rank-2"; L4 gets extra active window levels
  (e.g. type14 `m=0` has the low double at rank 2, still half-alive at `j=1`). Use the
  verified L3 lemmas (`pair_finally_gap`, `type13_of_decomp`, seed/window in
  `Case34PairFinallyOne`) as CONCEPTUAL templates (mirror the strategy, not the ranks).
* Same adaptation as the LP->PL port (level-1 asymmetry, charge-dual, j=k boundary):
  the mirror "fails" precisely at rank-minimal/boundary leaves and needs re-derivation.

## 3. Port order (dependency-respecting)
Batch A — Type wrappers (each: general constructors [clean] + window lemmas [adapt]):
  Type16 (partial) -> Type15 -> Type12; Type16 -> Type17;
  Type13 -> Type14 (partial); Type15 -> Type12 -> Type11 -> Type10.
  Per file mirror `Mix2LambdaPi/TypeN.lean`; recompute
  `typeN_..._signature_{eq_before,mid,eq_after}` and
  `typeN_..._target_add_rest_le_of_gaps` with L4 parity (odd/even mid swap).
Batch B — infrastructure:
  `Window.lean` (imports Type10; KEY_X/KEY_Y/twostep variety-agnostic, mostly clean),
  then `Case34Helpers.lean`, `Case34Seed.lean` (import Window), then `Case34Gaps.lean`
  (imports Helpers + Type15 + Type17).
Batch C — Case34 tree (mirror `Mix2LambdaPi/Case34*`, ADAPT boundaries):
  NoPair, NoPairRankGeThree, NoPairRankOne (+Double, SameGene, SameSign),
  PairBranch, PairRankOne, PairFinally{One,Quad,Triple,Boundary}, SecondDouble,
  NegPartner, RemainderDouble, Remaining.
Batch D — integration:
  Fill `Case34.lean` `exists_mutation_le_polarized_remaining` (mirror L3
  `exists_mutation_le_polarized_remaining_of_pair` + `exists_mutation_le_no_pair`);
  confirm `lake build ...MixPi2Lambda` green, 0 sorries project-wide.

## 4. Reference
L3 originals to mirror: `YoungDiagram/Theorem6/Mix2LambdaPi/` (~13k lines / ~25 files);
multi-session effort; verify per file.

## 5. Division of labor
* Orchestrator: reconnaissance (done), boundary-adaptation hard cores, per-batch
  review, final dispatcher wiring.
* Local/budget agent: mechanical mirror of the clean parts + first pass of the adapted
  files (flag failures at boundary leaves for the orchestrator).

## 6. Current batch C checkpoint
* 2026-07-09: batch C started with thirteen green dependency modules:
  `Case34PairRankOne.lean`, `Case34NoPair.lean`, and
  `Case34NoPairRankGeFour.lean`, plus `Case34NoPairSplit.lean` and
  `Case34NoPairDispatcher.lean`, and the rank-2 boundary setup
  `Case34NoPairRankTwo.lean`, `Case34NoPairRankTwoDouble.lean`, plus
  `Case34NoPairRankTwoDoubleRest.lean` and
  `Case34NoPairRankTwoSingleRest.lean`, and the rank-2 aggregate dispatcher
  `Case34NoPairRankTwoBranches.lean`, plus the no-pair aggregate dispatcher
  `Case34NoPairBranches.lean`, and the double-empty leaf wrapper
  `Case34NoPairRankTwoDoubleEmpty.lean`, plus its reduced rank-two integration
  layer `Case34NoPairRankTwoClosed.lean`.
* `Case34PairRankOne.pair_rank_two_zero_successor_shape` records the Label 4
  rank-2 boundary shape.  Unlike Label 3's rank-one pair boundary, this is not
  a contradiction: rank-2 positive and negative genes both have signature `(1,1)`.
* `Case34NoPair.no_pair_min_gene_data` records the Label 4 no-pair split:
  minimal polarized rank is `2*p+2`; `p=0` is the rank-2 boundary and `0<p`
  gives rank at least 4.
* `Case34NoPairRankGeFour.no_pair_rank_ge_four_first_gap` packages the first
  rank-ge-four no-pair setup: `prime^[1] X != 0`, `prime^[1] Y != 0`, and the
  strict rank gap at level 1 from (17.1).
* `Case34NoPairRankGeFour.no_pair_rank_ge_four_window_data` normalizes this
  branch to the natural Label 4 window form `g.rank = 2*q+4`, packages the
  support lower bound `2*q+4 <= h.rank`, and carries the same first-gap data.
* `Case34NoPairSplit.no_pair_min_gene_rank_split` packages the no-pair
  dispatcher split: either the minimal polarized gene has rank `2`, or the
  rank-ge-four branch already carries the normalized `2*q+4` window data and
  the first strict rank gap.
* `Case34NoPairDispatcher.exists_mutation_le_no_pair_of_rank_branches` is a
  no-sorry glue lemma: given a rank-2 boundary solver and a rank-ge-four window
  solver, it proves the no-pair conclusion by dispatching through
  `no_pair_min_gene_rank_split`.
* `Case34NoPairRankTwo` packages the common rank-2 no-pair boundary data:
  `no_pair_rank_two_boundary_data` gives the opposite-sign zero and the
  single/double coefficient split, while
  `no_pair_rank_two_rest_min_gene_data` chooses a minimal gene after removing
  one copy of the rank-2 minimal gene.
* `Case34NoPairRankTwo.exists_mutation_le_no_pair_rank_two_of_subcases` is the
  rank-2 branch dispatcher: it reduces the future solver to three leaf solvers
  for the double minimal gene, empty singleton remainder, and nonempty singleton
  remainder cases.
* `Case34NoPairRankTwo.no_pair_rank_two_single_empty_shape` handles the
  bookkeeping for the empty singleton leaf: it proves `X = single g 1`, pins the
  ambient rank parameter to `m = 0`, computes `signature X = (1,1)`, and gives
  `prime^[3] X = 0`.
* `Case34NoPairRankTwo` also prepares the double minimal-gene branch:
  `no_pair_rank_two_double_rest_min_gene_data` chooses a minimal gene after
  removing two copies of the rank-2 minimal gene, and
  `no_pair_rank_two_double_empty_shape` packages the empty double-remainder
  shape `X = single g 1 + single g 1`, `m = 2`, `signature X = (2,2)`, and
  `prime^[3] X = 0`.
* `Case34NoPairRankTwoDouble.exists_mutation_le_no_pair_rank_two_double_of_subcases`
  is the no-sorry double-branch glue: it splits the `2 <= X g` branch into
  empty and nonempty double-remainder leaf solvers, passing the prepared shape
  and minimal-gene data through.
* `Case34NoPairRankTwoDoubleRest.no_pair_rank_two_double_rest_rank_split`
  packages the next nonempty double-remainder split: the selected remainder
  gene is either the original rank-`2` gene again, or it has normalized
  rank `2*q₂+4`.  The companion dispatcher
  `exists_mutation_le_no_pair_rank_two_double_rest_of_rank_split` is no-sorry
  glue for future same-gene-extra and rank-ge-four leaf solvers; the higher
  dispatcher `exists_mutation_le_no_pair_rank_two_double_of_rank_split` combines
  it with the double-empty split, so the full double branch now reduces to
  three leaf solvers: empty double remainder, same-gene extra multiplicity, and
  rank-ge-four remainder.
* `Case34NoPairRankTwoSingleRest.no_pair_rank_two_single_rest_rank_ge_four`
  packages the singleton-remainder normalization: when `X g = 1` and removing
  that one copy leaves a nonempty remainder, its minimal gene cannot still have
  rank `2`, so it has normalized rank `2*q₂+4`.  The companion dispatcher
  `exists_mutation_le_no_pair_rank_two_single_rest_of_rank_ge_four` is no-sorry
  glue for the future singleton-remainder rank-ge-four leaf solver; the higher
  dispatcher `exists_mutation_le_no_pair_rank_two_single_of_rank_ge_four`
  combines it with the singleton-empty shape, so the full singleton branch now
  reduces to two leaf solvers: empty singleton remainder and rank-ge-four
  singleton remainder.
* `Case34NoPairRankTwoBranches.exists_mutation_le_no_pair_rank_two_of_rank_branches`
  combines the prepared singleton and double dispatchers.  The whole rank-`2`
  no-pair boundary now reduces to five future leaf solvers: singleton-empty,
  singleton rank-ge-four, double-empty, double same-gene-extra, and double
  rank-ge-four.
* `Case34NoPairBranches.exists_mutation_le_no_pair_of_prepared_branches`
  combines the top-level no-pair minimal-rank split with the rank-`2` aggregate
  dispatcher.  The full no-pair branch now reduces to the five rank-`2` leaves
  plus the rank-ge-four window solver.
* `Case34NoPairRankTwoDoubleEmpty.exists_mutation_le_no_pair_rank_two_double_empty_of_type10_gaps`
  is the first concrete mutation leaf wrapper: the rank-`2` double-empty shape
  is converted to the doubled-gene type10 step once the three standard type10
  gaps at levels `1`, `2`, and `3` are supplied.
  The same module now also records the low-level double-empty normalization:
  `prime^[1] X` has the two-copy rank-`1` signature, `prime^[2] X = 0`,
  and `prime^[1] Y != 0`.
  `Case34Gaps.type10_succ_gap_positive` and
  `Case34Gaps.type10_succ_gap_negative` expose the reusable odd-level type10
  successor interface.  The informal §17 Case 2 drop chain is formalized by
  `no_pair_rank_two_double_empty_case2_succ_gap`, while
  `no_pair_rank_two_double_empty_case2_pred_gap` rules out the wrong
  predecessor component using level-`0` agreement and `signature_prime_le`.
  Consequently `exists_mutation_le_no_pair_rank_two_double_empty` closes the
  leaf unconditionally.  `Case34NoPairRankTwoClosed` supplies this theorem to
  the prepared dispatcher and reduces the rank-`2` no-pair branch from five
  future leaves to four.
* Verified directly:
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34PairRankOne`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPair`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankGeFour`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairSplit`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairDispatcher`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwo`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDouble`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDoubleRest`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleRest`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoBranches`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairBranches`,
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDoubleEmpty`, and
  `lake build YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoClosed`, and
  `lake build YoungDiagram.Theorem6.MixPi2Lambda`.
-/
