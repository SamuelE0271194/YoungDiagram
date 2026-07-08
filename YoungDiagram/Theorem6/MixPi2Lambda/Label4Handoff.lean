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
-/
