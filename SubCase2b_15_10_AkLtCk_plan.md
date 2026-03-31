# Plan: Sub-case 2b, (15.10) branch, `a_k < c_k` (line 801 of Theorem_6_Claude.lean)

## Context

This sorry sits inside the following nested case structure:

- **Case 2** (disjoint supports): `hcommon` negated — X and Y share no gene.
- **Sub-case 2b** (`hsigeq`): For every k ≥ 1 with `prime^[k] Y ≠ 0`, the sigma column
  satisfies `σ X k ≠ σ Y k`.
- **(15.10) branch** (`hXpn` negated): X contains **no** pair `(g⁺(r), g⁻(r))` of genes of the
  same rank and opposite types. Equivalently, for each rank `r`, X has only positive genes at
  rank `r`, or only negative genes, or none.
- **`ha` branch**: there exists `k : ℕ` with `0 < k`, `prime^[k] Y ≠ 0`, and
  `(Sigma.sigma X k).1 < (Sigma.sigma Y k).1`, i.e. `a_k < c_k` at some level `k`.

After `obtain ⟨k, hkpos, hYkne, hak⟩ := ha`, the available hypotheses are:

| Name | Type |
|------|------|
| `k` | `ℕ` |
| `hkpos` | `0 < k` |
| `hYkne` | `Chromosome.prime^[k] Y.val ≠ 0` |
| `hak` | `(Sigma.sigma X k).1 < (Sigma.sigma Y k).1` (i.e. `a_k < c_k`) |
| `hsigeq` | `∀ j > 0, prime^[j] Y ≠ 0 → Sigma.sigma X j ≠ Sigma.sigma Y j` |
| `hXpn` | `∀ (g h : Gene), ¬(g.rank = h.rank ∧ g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.val g ∧ 0 < X.val h)` |
| `hXY` | `X < Y` (in `Variety.Pi`) |
| `hcommon` | `∀ g, ¬(0 < X.val g ∧ 0 < Y.val g)` (disjoint supports) |
| `hX`, `hY` | `X ∈ Pi_n (m+2)`, `Y ∈ Pi_n (m+2)` |

**Goal:** `∃ Z : Variety.Pi, Pi.Step X Z ∧ Z ≤ Y`

---

## Key notations

Write `a_j = (Sigma.sigma X j).1`, `b_j = (Sigma.sigma X j).2`,
`c_j = (Sigma.sigma Y j).1`, `d_j = (Sigma.sigma Y j).2`.

From `X ≤ Y`: `(a_j, b_j) ≤ (c_j, d_j)` componentwise for all `j`.
From `hsigeq`: `(a_j, b_j) ≠ (c_j, d_j)` for all `j ≥ 1` with `prime^[j] Y ≠ 0`.
From `hak`: `a_k < c_k`.

Because `hXpn` holds, `prime^[k] X` also has **no** same-rank pos-neg pair:
if `(prime^[k] X)(r, .Pos) > 0` and `(prime^[k] X)(r, .Neg) > 0` then `X(r+k, .Pos) > 0`
and `X(r+k, .Neg) > 0` — same rank `r+k`, contradicting `hXpn`.

---

## Overview of the proof

The proof applies one of four primitive `Pi.Step` mutations to X, yielding Z, then verifies Z ≤ Y
using the hypothesis `a_k < c_k` (and the rest of the domination `X ≤ Y`). The 4 cases are
distinguished by which kind of two-gene sub-chromosome can be extracted from X; each case maps
to one of the available primitive mutation types (type1 or type2). The paper (Djoković 1982, §15)
labels these "Cases 1–4" after the assumption `a_1 < c_1` (here `a_k < c_k`).

### Common proof skeleton (same as lines 616–791)

In every case:
1. Identify two specific genes `gA, gB` in `X` and set
   `X1 := Pi.X1 (or X2) ...`, `Y1 := Pi.Y1 (or Y2) ...`, `restval := X.val - X1.val`.
2. Show `rest_mem : restval ∈ Pi` (support of rest ⊆ support of X, which is polarized).
3. Show `hX_eq : X1.val + restval = X.val`.
4. Construct `Z := ⟨Y1.val + restval, ...⟩`.
5. Produce `Pi.Step X Z` via `Pi.Step.mk X1 Y1 rest_pi hprim`.
6. Prove `Z ≤ Y` via `le_iff_dominates`, splitting on `j < k`, `j = k`, `j > k`.

---

## Case 1 — Type 1 mutation, ε = .Positive (small positive + large negative gene)

**Condition**: X contains a positive gene `gpos` at rank `r` with `r ≤ k`, and a negative gene
`gneg` at rank `s > r` (possibly `s > k`).

Concretely: `∃ gpos gneg : Gene, gpos.type = .Positive ∧ gneg.type = .Negative ∧
  gpos.rank ≤ k ∧ gpos.rank < gneg.rank ∧ 0 < X.val gpos ∧ 0 < X.val gneg`.

**Mutation**: `g⁺(r) + g⁻(s) → g⁻(r−1) + g⁺(s+1)` (type1, ε = .Positive, `m = r`, `n = s`).

**Why Z ≤ Y**: At level `j`:

- `j < r`: signature change cancels by `mutation_type1_iterate_signature_eq` (j ≤ r−1 ≤ k−1).
- `j = r, ..., k−1` (if `r < k`): need to show the gain `g⁺(s+1)` and loss `g⁻(s)` do not
  exceed the excess `(c_j − a_j, d_j − b_j)`. At level `j < k`, `prime^[j] X1` has only
  `g⁻(s−j)` (since `r ≤ k` means `prime^[r] g⁺(r) = g⁺(0) = 0` after `j ≥ r`). Compare with
  `prime^[j] Y1` which has `g⁺(s+1−j)`. The signature change at these levels must be bounded
  using dominance from `X ≤ Y`.
- `j = k`: `prime^[k] X1` has `g⁻(s−k)` (if `s > k`) contributing `(0, *)` to signature.
  `prime^[k] Y1` has `g⁺(s+1−k)` contributing `(*, 0)`. Net change to `a_k`: +1 (new `g⁺(s+1)`
  at level `k`), gain is ≤ `c_k − a_k ≥ 1` by `hak`. ✓
- `j > k`: both `X1` and `Y1` contribute identically at levels `j > s` (vanish). For
  `k < j ≤ s`: use the excess at those levels from `X ≤ Y`.

**Key lemmas**: `mutation_type1_iterate_signature_eq`, `Pi.Primitive.type1`,
`signature_ofRank_one_positive`, `signature_ofRank_one_negative`.

---

## Case 2 — Type 1 mutation, ε = .Negative (small negative + large positive gene)

**Condition**: X contains a negative gene `gneg` at rank `r` with `r ≤ k`, and a positive gene
`gpos` at rank `s > r` (and `s > k` so `gpos` contributes to `a_k`).

Concretely: `∃ gneg gpos : Gene, gneg.type = .Negative ∧ gpos.type = .Positive ∧
  gneg.rank ≤ k ∧ gneg.rank < gpos.rank ∧ 0 < X.val gneg ∧ 0 < X.val gpos`.

**Mutation**: `g⁻(r) + g⁺(s) → g⁺(r−1) + g⁻(s+1)` (type1, ε = .Negative, `m = r`, `n = s`).

Here type1 with ε = .Negative uses `X1 = g^ε(m) + g^{−ε}(n) = g⁻(r) + g⁺(s)` and
`Y1 = g^{−ε}(m−1) + g^ε(n+1) = g⁺(r−1) + g⁻(s+1)`.

**Why Z ≤ Y**: The positive gene moves from rank `s` to rank `r−1`. Since `r ≤ k < s`, the net
effect on `a_k` is: loses `g⁺(s)` (rank `s > k`): `a_k` decreases by 1. Gains `g⁺(r−1)` (rank
`r−1 < k`): does not contribute to `a_k`. So `a_k(Z) = a_k − 1 < a_k ≤ c_k − 1 ≤ c_k`. ✓ (but
the sigma at level `k` for the positive component is fine). However, the negative component gains:
`b_k` decreases by 1 at the old `g⁺(s)` and the new `g⁻(s+1)` at rank `s+1 > k` increases
`b_k`. The proof that `Z ≤ Y` must use both the `(a_k, b_k) ≤ (c_k, d_k)` bound and the sigma
comparison at intermediate levels.

**Note**: This case is most natural when `b_k < d_k` additionally, which follows from `hsigeq`
when `a_k = a_k(Z)` coincides with `c_k` in the intermediate step, but at level `k` the sigma of
Z may still satisfy the bound via the negative component excess.

**Key lemmas**: same as Case 1 but with ε = .Negative.

---

## Case 3 — Type 2 mutation, ε = .Positive (two positive genes, m ≥ 2)

**Condition**: X contains two positive genes `gpos1`, `gpos2` at ranks `r₁ ≤ r₂` with `r₁ ≥ 2`.
(They may be at the same rank if `X.val gpos1 ≥ 2`, or different ranks.)

Concretely: `∃ gpos1 gpos2 : Gene, gpos1.type = .Positive ∧ gpos2.type = .Positive ∧
  gpos1.rank ≤ gpos2.rank ∧ 1 < gpos1.rank ∧ 0 < X.val gpos1 ∧ 0 < X.val gpos2`.

**Mutation**: `g⁺(r₁) + g⁺(r₂) → g⁺(r₁−2) + g⁺(r₂+2)` (type2, ε = .Positive).

**Why Z ≤ Y**: At level `j`:

- `j < r₁ − 2`: signature change cancels by `mutation_type2_iterate_signature_eq`.
- `r₁ − 2 ≤ j < r₁` (if `r₁ ≥ 3`): the lower gene `g⁺(r₁)` vanishes while `g⁺(r₁−2)` is
  smaller; `g⁺(r₂+2)` extends higher. Need to bound using dominance.
- `j = k`: uses `a_k < c_k` to absorb the gain from the upward-shifted positive gene.
- `j > r₂`: both pairs vanish, signature is unchanged (equals `X`).

**Key lemma**: `mutation_type2_iterate_signature_eq`, `Pi.Primitive.type2`.

---

## Case 4 — Type 2 mutation, ε = .Negative (two negative genes, m ≥ 2)

**Condition**: X contains two negative genes `gneg1`, `gneg2` at ranks `r₁ ≤ r₂` with `r₁ ≥ 2`.

Concretely: `∃ gneg1 gneg2 : Gene, gneg1.type = .Negative ∧ gneg2.type = .Negative ∧
  gneg1.rank ≤ gneg2.rank ∧ 1 < gneg1.rank ∧ 0 < X.val gneg1 ∧ 0 < X.val gneg2`.

**Mutation**: `g⁻(r₁) + g⁻(r₂) → g⁻(r₁−2) + g⁻(r₂+2)` (type2, ε = .Negative).

This case is symmetric to Case 3. The mutation moves two negative genes further apart. Even though
we are trying to increase `a_k`, the movement of negative genes can create room by adjusting `b_k`
downward (towards `d_k`), freeing up the dominance inequality to accommodate the positive excess
needed at level `k`.

**Why Z ≤ Y**: As in Case 3, with the positive/negative components swapped. Key: at level `k`
the negative component `b_k(Z)` decreases (or stays), and we use `d_k − b_k ≥ 0` combined with
`a_k < c_k` to verify both components.

---

## Exhaustiveness

The 4 cases must together cover all X that can arise in this branch. The argument is:

X has rank `m + 2 ≥ 2` and lies in Pi (all genes polarized). We need X to contain a 2-gene
sub-chromosome that admits a primitive mutation; it suffices that X has one of:
- Two genes of the same type and one of them has rank ≥ 2 (Cases 3 or 4), OR
- Two genes of opposite types at different ranks (Cases 1 or 2).

**Why X cannot have only rank-1 genes of one type**: If X had only `g⁺(1)^m+2` (all rank-1
positive), then `a_j = 0` for `j ≥ 1` (all rank-1 genes vanish under prime). Then `a_k = 0`.
For `X ≤ Y` and `prime^[k] Y ≠ 0`, we would need `c_k ≥ 1` and the sigma comparison would
force a contradiction with `X < Y` and disjoint supports (similar argument to the rank-1 base
case at lines 46–61). So such X cannot appear given `X < Y` disjoint.

**The actual case split in Lean** might proceed by `by_cases` on:
1. Whether X has a positive gene `gpos` with `gpos.rank ≤ k`:
   - Yes → further `by_cases` on whether a negative gene `gneg` with `gpos.rank < gneg.rank`
     exists (Cases 1 or 2), or a second positive gene with rank ≥ 2 (Case 3).
   - No (all positive genes have rank > k) → Case 3 (two positive genes of rank > k ≥ 1, so both
     rank ≥ 2) or Case 4.

---

## Step-by-step proof of Z ≤ Y for Case 1 (detailed)

The structure mirrors exactly the proof at lines 616–791 (the g⁺(k)+g⁻(k) branch):

```lean
-- Extract genes
obtain ⟨gpos, gneg, hr_le, htpos, htneg, hXgpos, hXgneg⟩ := ...
let r := gpos.rank
let s := gneg.rank
have hlt : r < s := ...
have hre : ε = .Positive := rfl
-- X1, Y1, rest
let X1 : Pi := Pi.X1 hε (Nat.le_of_lt hlt) hr_pos
let Y1 : Pi := Pi.Y1 hε (Nat.le_of_lt hlt) hr_pos
let restval := X.val - Finsupp.single gpos 1 - Finsupp.single gneg 1
-- rest_mem, hX_eq (same as lines 590–614)
-- Pi.Step construction (same as lines 632–637)
-- Z ≤ Y: intro j, split on j < r, r ≤ j < k, j = k, j > k
```

The critical new case (not present in lines 616–791) is `r ≤ j < k`:
```lean
-- r ≤ j < k: prime^[j] g⁺(r) = Gene.ofRank (r-j) .Positive = 0 (since j ≥ r)
-- prime^[j] g⁻(s) = Gene.ofRank (s-j) .Negative (nonzero since j < k ≤ s? need s > j)
-- prime^[j] Y1 = prime^[j] g⁻(r-1) + prime^[j] g⁺(s+1)
-- Need: sig(Y1^(j)) + sig(rest^(j)) ≤ sig(Y^(j))
-- = sig(X^(j)) - sig(X1^(j)) + sig(Y1^(j)) ≤ sig(Y^(j))
-- Difference = sig(Y1^(j)) - sig(X1^(j))
```

The key identity for the range `r ≤ j < k` is:
```lean
have hY1X1_j : signature (Chromosome.prime^[j] Y1.val) ≤
    signature (Chromosome.prime^[j] X1.val) + (Sigma.sigma Y j - Sigma.sigma X j)
```

This uses `X ≤ Y` (dominance at level `j`) and the mutation signature lemma.

---

## Key lemmas needed

| Lemma | File | Role |
|-------|------|------|
| `mutation_type1_iterate_signature_eq` | `Mutations/Pi.lean` | Cancel sig change for `j < r` |
| `mutation_type2_iterate_signature_eq` | `Mutations/Pi.lean` | Cancel sig change for `j < m₁−2` |
| `Pi.Primitive.type1`, `Pi.Primitive.type2` | `Mutations/Basic.lean` | Construct primitive steps |
| `le_iff_dominates` | `Chromosome.lean` | Convert `≤` to sigma comparison |
| `iterate_map_add`, `map_add` | Mathlib | Linearity of prime and signature |
| `prime_iterate_ofRank` | `Chromosome.lean` | `prime^[k](g^ε(n)) = g^ε(n−k)` |
| `signature_ofRank_one_positive/negative` | `Chromosome.lean` | Base signatures |
| `signature_pi_isNat` | `Sigma.lean` | Signatures are nonneg integers for Pi elements |

---

## Open questions / uncertainties

1. **Exact formulation of the 4 cases from the paper**: The paper (Djoković 1982, §15) likely
   states the cases in terms of the structure of prime^[k] X (rank of the minimal gene, parity of
   indices, etc.) rather than the raw gene structure of X. The case split above is a reconstruction
   — verify against the paper.

2. **The intermediate levels `r ≤ j < k`** (Case 1): The existing proof for the `hXpn` branch
   (lines 616–791) only needed `j < r`, `j = r`, `j > r`. Here `r ≤ k` opens up an intermediate
   range that needs a new sigma bound argument. The bound comes from `X ≤ Y` at those levels.

3. **Cases 2–4**: Similar intermediate range analysis is needed, adapted to the negative component
   and type2 mutations. The key is that `hak` provides at least 1 unit of slack at level `k`.

4. **Type3 mutations**: The `Pi.Primitive.type3` constructor uses `Gene.ofRankAlt` (alternating
   sign convention). These may appear for X with alternating-parity gene structure that doesn't fit
   Cases 1–4. If the 4 cases don't exhaust all X, a Case 5 using type3 may be needed.
