# `exists_mutation_le_fifteen_ten`

## Statement

Given `X, Y : nPi (m+2)` (Young diagrams of rank `m+2`), if `X < Y`, then there exists a one-step mutation `Z` (i.e. `Pi.Step X Z`) such that `Z ≤ Y`.

```
∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1
```

## Hypotheses

| Name | Meaning |
|---|---|
| `m : ℕ` | Base rank (actual rank is `m + 2`) |
| `ih` | **Induction hypothesis**: for all smaller ranks `k < m+2`, the result holds — any `X < Y` of rank `k` admits a mutation step toward `Y` |
| `X Y : nPi (m+2)` | Two Young diagrams of rank `m + 2` |
| `hXY : X.1 < Y.1` | `X` is strictly less than `Y` in the partial order on `Pi` |
| `hcommon` | **No shared gene**: X and Y have disjoint support — there is no gene `g` with `X(g) > 0` and `Y(g) > 0` |
| `hsigeq` | **No coinciding sigma**: for every level `k ≥ 1` where `Y^(k) ≠ 0`, the signatures differ — `σ(X, k) ≠ σ(Y, k)` |
| `hXpn` | **X has no positive-negative pair**: X does not contain both a positive and a negative gene of the same rank simultaneously |

## Context

This lemma handles **Cases 1–4 of §15.10** of Djoković's paper — the subcase where:
- X and Y are **disjoint** (no shared gene),
- their **sigma signatures never agree** at any level where Y is nonzero, and
- X is **sign-consistent** (no mixed ± gene at any rank).

It is called in `YoungDiagram/Theorem6.lean` (line 523) after the other three subcases (`shared_gene`, `disjoint_sigma_eq`, `disjoint_pair`) have been dispatched.

---

## Notation

Write `σ(X, j) = (aⱼ, bⱼ)` and `σ(Y, j) = (cⱼ, dⱼ)`. From `X ≤ Y`, dominance gives `(aⱼ, bⱼ) ≤ (cⱼ, dⱼ)` componentwise at each level `j`. From `hsigeq`, `σ(X, j) ≠ σ(Y, j)` for every `j ≥ 1` with `Y^(j) ≠ 0`, so at every such level at least one component is strictly smaller.

Let `m` be the minimal rank of any gene in `X`, and write `g₁ = g_{ε₁}(m)` for the gene of rank `m` in `X`, where `g_ε(k) := g^{ε · (−1)^{k−1}}(k)` (Djoković §15, p. 30), so the sign of `g_ε(k)` alternates with `k`.

---

## Proof Split

The proof splits on whether `a₁ < c₁` (the first sigma component at level 1 strictly increases):

---

### Case A: `a₁ < c₁`

**Condition:** `(σ(X, 1)).1 < (σ(Y, 1)).1`, i.e. the positive-gene count at level 1 is strictly smaller in X than in Y.

This is the paper's assumption **"a₁ < c₁"** (Cases 1–4 of §15.10). The gene `g₁ = g_{ε₁}(m)` is chosen as the gene of minimal rank `m` in X, which determines a sign `ε₁`. The proof further splits on the gene structure of X:

**Case 1** (refined below) and Cases 2–4 each pick a pair `(g₁, g₂)` from X and apply a mutation `Z = X − g₁ − g₂ + g₁' + g₂'`. One then verifies `Z ≤ Y` by checking `σ(Z, j) ≤ σ(Y, j)` in three ranges: `j < m`, `m ≤ j ≤ k`, and `j > k`.

#### Case 1 — Type 1 mutation, `ε₁ = −`

**Setup.** Let `k` be the **minimal** index with `Y^(k) ≠ 0` and `aₖ < cₖ` (non-empty by Case A). Let `m` be the minimal rank of any gene in X.

- **`g₁ = g_{+}(m) = g^{(−1)^{m−1}}(m)`** — the gene of minimal rank `m` in X, with sign `(−1)^{m−1}` (positive when `m` odd, negative when `m` even).
- **`g₂ = g_{+}(k) = g^{(−1)^{k−1}}(k)`** — a gene of rank `k` in X, with sign `(−1)^{k−1}` (positive when `k` odd, negative when `k` even).

The sign of `g₂` depends on the parity of `k`, giving two sub-subcases:

| Sub-subcase | Parity of `k` | `g₂` as signed gene | Mutation in signed genes |
|---|---|---|---|
| **Case 1a** | `k` odd | `g₂ = g^+(k)` | `g^{(−1)^{m−1}}(m) + g^+(k) → g^{(−1)^{m−1}}(m−1) + g^−(k+1)` |
| **Case 1b** | `k` even | `g₂ = g^−(k)` | `g^{(−1)^{m−1}}(m) + g^−(k) → g^{(−1)^{m−1}}(m−1) + g^+(k+1)` |

In both sub-subcases the mutation shifts rank: `g₁' = g_{−}(m−1)` and `g₂' = g_{+}(k+1)`.

##### Key inequalities for Case 1a (`k` odd, `k ≥ 3`)

Since `k` is odd, we apply `cond_15_6` to Y at two consecutive indices to obtain a chain of inequalities needed to verify `Z ≤ Y`.

**Inequality 1:** `c_{k−1} − c_k ≤ d_{k−2} − d_{k−1}`

Apply `cond_15_6` to Y at index `k − 2` (which is odd, since `k` is odd):

```
cond_15_6 at k−2 (odd):  c_{(k−2)+1} − c_{(k−2)+2} ≤ d_{k−2} − d_{(k−2)+1}
                      ⟺  c_{k−1} − c_k ≤ d_{k−2} − d_{k−1}
```

**Inequality 2:** `d_{k−2} − d_{k−1} ≤ c_{k−3} − c_{k−2}`

Apply `cond_15_6` to Y at index `k − 3` (which is even, since `k` is odd):

```
cond_15_6 at k−3 (even):  d_{(k−3)+1} − d_{(k−3)+2} ≤ c_{k−3} − c_{(k−3)+1}
                       ⟺  d_{k−2} − d_{k−1} ≤ c_{k−3} − c_{k−2}
```

> Note: `cond_15_7` at `k−3` (even) gives the adjacent step `c_{k−2} − c_{k−1} ≤ d_{k−3} − d_{k−2}`, which is a different inequality. Both inequalities above require `cond_15_6`, not `cond_15_7`.

**Full chain** (`k ≥ 1` odd): applying `cond_15_6` at each index `i = k−2, k−3, …, 0` in turn gives the alternating chain:

```
c_{k−1} − c_k  ≤  d_{k−2} − d_{k−1}  ≤  c_{k−3} − c_{k−2}  ≤  ···  ≤  c_0 − c_1
```

Each step uses one of the two branches of `cond_15_6`, depending on the parity of `i`:

| Applied at `i` | Parity | Branch | Step |
|---|---|---|---|
| `k−2` | odd  | `c_{i+1} − c_{i+2} ≤ d_i − d_{i+1}` | `c_{k−1} − c_k ≤ d_{k−2} − d_{k−1}` |
| `k−3` | even | `d_{i+1} − d_{i+2} ≤ c_i − c_{i+1}` | `d_{k−2} − d_{k−1} ≤ c_{k−3} − c_{k−2}` |
| `k−4` | odd  | `c_{i+1} − c_{i+2} ≤ d_i − d_{i+1}` | `c_{k−3} − c_{k−2} ≤ d_{k−4} − d_{k−3}` |
| `k−5` | even | `d_{i+1} − d_{i+2} ≤ c_i − c_{i+1}` | `d_{k−4} − d_{k−3} ≤ c_{k−5} − c_{k−4}` |
| ⋮ | ⋮ | ⋮ | ⋮ |
| `1` | odd  | `c_{i+1} − c_{i+2} ≤ d_i − d_{i+1}` | `c_2 − c_3 ≤ d_1 − d_2` |
| `0` | even | `d_{i+1} − d_{i+2} ≤ c_i − c_{i+1}` | `d_1 − d_2 ≤ c_0 − c_1` |

Since `k` is odd, `k−2` is odd and the parities of `k−2, k−3, …, 0` alternate odd, even, odd, …, even. The full chain is the transitive closure of these `k−1` steps.

**Example (`k = 5`):**
```
c_4 − c_5  ≤  d_3 − d_4  ≤  c_2 − c_3  ≤  d_1 − d_2  ≤  c_0 − c_1
```
using `cond_15_6` at indices `3, 2, 1, 0` respectively.

**Deduction: `c_0 − c_1 < a_0 − a_1`**

This follows from two facts derivable from the hypotheses:

- **`a_0 = c_0`**: Since X and Y have the same rank `n`, we have `a_0 + b_0 = n = c_0 + d_0`. From `X ≤ Y`, dominance at level 0 gives `a_0 ≤ c_0` and `b_0 ≤ d_0`. Both differences are non-negative and sum to zero, so `a_0 = c_0`.

- **`a_1 < c_1`**: This is exactly the Case A hypothesis `a_1 < c_1`.

Therefore:
```
c_0 − c_1 = a_0 − c_1 < a_0 − a_1
```
where the equality uses `a_0 = c_0` and the strict inequality uses `c_1 > a_1` (so `−c_1 < −a_1`).

**Deduction: `a_0 − a_1 = b_1 − b_2 = a_2 − a_3 = ⋯ = b_{k−2} − b_{k−1} = a_{k−1} − a_k`**

Since X is a Pi element it satisfies conditions 15.6 and 15.7. In Case 1a (`k` odd), all genes in X have rank ≤ k, so `σ(X, j) = 0` for `j ≥ k`, giving `a_k = b_k = 0`. Backward induction from `j = k` using 15.6 and 15.7 at each index `i ∈ [0, k−2]` yields the alternating equalities:

| `cond_15_6` at `i` | `cond_15_7` at `i` | Combined equality |
|---|---|---|
| `i = 0` (even): `b_1 − b_2 ≤ a_0 − a_1` | `i = 0` (even): `a_0 − a_1 ≤ b_1 − b_2` | `a_0 − a_1 = b_1 − b_2` |
| `i = 1` (odd): `a_2 − a_3 ≤ b_1 − b_2` | `i = 1` (odd): `b_1 − b_2 ≤ a_2 − a_3` | `b_1 − b_2 = a_2 − a_3` |
| ⋮ | ⋮ | ⋮ |
| `i = k−3` (even): `b_{k−2} − b_{k−1} ≤ a_{k−3} − a_{k−2}` | `i = k−3` (even): `a_{k−3} − a_{k−2} ≤ b_{k−2} − b_{k−1}` | `a_{k−3} − a_{k−2} = b_{k−2} − b_{k−1}` |
| `i = k−2` (odd): `a_{k−1} − a_k ≤ b_{k−2} − b_{k−1}` | `i = k−2` (odd): `b_{k−2} − b_{k−1} ≤ a_{k−1} − a_k` | `b_{k−2} − b_{k−1} = a_{k−1} − a_k` |

By transitivity:
```
a_0 − a_1 = b_1 − b_2 = a_2 − a_3 = ⋯ = b_{k−2} − b_{k−1} = a_{k−1} − a_k
```

Call this common value `α`.

**Deduction: `a_k < c_k`, `b_{k−1} < d_{k−1}`, `a_{k−2} < c_{k−2}`, …, `b_2 < d_2`**

The full combined chain is:

```
c_{k−1}−c_k  ≤  d_{k−2}−d_{k−1}  ≤  ⋯  ≤  c_0−c_1  <  α  =  a_{k−1}−a_k  =  b_{k−2}−b_{k−1}  =  ⋯  =  a_0−a_1
```

Every Y-chain term is strictly less than `α`. Each Y-chain term is paired with the corresponding X-chain term (which equals `α`), and the strict comparison gives a Δ-inequality which forces a strict inequality between sigma components of X and Y:

| Y-chain term `<` X-chain term | Rearrangement | Consequence |
|---|---|---|
| `c_{k−1} − c_k < a_{k−1} − a_k` | `(c_{k−1}−a_{k−1}) < (c_k−a_k)`, i.e. `Δa_{k−1} < Δa_k` | `Δa_k ≥ 1`, so **`a_k < c_k`** |
| `d_{k−2} − d_{k−1} < b_{k−2} − b_{k−1}` | `(d_{k−2}−b_{k−2}) < (d_{k−1}−b_{k−1})`, i.e. `Δb_{k−2} < Δb_{k−1}` | `Δb_{k−1} ≥ 1`, so **`b_{k−1} < d_{k−1}`** |
| `c_{k−3} − c_{k−2} < a_{k−3} − a_{k−2}` | `Δa_{k−3} < Δa_{k−2}` | `Δa_{k−2} ≥ 1`, so **`a_{k−2} < c_{k−2}`** |
| `d_{k−4} − d_{k−3} < b_{k−4} − b_{k−3}` | `Δb_{k−4} < Δb_{k−3}` | `Δb_{k−3} ≥ 1`, so **`b_{k−3} < d_{k−3}`** |
| ⋮ | ⋮ | ⋮ |
| `d_1 − d_2 < b_1 − b_2` | `Δb_1 < Δb_2` | `Δb_2 ≥ 1`, so **`b_2 < d_2`** |
| `c_0 − c_1 < a_0 − a_1` | `Δa_0 < Δa_1` | `Δa_1 ≥ 1`, so **`a_1 < c_1`** *(original hypothesis)* |

Each step uses `Δ ≥ 0` (from dominance `X ≤ Y`) together with the strict inequality `Δ_j < Δ_{j+1}` to conclude `Δ_{j+1} ≥ 1`. The last row recovers the original Case A hypothesis `a_1 < c_1`, confirming consistency.

#### Cases 2–4: Case 1 fails (`ε₁ = +`)

When Case 1 fails, `ε₁ = +`, i.e. `g₁ = g_{+}(m) = g^{(−1)^{m−1}}(m)` is a positive gene at rank `m`. *(Details to be filled in. Currently `sorry` in the Lean proof.)*

---

### Case B: `a₁ = c₁` (so `b₁ < d₁`)

**Condition:** `(σ(X, 1)).1 = (σ(Y, 1)).1`, i.e. the first sigma components agree at level 1.

Since `hsigeq` forces `σ(X, 1) ≠ σ(Y, 1)` (when `Y^(1) ≠ 0`) and dominance gives `σ(X, 1) ≤ σ(Y, 1)`, the first components must be equal and the second must satisfy `b₁ < d₁` strictly.

The appropriate mutation in this case targets the level where `bⱼ < dⱼ`. *(Currently `sorry` in the Lean proof.)*
