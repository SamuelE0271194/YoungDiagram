# Case 4, `hzero` sub-case: contradiction sketch

## Setup

We are inside `intro hzero` where `hzero : prime^[g₁.rank] X.1.val = 0`,
trying to prove `False` from `hXY : X.1 < Y.1`.

Key facts already established:

| Hypothesis | Statement |
|---|---|
| `hX_eq_g₁ hzero` | `X.1.val = single g₁ 1` |
| `hX_rank_eq` | `X.1.val.rank = g₁.rank` |
| `hYX_rank` | `Y.1.val.rank = X.1.val.rank` |
| `hY_maxrank` | `Y.1.val.maxRank = X.1.val.maxRank = g₁.rank` |
| `hg₁_ge2` | `2 ≤ g₁.rank` |
| `hXY` | `X.1 < Y.1` in the Pi partial order |

---

## Step 1: Y has exactly one gene with multiplicity 1

We have `Y.1.val.rank = Y.1.val.maxRank = g₁.rank`.

**Why this forces Y = single g₂ 1:**

Write `rank Y = Σ_{g ∈ support} Y(g) * g.rank = g₁.rank`.

Let `g_max` be any gene in Y's support with `g_max.rank = maxRank Y = g₁.rank`
(such a gene exists because `maxRank Y = g₁.rank ≥ 2 > 0`, so the support is nonempty
and some gene achieves the sup).

Since every `g.rank ≥ 1` and `Y(g) ≥ 1` for `g ∈ support`:

- `Y(g_max) * g₁.rank + Σ_{g ≠ g_max} Y(g) * g.rank = g₁.rank`

If any other gene `g' ≠ g_max` is in the support, its term contributes `≥ 1`, so:

- `Y(g_max) * g₁.rank ≤ g₁.rank - 1`
- But `Y(g_max) ≥ 1` implies `Y(g_max) * g₁.rank ≥ g₁.rank`. Contradiction.

So `g_max` is the **only** gene in Y's support, and `Y(g_max) * g₁.rank = g₁.rank`
gives `Y(g_max) = 1`.

Hence **`Y.1.val = single g₂ 1`** for some polarized gene `g₂` with `g₂.rank = g₁.rank`.

**Lean proof sketch:**
```lean
have hY_eq_g₂ : ∃ g₂ : Gene, g₂.rank = g₁.rank ∧ Y.1.val = Finsupp.single g₂ 1 := by
  exact rank_one Y.1.val ... -- analogous to hX_eq_g₁ but using hY_maxrank
```

---

## Step 2: Contradiction from X < Y

We now have:
- `X.1.val = single g₁ 1`
- `Y.1.val = single g₂ 1`
- `g₁.rank = g₂.rank =: r` with `r ≥ 2`
- Both `g₁`, `g₂` are polarized (types ∈ {Positive, Negative})
- `X.1 < Y.1` in the Pi order

**At sigma step `k = r - 1`:**

```
sigma(X, r-1) = signature(prime^[r-1] (single g₁ 1))
              = signature(ofRank 1 g₁.type)     -- by prime_iterate_ofRank

sigma(Y, r-1) = signature(prime^[r-1] (single g₂ 1))
              = signature(ofRank 1 g₂.type)     -- by prime_iterate_ofRank
```

From `signature_ofRank_one_positive/negative`:
- `signature(ofRank 1 Positive) = (1, 0)`
- `signature(ofRank 1 Negative) = (0, 1)`

**Case A: `g₁.type = g₂.type`.**
Then `g₁ = g₂` (same rank, same type), so `X.1.val = Y.1.val`, contradicting `X.1 < Y.1`.

**Case B: `g₁.type ≠ g₂.type`.**
Since both are polarized, one is Positive and one is Negative.
The two sigma values are `(1,0)` and `(0,1)` in some order.

`X < Y` requires `sigma(X, r-1) ≤ sigma(Y, r-1)` (componentwise).
- `(1,0) ≤ (0,1)` fails (first component: `1 ≤ 0`).
- `(0,1) ≤ (1,0)` fails (second component: `1 ≤ 0`).

Either way, contradiction.

**Lean proof sketch:**
```lean
-- Get hle : sigma(X, r-1) ≤ sigma(Y, r-1) from X < Y
have hle := (le_iff_dominates.mp hXY.le) (g₁.rank - 1)
-- Rewrite both sides using hX_eq_g₁ hzero and hY_eq_g₂
rw [Sigma.sigma, hX_eq_g₁ hzero, ← Gene.ofRank_eq_gene,
    prime_iterate_ofRank, show r - (r-1) = 1 by omega] at hle
-- Similarly rewrite Y side
-- Now hle : signature(ofRank 1 g₁.type) ≤ signature(ofRank 1 g₂.type)
-- Case split on g₁.type and g₂.type (both Positive or Negative)
-- simp [signature_ofRank_one_positive, signature_ofRank_one_negative] to get (1,0) ≤ (0,1) or vice versa
-- Close with omega / linarith
```
