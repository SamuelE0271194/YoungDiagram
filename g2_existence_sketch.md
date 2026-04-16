# Existence of g₂ = g₊(k) in Case 1

## Setting

We are in **Case 1** of `exists_mutation_le_fifteen_ten`:

- `ha : ∃ k, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧ (sigma X.1 k).1 < (sigma Y.1 k).1`
- `hε₁ : g₁.type = .Negative` (the gene of minimal rank in X is negative)
- `k` extracted from `ha`, so `hak : (sigma X.1 k).1 < (sigma Y.1 k).1`, i.e., `a_k < c_k`

We want to show:

```
hg₂_exists : ∃ (g₂ : Gene), g₂.rank = k ∧
    g₂.type = (Int.negOnePow ((k : ℤ) - 1) • .Positive) ∧
    0 < X.1.val g₂
```

That is, X contains a gene of rank `k` with alternating-sign type
`(-1)^{k-1} • .Positive` — which is `.Positive` when `k` is odd and `.Negative` when `k` is even.

---

## Key observation: sigma differences count alternating-sign genes

The sigma function is defined as `sigma X k = signature (prime^[k] X)`.

Applying `prime` once replaces each gene `g` by `primeGene g = Gene.ofRank (g.rank - 1) g.type`
(rank decreases by 1, type is preserved; rank-1 genes vanish).

Therefore `prime^[k-1] X` has, for each gene `g` in X with `g.rank = k`, a corresponding
rank-1 gene of the same type in `prime^[k-1] X`. The signature contributions of rank-1 genes are:

| Type     | Signature |
|----------|-----------|
| .Positive | (1, 0)   |
| .Negative | (0, 1)   |

So the difference `a_{k-1} - a_k = (sigma X (k-1)).1 - (sigma X k).1` equals:

- **k odd** (alternating type is `.Positive`):
  `Σ_{g.rank=k, g.type=.Positive} X(g)`
- **k even** (alternating type is `.Negative`):
  `0` (all .Negative rank-k genes contribute to `b_{k-1} - b_k`, not to `a`)

---

## Contradiction argument

**Assume** X has no gene of rank `k` with type `(-1)^{k-1} • .Positive`.

### Case k = 1 (k odd, alternating type is `.Positive`):

If X has no `.Positive` rank-1 gene, then `a_0 - a_1 = 0`, i.e., `a_0 = a_1`.

But:
- `a_0 = c_0` — because X and Y have equal ranks, so `a_0 + b_0 = n = c_0 + d_0`, and from
  dominance `X ≤ Y`: `a_0 ≤ c_0` and `b_0 ≤ d_0`; both differences non-negative summing to zero
  forces `a_0 = c_0`.
- `c_0 ≥ c_1` — by `Sigma.cond_15_2` (sigma is antitone).
- `a_1 < c_1` — from `hak` (with `k = 1`).

Chain: `a_0 = a_1 < c_1 ≤ c_0 = a_0`. Contradiction (`a_0 < a_0`).

### Case k > 1, general:

The chain equalities from cond_15_6 and cond_15_7 applied to X give:

```
α  :=  a_0 - a_1  =  b_1 - b_2  =  a_2 - a_3  =  …  =  a_{k-1} - a_k
```

(This uses the fact that all sigma components of X vanish at level ≥ k, which holds because
the maximal rank of any gene in X is at most k when g₁ is the minimal-rank gene and g₂ is
claimed to have rank k — but formally requires knowing X has no genes of rank > k, which is
part of the Case 1 setup.)

If X has no g₊(k), then `a_{k-1} = a_k` (for k odd), giving `α = 0`.

But from the Y-side chain (cond_15_6 for Y) and `a_0 = c_0` with `a_1 < c_1`:

```
0  =  α  =  a_0 - a_1  >  c_0 - c_1  ≥  0
```

Contradiction.

---

## Lean sketch

```lean
-- Extract k from ha
obtain ⟨k, hkpos, hYkne, hak⟩ := ha

-- g₂ = g_+(k): gene of rank k with alternating-sign type in X.
-- Existence: if no such g₂, applying prime^[k-1] and then prime once more to X
-- leaves the a-component (k odd) or b-component (k even) unchanged, since the
-- rank-k genes with the alternating sign are precisely those contributing to
-- a_{k-1} - a_k (k odd) or b_{k-1} - b_k (k even).
-- For k = 1: absence ⟹ a_0 = a_1, contradicting a_1 < c_1 ≤ c_0 = a_0.
-- For k > 1: chain equalities (cond_15_6/15_7 on X) give α = a_0 - a_1 = 0,
-- contradicting α > c_0 - c_1 ≥ 0 (from a_1 < c_1 and a_0 = c_0).
have hg₂_exists : ∃ (g₂ : Gene), g₂.rank = k ∧
    g₂.type = (Int.negOnePow ((k : ℤ) - 1) • GeneType.Positive) ∧
    0 < X.1.val g₂ := by
  -- Key lemma needed: a_{k-1} - a_k = Σ_{g.rank=k, g.type=(-1)^{k-1}•.Positive} X(g)
  -- This follows from signature_prime_fst and signature_ofRank_one_positive/negative.
  -- Then show this sum > 0 by contradiction:
  --   assume sum = 0 ⟹ a_{k-1} = a_k
  --   use a_0 = c_0 (equal-rank lemma) + a_k < c_k + cond_15_2 on Y to derive a_0 < a_0.
  sorry
obtain ⟨g₂, hg₂rank, hg₂type, hXg₂⟩ := hg₂_exists
```

---

## Relevant lemmas

| Lemma | Statement |
|-------|-----------|
| `Chromosome.signature_ofRank_one_positive` | `(Gene.ofRank 1 .Positive).signature = (1, 0)` |
| `Chromosome.signature_ofRank_one_negative` | `(Gene.ofRank 1 .Negative).signature = (0, 1)` |
| `Chromosome.signature_prime_fst` | `(signature X.prime).1 = X.sum (fun g m ↦ m • (primeGene g).signature.1)` |
| `Sigma.cond_15_2` | sigma first component is antitone: `a_{k+1} ≤ a_k` |
| `Sigma.cond_15_6` / `cond_15_7` | chain (in)equalities for Pi elements |
| `Sigma.cond_15_8` | dominance: `X ≤ Y ⟹ a_k ≤ c_k` and `b_k ≤ d_k` |
