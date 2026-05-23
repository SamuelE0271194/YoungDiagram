# Existence of `g₂` in Case 1 of §15.10

## Setting

We are inside `exists_mutation_le_fifteen_ten`, in **Case A** (`a₁ < c₁`) and **Case 1** (`ε₁ = −`),
meaning:

- `g₁` is the gene of **minimal rank** `m` in X, with `g₁.type = .Negative`.
- We are in **Case A**: there exists a minimal `k ≥ 1` with `prime^[k] Y ≠ 0` and `aₖ < cₖ`.
- In particular, `a₁ < c₁` holds (taking `k = 1` if 1 is the minimal such index, or relying on
  the Case A hypothesis directly).

The goal is to show:

> **Claim.** X contains a gene `g₂` with `g₂.rank = k` and
> `g₂.type = (Gene.ofRankAlt k .Positive).type`, i.e., `g₂` is the gene of rank `k` whose
> type alternates as `(−1)^{k−1}`:
> - `g₂ = Gene.ofRank k .Positive` when `k` is **odd**,
> - `g₂ = Gene.ofRank k .Negative` when `k` is **even**.

---

## Key background: how `prime` changes the first signature component

Recall:
- `signature : Chromosome → ℚ × ℚ`, with components `(a, b)`.
- `prime` lowers the rank of each constituent gene by 1, preserving its type.
- `σ(X, j) = signature(prime^[j] X)`, so `aⱼ = (σ(X, j)).1`.

**Lemma (sign of `Δa` under one prime).** For a single gene `Gene.ofRankAlt r ε`:
- `ε = .Positive`: `Gene.ofRankAlt r .Positive` is `Gene.ofRank r .Positive` (r odd) or
  `Gene.ofRank r .Negative` (r even). In **both** cases, one application of `prime` decreases
  the first signature component by exactly **1**:
  - r odd → gene `(r, .Positive)`, sig.1 = `(r+1)/2`; after prime → `(r-1, .Positive)` with
    sig.1 = `(r-1)/2`. Change = **−1**.
  - r even → gene `(r, .Negative)`, sig.1 = `r/2`; after prime → `(r-1, .Negative)` with
    sig.1 = `(r-2)/2`. Change = **−1**.
- `ε = .Negative`: `Gene.ofRankAlt r .Negative` is `Gene.ofRank r .Negative` (r odd) or
  `Gene.ofRank r .Positive` (r even). In **both** cases, `prime` leaves the first component
  unchanged and decreases the second component by exactly **1**:
  - r odd → gene `(r, .Negative)`, sig.1 = `(r-1)/2`; after prime → `(r-1, .Negative)` with
    sig.1 = `(r-1)/2`. Change = **0**.
  - r even → gene `(r, .Positive)`, sig.1 = `r/2`; after prime → `(r-1, .Positive)` with
    sig.1 = `r/2`. Change = **0**.

**Summary:** every application of `prime` changes `a` by `−(number of Gene.ofRankAlt · .Positive genes)`. Equivalently:
```
a₀ − a₁  =  Σ_{r ≥ 1} (multiplicity of Gene.ofRankAlt r .Positive gene in X)
```

---

## Proof of the Claim by contradiction

**Assume** X contains **no** gene of type `Gene.ofRankAlt r .Positive` for any `r ≥ 1`, i.e.,
every gene in `X` is of the form `Gene.ofRankAlt r .Negative` for some `r`.

By the lemma above, `prime` leaves the first signature component unchanged:
```
a₀ − a₁ = 0,   i.e.,   a₀ = a₁.          … (*)
```

Now use the following two facts, both available in the current proof context:

**Fact 1 (`a₀ = c₀`).** X and Y have the same rank `n = m + 2`. Since
`signature_sum_eq_rank` gives `a₀ + b₀ = n = c₀ + d₀`, and dominance `X ≤ Y` (from `hXY.le`)
gives `a₀ ≤ c₀` and `b₀ ≤ d₀`, both differences are non-negative and sum to zero. Therefore:
```
a₀ = c₀.          … (**)
```

**Fact 2 (`a₁ < c₁`).** This is directly the Case A hypothesis `ha` (the minimal k is at most 1,
or we take k = 1):
```
a₁ < c₁.          … (***)
```

**Fact 3 (`c₁ ≤ c₀`).** By `Sigma.antitone`, `σ(Y, ·)` is antitone, so:
```
c₁ ≤ c₀.          … (****)
```

**Combining:**
```
a₀  =  a₁              (from *)
    <  c₁              (from ***)
    ≤  c₀              (from ****)
    =  a₀              (from **)
```

This gives `a₀ < a₀`, a contradiction.

Therefore X must contain at least one gene of type `Gene.ofRankAlt r .Positive` for some `r`.
The specific gene `g₂` is then chosen at rank `k` (the minimal index with `aₖ < cₖ` from `ha`),
whose existence at rank `k` in X is argued separately (e.g., by looking at the first level where
the sigma drops and tracking which rank of gene must be contributing to the decrease in `a`).

---

## Lean sketch

```lean
-- Inside Case 1 (hε₁ : g₁.type = .Negative), after obtaining k from ha.
obtain ⟨k, hkpos, hYkne, hak⟩ := ha
-- The claim: ∃ g₂ : Gene, g₂.rank = k ∧ g₂.type = (Int.negOnePow (k-1) • .Positive) ∧ 0 < X.1.val g₂
by_contra hno_g₂
push_neg at hno_g₂
-- hno_g₂ : ∀ g : Gene, g.rank = k → g.type = ... → X.1.val g = 0
-- Derive a₀ = a₁ from the fact that every gene in X is of ofRankAlt · .Negative type.
-- (All genes decrease only b, not a.)
have ha₀_eq_a₁ : (Sigma.sigma X.1 0).1 = (Sigma.sigma X.1 1).1 := by
  simp only [Sigma.sigma]
  -- signature_prime_fst: (signature (prime X)).1 = X.sum (fun g m ↦ m * (primeGene g).sig.1)
  -- For each gene g in X, primeGene g has the same type with rank g.rank - 1.
  -- Since X has no ofRankAlt · .Positive genes, the first component never decreases.
  sorry
-- Derive a₀ = c₀ from equal ranks and dominance.
have ha₀_eq_c₀ : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 := by
  -- a₀ + b₀ = rank X = rank Y = c₀ + d₀, and a₀ ≤ c₀ and b₀ ≤ d₀ from hXY.le.
  sorry
-- Now derive the contradiction.
have hc₁_le_c₀ : (Sigma.sigma Y.1 1).1 ≤ (Sigma.sigma Y.1 0).1 :=
  (Sigma.antitone Y.1 (Nat.le_succ 0)).1
-- a₁ = a₀ = c₀ ≥ c₁ > a₁, contradiction.
linarith [ha₀_eq_a₁, ha₀_eq_c₀, hc₁_le_c₀, hak]
```

---

## Summary

The existence of `g₂ : Gene` of type `Gene.ofRankAlt k .Positive` in X follows by contradiction:
if no such gene existed, every prime application would preserve `a` (only `b` decreases), giving
`a₀ = a₁`. But `a₀ = c₀` (equal ranks + dominance) and `a₁ < c₁ ≤ c₀` (Case A + antitone),
so `a₀ = a₁ < c₁ ≤ c₀ = a₀`, which is impossible.
