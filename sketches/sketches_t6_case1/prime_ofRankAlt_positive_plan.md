# Proof Plan: `prime_ofRankAlt_positive`

**Statement:**
```lean
lemma prime_ofRankAlt_positive {k : ℕ} (hk : 1 ≤ k) :
    prime (Gene.ofRankAlt k GeneType.Positive) = Gene.ofRankAlt (k - 1) GeneType.Negative
```

---

## Step 1 — Unfold both sides

Apply `Gene.ofRankAlt_def` and `prime_ofRank`.

- **LHS:** `prime (Gene.ofRank k (Int.negOnePow (k-1) • .Positive))` becomes `Gene.ofRank (k-1) (Int.negOnePow (k-1) • .Positive)`
- **RHS:** `Gene.ofRankAlt (k-1) .Negative` becomes `Gene.ofRank (k-1) (Int.negOnePow (((k-1 : ℕ) : ℤ) - 1) • .Negative)`

Both sides are now `Gene.ofRank (k-1) (...)`, so it remains to show the **type arguments are equal**.

---

## Step 2 — Simplify the integer exponent on the RHS

Use `omega` with `hk : 1 ≤ k` to rewrite:

```
((k - 1 : ℕ) : ℤ) - 1 = (k : ℤ) - 2
```

Remaining goal:
```
Int.negOnePow ((k : ℤ) - 1) • .Positive = Int.negOnePow ((k : ℤ) - 2) • .Negative
```

---

## Step 3 — Rewrite `.Negative` as `-.Positive`

Apply `← GeneType.neg_positive` on the RHS.

Remaining goal:
```
Int.negOnePow ((k : ℤ) - 1) • .Positive = Int.negOnePow ((k : ℤ) - 2) • (-.Positive)
```

---

## Step 4 — Apply `GeneType.negOnePow_smul_neg`

The lemma states: `n.negOnePow • (-ε) = (n + 1).negOnePow • ε`

Applied with `n = (k : ℤ) - 2` and `ε = .Positive`:
```
Int.negOnePow ((k : ℤ) - 2) • (-.Positive) = Int.negOnePow ((k : ℤ) - 2 + 1) • .Positive
```

---

## Step 5 — Close by arithmetic

Use `ring`: `(k : ℤ) - 2 + 1 = (k : ℤ) - 1`.

---

## Proof sketch

```lean
lemma prime_ofRankAlt_positive {k : ℕ} (hk : 1 ≤ k) :
    prime (Gene.ofRankAlt k GeneType.Positive) = Gene.ofRankAlt (k - 1) GeneType.Negative := by
  simp only [Gene.ofRankAlt_def, prime_ofRank]
  congr 1
  rw [show (((k - 1 : ℕ) : ℤ) - 1) = (k : ℤ) - 2 from by omega,
      ← GeneType.neg_positive, GeneType.negOnePow_smul_neg,
      show (k : ℤ) - 2 + 1 = (k : ℤ) - 1 from by ring]
```
