# Proof Plan: `sigma_fst_diff`

**Statement:**
```lean
lemma sigma_fst_diff (hX : X ∈ Variety.Pi) :
    (sigma X k).1 - (sigma X (k + 1)).1 =
    (prime^[k] X).sum (fun g m ↦
      if g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive
      then (m : ℚ) else 0)
```

---

## Step 1 — Unfold `sigma` and reduce to a single chromosome

By definition, `sigma X k = signature (prime^[k] X)` and `sigma X (k+1) = signature (prime^[k+1] X)`.
Using `Function.iterate_succ_apply'`, the LHS becomes:

```
(signature (prime^[k] X)).1 - (signature (prime (prime^[k] X))).1
= (signature Y - signature Y.prime).1
```

where `Y := prime^[k] X`.

---

## Step 2 — Note that Y is in Pi

By `Variety.prime_mem_Pi_iterate hX`, we have `Y ∈ Variety.Pi`, so every gene in
`Y.support` is polarized: `g.type ≠ .NonPolarized`.

This means every gene in `Y.support` has type either `.Positive` or `.Negative`, and
falls into exactly one of the two alternating-basis cases:
- `g.type = Int.negOnePow ((g.rank : ℤ) - 1) • .Positive`   (**ofRankAlt Positive**)
- `g.type = Int.negOnePow ((g.rank : ℤ) - 1) • .Negative`   (**ofRankAlt Negative**)

---

## Step 3 — Decompose the signature difference by linearity

Using linearity of `signature` and `prime` (both are `AddMonoidHom`s), and the
`Finsupp.induction` or `map_finsuppSum` pattern:

```
(signature Y - signature Y.prime).1
= Y.sum (fun g m ↦ (m : ℚ) • (signature (single g 1) - signature (prime (single g 1))).1)
```

---

## Step 4 — Per-gene contribution

For each gene `g ∈ Y.support`, use `Gene.ofRankAlt_eq_gene g.rank_pos` to identify
`single g 1` with the appropriate alternating-basis chromosome.

**Sub-case A — ofRankAlt Positive** (`g.type = Int.negOnePow ((g.rank:ℤ)-1) • .Positive`):

- `Gene.ofRankAlt_eq_gene` gives `Gene.ofRankAlt g.rank .Positive = single g 1`.
- Rewrite using `prime_ofRankAlt_positive`:
  ```
  prime (Gene.ofRankAlt g.rank .Positive) = Gene.ofRankAlt (g.rank - 1) .Negative
  ```
- Now the signature difference is:
  `signature (Gene.ofRankAlt g.rank .Positive) - signature (Gene.ofRankAlt (g.rank-1) .Negative)`
- This equals `(1, 0)` by `signature_prime_ofRankAlt_positive g.rank_pos`,
  so the `.1` component contributes **1**.

**Sub-case B — ofRankAlt Negative** (`g.type = Int.negOnePow ((g.rank:ℤ)-1) • .Negative`):

- `Gene.ofRankAlt_eq_gene` gives `Gene.ofRankAlt g.rank .Negative = single g 1`.
- By `signature_prime_ofRankAlt_negative g.rank_pos`:
  `signature (Gene.ofRankAlt g.rank .Negative) - signature (prime (Gene.ofRankAlt g.rank .Negative)) = (0, 1)`
- So the `.1` component contributes **0**.

---

## Step 5 — Conclude

Combining Steps 3–4, each gene `g` with multiplicity `m` contributes `(m : ℚ)` to the
sum when it is ofRankAlt Positive, and `0` otherwise. This matches the RHS exactly:

```
Y.sum (fun g m ↦ if g.type = Int.negOnePow ((g.rank : ℤ) - 1) • .Positive
                 then (m : ℚ) else 0)
```

---

## Proof sketch

```lean
  simp only [sigma, Function.iterate_succ_apply']
  set Y := prime^[k] X with hY
  have hYPi : Y ∈ Variety.Pi := Variety.prime_mem_Pi_iterate hX
  -- Step 3: linearity
  rw [← Prod.fst_sub, ← map_sub, signature_prime, ← Finsupp.sum_sub_index]
  refine Finsupp.sum_congr (fun g hg ↦ ?_)
  -- Step 4: per-gene case split
  have hpol : g.type ≠ .NonPolarized := Variety.IsPolarized_def'.1 hYPi g hg
  rcases GeneType.polarized_cases hpol with hpos | hneg
  · -- Sub-case A: ofRankAlt Positive
    rw [show single g 1 = Gene.ofRankAlt g.rank .Positive from (Gene.ofRankAlt_eq_gene g.rank_pos).symm]
    rw [prime_ofRankAlt_positive]
    simp [signature_prime_ofRankAlt_positive g.rank_pos, hpos]
  · -- Sub-case B: ofRankAlt Negative
    rw [show single g 1 = Gene.ofRankAlt g.rank .Negative from (Gene.ofRankAlt_eq_gene g.rank_pos).symm]
    simp [signature_prime_ofRankAlt_negative g.rank_pos, hneg,
          show g.type ≠ Int.negOnePow _ • .Positive from ...]
```
