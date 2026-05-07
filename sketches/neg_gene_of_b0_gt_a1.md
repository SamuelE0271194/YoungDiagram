# Proof plan: `neg_gene_of_b0_gt_a1`

**Statement.** If `X ∈ Variety.Pi` and `a X 1 < b X 0`, then there exists a gene `g` with
`g.type = .Negative` and `0 < X g`.

The proof reduces to the single-gene case via `neg_type_of_b0_gt_a1_single`.

---

## Step 1 — Linearity decomposition

Using additivity of `signature` and `prime` over the support of `X`, write

```
b X 0 = Σ_{g ∈ supp(X)}  X g · b(single g 1) 0
a X 1 = Σ_{g ∈ supp(X)}  X g · a(single g 1) 1
```

These follow from `signature_single`, `prime_single`, and linearity of `signature`/`prime`.

---

## Step 2 — Positive-sum argument

From `h : a X 1 < b X 0`, the weighted difference

```
Σ_{g ∈ supp(X)}  X g · (b(single g 1) 0 − a(single g 1) 1)  >  0
```

so by a `Finsupp.sum` positivity argument there exists `g₀ ∈ supp(X)` with `0 < X g₀`
and `a(single g₀ 1) 1 < b(single g₀ 1) 0`.

---

## Step 3 — Single gene is in `Variety.Pi`

Show `single g₀ 1 ∈ Variety.Pi` from `hX : X ∈ Variety.Pi` and `0 < X g₀`.
This should follow from a component-membership property of `Variety.Pi`.

---

## Step 4 — Apply `neg_type_of_b0_gt_a1_single`

With `single g₀ 1 ∈ Variety.Pi` (Step 3) and `a(single g₀ 1) 1 < b(single g₀ 1) 0`
(Step 2), apply `neg_type_of_b0_gt_a1_single` to get `g₀.type = .Negative`.

---

## Step 5 — Conclude

Return `⟨g₀, step 4, 0 < X g₀⟩`.
