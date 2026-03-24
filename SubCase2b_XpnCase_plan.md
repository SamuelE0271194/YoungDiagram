# Plan for the sorry at line 482 (Sub-case 2b, X ⊇ g⁺(r) + g⁻(r))

## Context

At line 482, we are in sub-case 2b, in the branch where X contains a positive gene `gpos` and
a negative gene `gneg` of the same rank. We have proved `hY_no_gene` and need to construct a
`Pi.Step X Z` with `Z ≤ Y`.

Available hypotheses:
- `r := gpos.rank`, `hr : 1 ≤ r` (from `gpos.rank_pos`)
- `hgpos : gpos.type = .Positive`, `hgneg : gneg.type = .Negative`
- `hrank : gpos.rank = gneg.rank` (so `gneg.rank = r`)
- `hXgpos : 0 < X.val gpos`, `hXgneg : 0 < X.val gneg`
- `hY_no_gene : ∀ g, g.rank = r → Y.val g = 0`
- `hsigeq : ∀ k > 0, prime^[k] Y.val ≠ 0 → Sigma.sigma X k ≠ Sigma.sigma Y k`
- `hXY : X < Y` (both in Pi_n (m+2)), in particular `hXY.le : X ≤ Y`
- `hcommon : ∀ g, ¬(0 < X.val g ∧ 0 < Y.val g)` (disjoint supports)

Paper reference: Djoković 1982, p. 245 (bottom), case "X ⊇ g⁺(k) + g⁻(k)".

---

## Step 1 — Prove `prime^[r] Y.val ≠ 0`

### Sub-step 1a: `(signature (prime^[r-1] X.val)).1 ≥ 1`

- `prime^[r-1] (Gene.ofRank r .Positive) = Gene.ofRank 1 .Positive`
  by `prime_iterate_ofRank` (rank r − (r−1) = 1).
- `signature_ofRank_one_positive : (Gene.ofRank 1 .Positive).signature = (1, 0)`,
  so first component = 1.
- Since `X.val gpos ≥ 1`, the map `prime^[r-1]` (an `AddMonoidHom`) satisfies
  `prime^[r-1] X.val ≥ prime^[r-1] (Finsupp.single gpos 1)` pointwise
  (monotonicity from `AddMonoidHom` applied to a Finsupp ≥ a single).
- `signature` is also an `AddMonoidHom`, so its first component is monotone.
- Therefore `(signature (prime^[r-1] X.val)).1 ≥ 1`.

### Sub-step 1b: `(signature (prime^[r-1] Y.val)).1 ≥ 1`

From `le_iff_dominates.mp hXY.le (r-1)`:
```
signature (prime^[r-1] X.val) ≤ signature (prime^[r-1] Y.val)
```
First component: `(sig(prime^[r-1] Y.val)).1 ≥ (sig(prime^[r-1] X.val)).1 ≥ 1`.

### Sub-step 1c: `prime^[r-1] Y.val ≠ 0`

If `prime^[r-1] Y.val = 0` then `signature 0 = (0,0)`, contradicting `.1 ≥ 1`.

### Sub-step 1d: `prime^[r] Y.val ≠ 0`

- `prime^[r-1]` applied to a gene of rank exactly r gives rank 1.
  But `hY_no_gene` says Y has no genes of rank r, so none of the genes in `prime^[r-1] Y.val`
  come from Y's rank-r genes.  All come from Y's genes of rank ≥ r+1, which shift to rank ≥ 2.
- Therefore every gene in `prime^[r-1] Y.val` has rank ≥ 2.
- `prime^[r] Y.val = prime (prime^[r-1] Y.val)`. Applying `prime` to a gene of rank ≥ 2
  gives a gene of rank ≥ 1 (nonzero). Since `prime^[r-1] Y.val ≠ 0` and all its genes have
  rank ≥ 2, applying `prime` preserves non-zeroness.
  **Auxiliary lemma needed** (may prove inline):
  *"If C ≠ 0 and every gene g in C's support has g.rank ≥ 2, then prime C ≠ 0."*

---

## Step 2 — Get a strict sigma inequality at level r

```lean
have hYr : Chromosome.prime^[r] Y.val ≠ 0 := -- from Step 1
have hsig_ne : Sigma.sigma X r ≠ Sigma.sigma Y r := hsigeq r gpos.rank_pos hYr
have hle_r : Sigma.sigma X r ≤ Sigma.sigma Y r := le_iff_dominates.mp hXY.le r
-- ≤ and ≠ together give at least one strict component:
have hsig_lt : (Sigma.sigma X r).1 < (Sigma.sigma Y r).1 ∨
               (Sigma.sigma X r).2 < (Sigma.sigma Y r).2 := by
  rcases lt_or_eq_of_le hle_r.1 with h1 | h1
  · exact Or.inl h1
  · rcases lt_or_eq_of_le hle_r.2 with h2 | h2
    · exact Or.inr h2
    · exact absurd (Prod.ext h1.symm h2.symm) hsig_ne
```

---

## Step 3 — Construct the mutation X → Z

Case split on `hsig_lt`. Both cases are symmetric.

### Primitive mutation pieces

Set `ε := .Positive` if `(Sigma.sigma X r).1 < (Sigma.sigma Y r).1`, else `ε := .Negative`.

In either case `hε : ε ≠ .NonPolarized` holds trivially.

Define:
- `X1 := Variety.Pi.X1 hε (le_refl r) gpos.rank_pos`
  — equals `Gene.ofRank r ε + Gene.ofRank r (-ε)` as a Pi chromosome.
  For ε = Positive: `= Gene.ofRank r .Positive + Gene.ofRank r .Negative`
                    `= Finsupp.single gpos 1 + Finsupp.single gneg 1`
                    (since `gpos = ⟨r, .Positive, _⟩` and `gneg = ⟨r, .Negative, _⟩`).
- `Y1 := Variety.Pi.Y1 hε (le_refl r) gpos.rank_pos`
  — equals `Gene.ofRank (r-1) (-ε) + Gene.ofRank (r+1) ε`.
- `rest.val := X.val - Finsupp.single gpos 1 - Finsupp.single gneg 1`
  (well-defined and nonneg since `X.val gpos ≥ 1` and `X.val gneg ≥ 1`).
- `rest ∈ Pi`: rest is a sub-Finsupp of X.val, so its support ⊆ support of X.val,
  hence all its genes are polarized (type ≠ NonPolarized). Use `mem_Pi_iff` + `IsPolarized_def'`.

### Key equation

```lean
have hX_eq : X1.val + rest.val = X.val := by
  ext g; simp [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, hXgpos, hXgneg]
  -- Case g = gpos: 1 + (X.val gpos - 1) = X.val gpos  (using hXgpos)
  -- Case g = gneg: similar
  -- Other g: 0 + X.val g = X.val g
```

### Pi.Step construction

```lean
have hprim : Pi.Primitive X1 Y1 :=
  Pi.Primitive.type1 ε hε (le_refl r) gpos.rank_pos
have hstep_raw : Pi.Step (X1 + ⟨rest.val, rest_mem⟩) (Y1 + ⟨rest.val, rest_mem⟩) :=
  Pi.Step.mk X1 Y1 ⟨rest.val, rest_mem⟩ hprim
-- X = X1 + rest (as Pi subtypes, via hX_eq):
have hstep : Pi.Step X ⟨Y1.val + rest.val, Z_mem⟩ := by
  convert hstep_raw using 1
  exact Subtype.ext hX_eq.symm
```

Return `⟨⟨Y1.val + rest.val, Z_mem⟩, hstep, ?_⟩`.

---

## Step 4 — Prove Z ≤ Y

Goal: `Y1.val + rest.val ≤ Y.val` (as Chromosomes, unfolded from Pi ≤).

```lean
rw [le_iff_dominates]
intro j
```

Split into three ranges. In all cases use:
- `sig(prime^[j] (A + B)) = sig(prime^[j] A) + sig(prime^[j] B)` (linearity of prime and sig).
- `sig(prime^[j] X.val) = sig(prime^[j] X1.val) + sig(prime^[j] rest.val)` (since X = X1 + rest).

### Case j < r (i.e., j ≤ r−1)

**Claim**: `sig(prime^[j] Z.val) = sig(prime^[j] X.val)`.

Key: `sig(prime^[j] Y1.val) = sig(prime^[j] X1.val)`.

Use `mutation_type1_iterate_signature_eq` with `m = n = 1`, `k = r−1`, `i = j`, `hi : j ≤ r−1`:
```lean
mutation_type1_iterate_signature_eq hε (le_refl 1) le_refl j (r-1) (by omega)
-- proves sig(prime^[j](Gene.ofRank r ε + Gene.ofRank r (-ε)))
--       = sig(prime^[j](Gene.ofRank (r-1) (-ε) + Gene.ofRank (r+1) ε))
```

Therefore:
```
sig(prime^[j] Z) = sig(prime^[j] Y1) + sig(prime^[j] rest)
                 = sig(prime^[j] X1) + sig(prime^[j] rest)   -- by above
                 = sig(prime^[j] X)                          -- since X = X1 + rest
                 ≤ sig(prime^[j] Y)                          -- from hXY.le
```

### Case j = r

**Claim**: `sig(prime^[r] Z.val) = sig(Gene.ofRank 1 ε) + sig(prime^[r] X.val)`.

Key computations via `prime_iterate_ofRank`:
| Gene | After `prime^[r]` | Signature |
|------|-------------------|-----------|
| `Gene.ofRank r ε` | `Gene.ofRank 0 ε = 0` | `(0, 0)` |
| `Gene.ofRank r (-ε)` | `0` | `(0, 0)` |
| `Gene.ofRank (r+1) ε` | `Gene.ofRank 1 ε` | `sig(Gene.ofRank 1 ε)` |
| `Gene.ofRank (r-1) (-ε)` | `Gene.ofRank 0 (-ε) = 0` | `(0, 0)` |

So `sig(prime^[r] X1) = (0, 0)` and `sig(prime^[r] Y1) = sig(Gene.ofRank 1 ε)`.

Hence:
```
sig(prime^[r] Z) = sig(prime^[r] Y1) + sig(prime^[r] rest)
                 = sig(Gene.ofRank 1 ε) + sig(prime^[r] rest)
                 = sig(Gene.ofRank 1 ε) + sig(prime^[r] X)  -- since sig(prime^[r] X1) = 0
```

For ε = Positive: `sig(Gene.ofRank 1 .Positive) = (1, 0)` (by `signature_ofRank_one_positive`).
Need `(a_r + 1, b_r) ≤ (c_r, d_r)`:
- `.1`: `a_r + 1 ≤ c_r` because `a_r < c_r` (our case hypothesis). ✓
- `.2`: `b_r ≤ d_r` from `le_iff_dominates.mp hXY.le r`. ✓

For ε = Negative: `sig(Gene.ofRank 1 .Negative) = (0, 1)`. Need `(a_r, b_r + 1) ≤ (c_r, d_r)`. ✓

### Case j > r (i.e., j ≥ r+1)

**Claim**: `sig(prime^[j] Z.val) = sig(prime^[j] X.val)`.

All four genes in X1 and Y1 have rank ≤ r+1. After `prime^[j]` with j ≥ r+1:
- `prime^[j](Gene.ofRank r ε) = Gene.ofRank (r-j) ε = 0` (since r < j)
- Similarly for the other three genes.

So `sig(prime^[j] X1) = sig(prime^[j] Y1) = (0,0)`. Then:
```
sig(prime^[j] Z) = sig(prime^[j] Y1) + sig(prime^[j] rest)
                 = sig(prime^[j] rest)
                 = sig(prime^[j] X1) + sig(prime^[j] rest)   -- add zero
                 = sig(prime^[j] X)
                 ≤ sig(prime^[j] Y)                          -- from hXY.le
```

---

## Summary of key lemmas

| Lemma | Where | Purpose |
|-------|-------|---------|
| `prime_iterate_ofRank` | `Chromosome.lean` | `prime^[k](Gene.ofRank n ε) = Gene.ofRank (n-k) ε` |
| `mutation_type1_iterate_signature_eq` | `MutationsAux.lean` | Signature cancellation for j < r |
| `signature_ofRank_one_positive` | `Chromosome.lean` | `sig(g⁺(1)) = (1, 0)` |
| `signature_ofRank_one_negative` | `Chromosome.lean` | `sig(g⁻(1)) = (0, 1)` |
| `le_iff_dominates` | `Chromosome.lean` | Convert `≤` to pointwise sigma comparison |
| `iterate_map_add` | Mathlib | `prime^[k](A + B) = prime^[k] A + prime^[k] B` |
| `map_add` (signature) | Mathlib | `sig(A + B) = sig(A) + sig(B)` |
| `X1_eq`, `Y1_eq` | `Mutations.lean` | Unfold the Pi.X1/Y1 definitions |

---

## Main difficulty

**Step 1d** (prime^[r] Y ≠ 0) is the trickiest Lean step. The cleanest route needs an auxiliary
lemma:

> **Aux**: If `C : Chromosome`, `C ≠ 0`, and `∀ g ∈ C.support, 2 ≤ g.rank`, then `prime C ≠ 0`.

Proof sketch: `prime C = C.sum (fun g m => m • Gene.ofRank (g.rank - 1) g.type)`. If all
`g.rank ≥ 2` then `g.rank - 1 ≥ 1 > 0` so every `Gene.ofRank (g.rank-1) g.type ≠ 0`. Since
`C ≠ 0` there is some gene `g` with `C g > 0`. That gene contributes a nonzero term to `prime C`.

This lemma can be proved inline using `Finsupp.sum_ne_zero` (or similar) and
`Finsupp.support_nonempty_iff`.
