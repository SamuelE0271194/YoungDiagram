# Proof Sketch: `prime_iterate_sum_pos_eq`

## Statement

```lean
lemma prime_iterate_sum_pos_eq (hk : Even k) :
    (prime^[k] X).sum (fun g m ↦
      if g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive
      then (m : ℚ) else 0) =
    ∑ g ∈ X.support.filter (fun g =>
      k < g.rank ∧ g.type = Int.negOnePow ((g.rank : ℤ) - 1) • GeneType.Positive),
    (X g : ℚ)
```

## Key lemmas available

- `prime_iterate_coeff k X g : (prime^[k] X) g = X ⟨g.rank + k, g.type, _⟩`
- `Int.negOnePow_add n₁ n₂ : (n₁ + n₂).negOnePow = n₁.negOnePow * n₂.negOnePow`
- `Int.negOnePow_even hn : n.negOnePow = 1` (when `Even n`)
- `Finset.sum_nbij` for change-of-variables in a `Finset.sum`

---

## Step 1 — unfold `Finsupp.sum` and rewrite coefficients

`Finsupp.sum` is `∑ g ∈ support, f g (coeff g)`. Rewrite each `(prime^[k] X) g` via `prime_iterate_coeff` to get:

```
∑ g ∈ (prime^[k] X).support,
  if g.type = negOnePow(g.rank - 1) • Pos then (X ⟨g.rank + k, g.type, _⟩ : ℚ) else 0
```

## Step 2 — absorb the `if` into the summation domain

`Finset.sum_filter` turns `∑ g ∈ S, if P g then f g else 0` into `∑ g ∈ S.filter P, f g`. After this the goal is:

```
∑ g ∈ (prime^[k] X).support.filter (fun g => g.type = negOnePow(g.rank - 1) • Pos),
  (X ⟨g.rank + k, g.type, _⟩ : ℚ)
=
∑ g ∈ X.support.filter (fun g => k < g.rank ∧ g.type = negOnePow(g.rank - 1) • Pos),
  (X g : ℚ)
```

## Step 3 — change of variables via `Finset.sum_nbij`

The bijection is `φ : g ↦ ⟨g.rank + k, g.type, _⟩`. Apply `Finset.sum_nbij φ` and discharge four obligations:

### (a) Membership (`g ∈ domain → φ(g) ∈ codomain`)

Three parts:

- `φ(g) ∈ X.support`: from `(prime^[k] X) g ≠ 0` and `prime_iterate_coeff`, which gives `X ⟨g.rank + k, ...⟩ ≠ 0`.
- `k < φ(g).rank = g.rank + k`: from `g.rank_pos` (every Gene has positive rank).
- Type condition preserved: `g.type = negOnePow(g.rank - 1) • Pos` implies `g.type = negOnePow(g.rank + k - 1) • Pos` because, writing `g.rank + k - 1 = (g.rank - 1) + k`:

```
negOnePow(g.rank + k - 1) = negOnePow(g.rank - 1) * negOnePow(k)
                           = negOnePow(g.rank - 1) * 1      -- by negOnePow_even hk
                           = negOnePow(g.rank - 1)
```

### (b) Injectivity

`⟨g₁.rank + k, g₁.type, _⟩ = ⟨g₂.rank + k, g₂.type, _⟩ → g₁ = g₂` by `Gene.ext` and `Nat.add_right_cancel`.

### (c) Surjectivity

Given `g' ∈ codomain`, produce `g = ⟨g'.rank - k, g'.type, _⟩` (rank positive since `k < g'.rank`). Verify `g ∈ domain`:

- `(prime^[k] X) g ≠ 0`: by `prime_iterate_coeff`, `(prime^[k] X) g = X ⟨g.rank - k + k, ...⟩ = X g'`, which is nonzero since `g' ∈ X.support`.
- Type condition: reverse of step (a) using the same parity argument.
- `φ(g) = ⟨g'.rank - k + k, g'.type, _⟩ = g'` by `Nat.sub_add_cancel (le_of_lt hk_lt)`.

### (d) Value equality

`(X ⟨g.rank + k, g.type, _⟩ : ℚ) = (X (φ g) : ℚ)`, which is `rfl` by definition of `φ`.

---

## Parity sub-lemma (used in (a) and (c))

```lean
have hpar : ∀ r : ℕ, Int.negOnePow ((↑r + ↑k - 1 : ℤ)) = Int.negOnePow ((↑r - 1 : ℤ)) := fun r => by
  rw [show (↑r + ↑k - 1 : ℤ) = (↑r - 1) + ↑k by ring]
  rw [Int.negOnePow_add, Int.negOnePow_even _ (by exact_mod_cast hk), mul_one]
```
