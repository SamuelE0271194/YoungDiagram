# Plan: Resolve sorry at line 364 (Pi Antisymmetry)

## Goal

```lean
have hXkYk_eq : Xk.val = Yk.val := by
  sorry -- Pi antisymmetry: Xk.val ≤ Yk.val → Yk.val ≤ Xk.val → Xk.val = Yk.val
```

### Context hypotheses

| Name | Type |
|------|------|
| `hle_k` | `Xk.val ≤ Yk.val` (i.e., `∀ j, sig(prime^[j] Xk.val) ≤ sig(prime^[j] Yk.val)`) |
| `hcontra` | `Xk.val.Dominates Yk.val` (i.e., `∀ j, sig(prime^[j] Yk.val) ≤ sig(prime^[j] Xk.val)`) |
| `prime_iterate_coeff` | `∀ k' D h, (prime^[k'] D) h = D ⟨h.rank + k', h.type, _⟩` (proved locally) |
| `Xk.2`, `Yk.2` | Both are Pi chromosomes (polarized: only Positive or Negative genes) |

### Key fact about `Gene.signature`

For a gene `g` with rank `r` and type `t`:

| Type | Rank parity | `g.signature.1 - g.signature.2` |
|------|-------------|----------------------------------|
| Positive | odd | `+1` |
| Positive | even | `0` |
| Negative | odd | `-1` |
| Negative | even | `0` |
| NonPolarized | any | `0` |

---

## Overall strategy

To prove `Xk.val = Yk.val` as Finsupp (equal on every gene), use `Finsupp.ext`. For each gene `g = ⟨r, t, _⟩`:

- **Sum:** `Xk.val ⟨r, Pos⟩ + Xk.val ⟨r, Neg⟩ = Yk.val ⟨r, Pos⟩ + Yk.val ⟨r, Neg⟩`
- **Diff:** `Xk.val ⟨r, Pos⟩ - Xk.val ⟨r, Neg⟩ = Yk.val ⟨r, Pos⟩ - Yk.val ⟨r, Neg⟩` (in ℤ)

Adding: `2 * Xk.val ⟨r, Pos⟩ = 2 * Yk.val ⟨r, Pos⟩`, so `Xk.val ⟨r, Pos⟩ = Yk.val ⟨r, Pos⟩` (and similarly for Neg).
For NonPolarized genes: both are 0 (Pi = IsPolarized, so `IsPolarized_def'` gives 0).

---

## Step A — Sig-tower equality

From `hle_k` and `hcontra`, the two inequalities at each level `j` are opposite, so:

```lean
have hsig_eq : ∀ j, signature (Chromosome.prime^[j] Xk.val) =
                     signature (Chromosome.prime^[j] Yk.val) := fun j =>
  le_antisymm (le_iff_dominates.mp hle_k j) (hcontra j)
```

`le_antisymm` applies to `ℚ × ℚ` with its product order (which is a `PartialOrder`).

---

## Step B — Rank equality at all levels

```lean
have hrank_eq : ∀ j, (Chromosome.prime^[j] Xk.val).rank =
                      (Chromosome.prime^[j] Yk.val).rank := fun j => by
  have h := congr_arg (fun p : ℚ × ℚ => p.1 + p.2) (hsig_eq j)
  simp only [signature_sum_eq_rank] at h
  exact_mod_cast h
```

Uses `signature_sum_eq_rank : sig(C).1 + sig(C).2 = C.rank` (as ℚ).

---

## Step C — Total-count formula for prime iterates

**Claim:**
```
(prime^[j] C).sum (fun _ m => m) = C.sum (fun g m => if j < g.rank then m else 0)
```

**Proof sketch:**
Using `prime_iterate_coeff`, `(prime^[j] C) g = C ⟨g.rank + j, g.type, _⟩`. The support of `prime^[j] C` bijects with `{g ∈ supp(C) | g.rank > j}` via `h ↦ ⟨h.rank + j, h.type, _⟩`. So the total count (sum of multiplicities) of `prime^[j] C` equals `∑_{g: g.rank > j} C g`.

In Lean: use `Finsupp.sum` with `Finset.sum_nbij` (or `Finsupp.sum_bij`) for the rank-shift bijection.

**Consequence:** From `hrank_eq`:
```
(prime^[j] Xk.val).rank - (prime^[j+1] Xk.val).rank
  = (prime^[j] Yk.val).rank - (prime^[j+1] Yk.val).rank
  = total count of prime^[j] Yk.val
```
So `∑_{g.rank > j} Xk.val g = ∑_{g.rank > j} Yk.val g` for all `j`.

---

## Step D — Sum equality at each rank

From Step C by telescoping (take `j = r-1` minus `j = r`):
```
∑_{g.rank = r} Xk.val g = ∑_{g.rank = r} Yk.val g
```

For a Pi chromosome, at each rank `r` only genes `⟨r, Positive, _⟩` and `⟨r, Negative, _⟩` can appear (no NonPolarized). So:

```lean
have hsum_eq : ∀ r : ℕ, 0 < r →
    Xk.val ⟨r, .Positive, _⟩ + Xk.val ⟨r, .Negative, _⟩ =
    Yk.val ⟨r, .Positive, _⟩ + Yk.val ⟨r, .Negative, _⟩ := ...
```

In Lean: use `Nat.add_sub_cancel` style telescoping on the rank-sum equality from Step C.

---

## Step E — The D formula

Define `D C j := (signature (Chromosome.prime^[j] C)).1 - (signature (Chromosome.prime^[j] C)).2 ∈ ℚ`.

**Claim:**
```
D C j = ∑_{n ≥ 0} (↑(C ⟨2n+1+j, Positive, _⟩) - ↑(C ⟨2n+1+j, Negative, _⟩)) : ℚ
```

**Proof:**
Expand `sig(prime^[j] C)`:
```
D C j
  = (prime^[j] C).sum (fun g m => (m : ℚ) * (g.signature.1 - g.signature.2))
  -- only odd-rank genes contribute (even-rank and NonPolarized contribute 0):
  = ∑_{g: Pos, g.rank odd} (prime^[j] C) g  -  ∑_{g: Neg, g.rank odd} (prime^[j] C) g
  -- apply prime_iterate_coeff: (prime^[j] C) g = C ⟨g.rank + j, g.type, _⟩
  = ∑_{n≥0} C ⟨2n+1+j, Pos, _⟩  -  ∑_{n≥0} C ⟨2n+1+j, Neg, _⟩
```

The parity of `g.rank + j` is irrelevant; what matters is the parity of `g.rank` in `prime^[j] C` (i.e., the gene in the shifted chromosome, not the original).

In Lean: unfold `signature`, unfold `Gene.signature`, use `prime_iterate_coeff`, then `Finsupp.sum` manipulation with the parity filter.

---

## Step F — Diff equality at each rank

From Step A: `(hsig_eq j).1` and `(hsig_eq j).2` give component equalities, so `D Xk.val j = D Yk.val j` for all `j`.

From the D formula (Step E), by telescoping `D(j) - D(j+2)`:
```
D C j - D C (j+2)
  = ∑_{n≥0} [C ⟨2n+1+j, Pos⟩ - C ⟨2n+1+j, Neg⟩]
  - ∑_{n≥0} [C ⟨2n+1+j+2, Pos⟩ - C ⟨2n+1+j+2, Neg⟩]
  = C ⟨1+j, Pos⟩ - C ⟨1+j, Neg⟩   -- only the n=0 term of the first sum doesn't cancel
```

Setting `j = r - 1`:
```lean
have hdiff_eq : ∀ r : ℕ, 0 < r →
    (Xk.val ⟨r, .Positive, _⟩ : ℤ) - Xk.val ⟨r, .Negative, _⟩ =
    (Yk.val ⟨r, .Positive, _⟩ : ℤ) - Yk.val ⟨r, .Negative, _⟩ := fun r hr => by
  -- D Xk.val (r-1) - D Xk.val (r+1) = Xk.val ⟨r, Pos⟩ - Xk.val ⟨r, Neg⟩
  -- D Yk.val (r-1) - D Yk.val (r+1) = Yk.val ⟨r, Pos⟩ - Yk.val ⟨r, Neg⟩
  -- And D Xk.val j = D Yk.val j for all j. QED.
  sorry
```

---

## Step G — Conclude pointwise equality, then `Finsupp.ext`

```lean
apply Finsupp.ext
intro g
-- Case split on g.type:
cases ht : g.type with
| Positive =>
  -- From hsum_eq and hdiff_eq (as ℤ): 2 * Xk.val g = 2 * Yk.val g, hence equal.
  have hS := hsum_eq g.rank g.rank_pos
  have hD := hdiff_eq g.rank g.rank_pos
  -- Rewrite g = ⟨g.rank, Positive, _⟩ using ht, then omega.
  omega
| Negative =>
  -- Similarly.
  omega
| NonPolarized =>
  -- Pi chromosomes: IsPolarized_def' gives Xk.val g = 0 and Yk.val g = 0.
  have hXnp : Xk.val g = 0 := by
    by_contra h
    exact absurd ht (IsPolarized_def'.mp (mem_Pi_iff.mp Xk.2) g
      (Finsupp.mem_support_iff.mpr h))
  have hYnp : Yk.val g = 0 := by
    by_contra h
    exact absurd ht (IsPolarized_def'.mp (mem_Pi_iff.mp Yk.2) g
      (Finsupp.mem_support_iff.mpr h))
  simp [hXnp, hYnp]
```

---

## Summary of sub-sorrys and required API

| Step | Main difficulty | Lean API needed |
|------|-----------------|-----------------|
| A | None | `le_antisymm` for `ℚ × ℚ` |
| B | None | `signature_sum_eq_rank`, `exact_mod_cast` |
| C | **Finsupp sum reindexing** via rank-shift bijection | `Finset.sum_nbij` or `Finsupp.sum_bij`; `prime_iterate_coeff` |
| D | Telescoping from Step C | `Nat.sub_add_cancel`, `omega` |
| E | **Expanding signature** formula with `prime_iterate_coeff`, parity case split | `Gene.signature`, `Finsupp.sum` splitting by `g.type` and `g.rank % 2` |
| F | Telescoping the D formula | `linarith` / `ring` combining D equality at two levels |
| G | `Finsupp.ext`, Pi polarization, `omega` | `IsPolarized_def'`, `mem_Pi_iff`, `Finsupp.ext` |

**The two hardest steps are C and E**, both requiring `Finsupp.sum` reindexing via the bijection `g ↦ ⟨g.rank + j, g.type, _⟩`. The cleanest Lean tool for this is `Finset.sum_nbij`:

```lean
Finset.sum_nbij (fun g => ⟨g.rank + j, g.type, by linarith [g.rank_pos]⟩)
  (fun g hg => ...)   -- membership
  (fun g₁ g₂ _ _ h => ...)  -- injectivity (from rank+j equality)
  (fun h hh => ...)   -- surjectivity (h has rank > j, take g = ⟨h.rank - j, ...⟩)
  (fun g _ => ...)    -- value equality via prime_iterate_coeff
```

---

## Recommended implementation order

1. Implement **Step A** (trivial, 1 line).
2. Implement **Step B** (trivial, copy from `hXk_Yk_rank` proof).
3. Implement **Step C** as a local `have` using `Finset.sum_nbij`.
4. Implement **Step D** using Step C and `Nat.sub_add_cancel`.
5. Implement **Step E** as a local `have` using the D formula (may need case splits on `g.type` and `Nat.even_or_odd g.rank`).
6. Implement **Step F** using Step E and `linarith`.
7. Implement **Step G** with `Finsupp.ext` and `omega`.
