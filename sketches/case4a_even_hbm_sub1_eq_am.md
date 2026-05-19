# Proof sketch: `hbm_sub1_eq_am` (Case 4a, even `g₁.rank`)

**Location.** `YoungDiagram/Theorem6.lean`, inside `hdi_sub_le_bi_sub`, odd-`j` sub-case.

**Statement.**
```
(Sigma.sigma X.1 (g₁.rank - 1)).2 - (Sigma.sigma X.1 g₁.rank).2 - 1
  = (Sigma.sigma X.1 g₁.rank).1 - (Sigma.sigma X.1 (g₁.rank + 1)).1
```

**Context.**
- `heven : Even g₁.rank`, so `g₁.rank - 1` is odd.
- `hε_neg : ε = .Negative`, so `g₁.type = .Negative`.
- `g₁.rank` is the minimal rank of any gene in `X.1.val.support`.
- `hg₁_one : X.1.val g₁ = 1`.
- `hXpn`: X has no Positive–Negative pair of equal rank.
- Relevant lemmas: `Sigma.sigma_snd_diff`, `Sigma.sigma_fst_diff`,
  `Sigma.prime_iterate_sum_neg_eq`, `Sigma.prime_iterate_sum_pos_eq`.

---

## Key idea

Both sides count exactly the same set of genes in `X.1.val.support`: those of rank
`> g₁.rank` with type `= altType g.rank Positive`. The LHS additionally picks up gene
`g₁` itself (contributing `X.1.val g₁ = 1`), which accounts for the `- 1`.

---

## Step 1 — Rewrite LHS via `sigma_snd_diff` + `prime_iterate_sum_neg_eq`

Apply `Sigma.sigma_snd_diff X.1.val (g₁.rank - 1) X.1.2`:

```
(sigma X (g₁.rank - 1)).2 - (sigma X g₁.rank).2
  = (prime^[g₁.rank - 1] X).sum (fun g m =>
      if g.type = altType g.rank Negative then m else 0)
```

Since `g₁.rank - 1` is odd (`¬Even (g₁.rank - 1)` from `heven` + `omega`), apply
`Sigma.prime_iterate_sum_neg_eq X.1.val (show ¬Even (g₁.rank - 1) from by omega)`:

```
= ∑ g ∈ X.support.filter (fun g =>
    g₁.rank - 1 < g.rank ∧ g.type = altType g.rank Positive),
  X.val g
```

---

## Step 2 — Rewrite RHS via `sigma_fst_diff` + `prime_iterate_sum_pos_eq`

Apply `Sigma.sigma_fst_diff X.1.val g₁.rank X.1.2`:

```
(sigma X g₁.rank).1 - (sigma X (g₁.rank + 1)).1
  = (prime^[g₁.rank] X).sum (fun g m =>
      if g.type = altType g.rank Positive then m else 0)
```

Since `g₁.rank` is even, apply
`Sigma.prime_iterate_sum_pos_eq X.1.val heven`:

```
= ∑ g ∈ X.support.filter (fun g =>
    g₁.rank < g.rank ∧ g.type = altType g.rank Positive),
  X.val g
```

---

## Step 3 — `g₁` lies in the LHS filter but not the RHS filter

- `g₁.rank - 1 < g₁.rank`: trivial.
- `g₁.type = altType g₁.rank Positive`: use `Sigma.altType_even g₁.rank heven GeneType.Positive`,
  which gives `altType g₁.rank Positive = -Positive = Negative = g₁.type`. ✓
- `¬(g₁.rank < g₁.rank)`: trivial, so `g₁ ∉` RHS filter.

---

## Step 4 — LHS filter = `{g₁} ∪` RHS filter (disjoint)

For any `g ≠ g₁` in the LHS filter (so `g₁.rank - 1 < g.rank ∧ g.type = altType g.rank Positive`):

- If `g.rank = g₁.rank`, then `g.type = altType g₁.rank Positive = Negative = g₁.type`,
  so `Gene.ext (rfl) (...)` gives `g = g₁` — contradicting `g ≠ g₁`.
- Therefore `g.rank > g₁.rank`, so `g` is also in the RHS filter.

The two filters are disjoint (`g₁ ∉` RHS filter) and their union is the LHS filter.
Formally, use `Finset.sum_union` after establishing disjointness via `Finset.disjoint_filter`.

---

## Step 5 — Split the sum and conclude

```
LHS sum = X.val g₁ + RHS sum   (by Finset.sum_union or Finset.sum_insert)
        = 1 + RHS sum           (by hg₁_one)
```

Therefore `LHS - 1 = RHS sum = RHS`. The goal `LHS - 1 = RHS` follows by `linarith`.

---

## Lean proof sketch

```lean
have hbm_sub1_eq_am : (Sigma.sigma X.1 (g₁.rank - 1)).2 -
    (Sigma.sigma X.1 g₁.rank).2 - 1 =
    (Sigma.sigma X.1 g₁.rank).1 - (Sigma.sigma X.1 (g₁.rank + 1)).1 := by
  -- Rewrite both sides as sums over X.support
  have hLHS : (Sigma.sigma X.1 (g₁.rank - 1)).2 - (Sigma.sigma X.1 g₁.rank).2 =
      ∑ g ∈ X.1.val.support.filter (fun g =>
        g₁.rank - 1 < g.rank ∧ g.type = altType g.rank GeneType.Positive),
      (X.1.val g : ℚ) := by
    rw [Sigma.sigma_snd_diff X.1.val (g₁.rank - 1) X.1.2,
        Sigma.prime_iterate_sum_neg_eq X.1.val (show ¬Even (g₁.rank - 1) from by omega)]
  have hRHS : (Sigma.sigma X.1 g₁.rank).1 - (Sigma.sigma X.1 (g₁.rank + 1)).1 =
      ∑ g ∈ X.1.val.support.filter (fun g =>
        g₁.rank < g.rank ∧ g.type = altType g.rank GeneType.Positive),
      (X.1.val g : ℚ) := by
    rw [Sigma.sigma_fst_diff X.1.val g₁.rank X.1.2,
        Sigma.prime_iterate_sum_pos_eq X.1.val heven]
  -- g₁ is in the LHS filter (altType g₁.rank Positive = Negative = g₁.type when g₁.rank even)
  have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive :=
    (Sigma.altType_even g₁.rank heven GeneType.Positive).symm ▸ hε_neg.symm
  -- LHS filter = {g₁} ∪ RHS filter  (g ≠ g₁ with same rank forces rank > g₁.rank by Gene.ext)
  have hfilter_split :
      X.1.val.support.filter (fun g => g₁.rank - 1 < g.rank ∧ g.type = altType g.rank GeneType.Positive) =
      {g₁} ∪ X.1.val.support.filter (fun g => g₁.rank < g.rank ∧ g.type = altType g.rank GeneType.Positive) := by
    ext g; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
                      Finsupp.mem_support_iff]
    constructor
    · rintro ⟨hsupp, hrank, htype⟩
      by_cases heq : g = g₁
      · left; exact heq
      · right; refine ⟨hsupp, ?_, htype⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by omega : g₁.rank - 1 < g.rank)) with h | h
        · exact h
        · exact absurd (Gene.ext h.symm (by rwa [← h, ← hg₁_altType] at htype)) heq
    · rintro (rfl | ⟨hsupp, hrank, htype⟩)
      · exact ⟨Finsupp.mem_support_iff.mpr (by omega_nat using hg₁_one), by omega, hg₁_altType⟩
      · exact ⟨hsupp, by omega, htype⟩
  -- Sum splits: LHS sum = X.val g₁ + RHS sum = 1 + RHS sum
  rw [hLHS, hfilter_split, Finset.sum_union (by simp [Finset.disjoint_filter, Finset.mem_singleton])]
  simp only [Finset.sum_singleton]
  rw [hg₁_one]
  linarith [hRHS]
```
