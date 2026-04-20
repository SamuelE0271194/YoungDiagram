# Case 1 Proof Framework — §15.10 of Djoković (line 497)

## Hypotheses available at line 497

| Name | Type |
|------|------|
| `g₁ : Gene` | Gene of minimal rank `m := g₁.rank` in X |
| `hε₁` | `g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Negative` |
| `hXg₁pos` | `0 < X.1.val g₁` |
| `hg₁min` | `∀ x' ∈ X.1.val.support, g₁.rank ≤ x'.rank` |
| `g₂ : Gene` | A gene with ofRankAlt-Positive type in X |
| `hg₂type` | `g₂.type = Int.negOnePow (g₂.rank - 1) • GeneType.Positive` |
| `hg₂pos` | `0 < X.1.val g₂` |
| `ha` | `(Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1` |
| `hXY` | `X.1 < Y.1` |
| `hcommon` | no gene appears in both X and Y |
| `hsigeq` | ∀ k ≥ 1 with `prime^[k] Y.1.val ≠ 0`, `Sigma.sigma X.1 k ≠ Sigma.sigma Y.1 k` |
| `hXpn` | X has no Positive-Negative pair at the same rank |

Write `m := g₁.rank` and `k := g₂.rank`.

---

## Shared setup (before odd/even split)

### Step 1 — m ≤ k

```lean
have hle : g₁.rank ≤ g₂.rank :=
  hg₁min g₂ (Finsupp.mem_support_iff.mpr hg₂pos.ne')
```

### Step 2 — Gene → Chromosome conversion

```lean
have hg₁chr : Gene.ofRankAlt m .Negative = Finsupp.single g₁ 1 := by
  rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]
  congr 1; exact Gene.ext rfl hε₁.symm

have hg₂chr : Gene.ofRankAlt k .Positive = Finsupp.single g₂ 1 := by
  rw [Gene.ofRankAlt_eq_gene g₂.rank_pos]
  congr 1; exact Gene.ext rfl hg₂type.symm
```

### Step 3 — g₁ ≠ g₂

When `m = k`, their types differ: `negOnePow(m-1) • .Negative ≠ negOnePow(m-1) • .Positive`
(one is Positive iff the other is Negative by the negOnePow sign flip).
When `m < k`, ranks differ.

```lean
have hne : g₁ ≠ g₂ := by
  intro heq
  have htype := congr_arg Gene.type heq
  rw [hε₁, hg₂type] at htype
  -- negOnePow(m-1) • .Negative = negOnePow(m-1) • .Positive is impossible
  cases GeneType.negOnePow_smul (g₁.rank - 1 : ℤ) GeneType.Negative <;>
  cases GeneType.negOnePow_smul (g₁.rank - 1 : ℤ) GeneType.Positive <;>
  simp_all [GeneType.neg_positive, GeneType.neg_negative]
```

