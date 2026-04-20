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

### Step 4 — X3 ≤ X.1.val

```lean
have hX3le : (Gene.ofRankAlt m .Negative + Gene.ofRankAlt k .Positive : Chromosome) ≤ X.1.val := by
  rw [hg₁chr, hg₂chr]
  intro g
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) hne
  · exact hXg₁pos  -- subst h1
  · exact hg₂pos   -- subst h2
  · omega
```

### Step 5 — Define X3, Y3, Z_rest as Pi values

```lean
let hε : GeneType.Negative ≠ .NonPolarized := by decide
let X3_pi : Pi := Pi.X3 hε hle g₁.rank_pos
let Y3_pi : Pi := Pi.Y3 hε hle g₁.rank_pos
-- X3_eq : X3_pi.val = Gene.ofRankAlt m .Negative + Gene.ofRankAlt k .Positive
-- Y3_eq : Y3_pi.val = Gene.ofRankAlt (m-1) .Positive + Gene.ofRankAlt (k+1) .Negative

let restval : Chromosome := X.1.val - X3_pi.val
have hrest_mem : restval ∈ Pi := sub_mem_Pi X3_pi.val X.1.2
let rest_pi : Pi := ⟨restval, hrest_mem⟩

have hX_eq : X3_pi.val + restval = X.1.val := by
  simp only [X3_pi, Pi.X3_eq, restval]
  rw [add_comm, Finsupp.sub_add_cancel_of_le hX3le]
```

### Step 6 — Construct the mutation step

```lean
have hprim : Pi.Primitive X3_pi Y3_pi :=
  Pi.Primitive.type3 .Negative hε hle g₁.rank_pos
have hstep_raw : Pi.Step (X3_pi + rest_pi) (Y3_pi + rest_pi) :=
  Pi.Step.mk X3_pi Y3_pi rest_pi hprim
have hX_sub : X3_pi + rest_pi = X.1 := Subtype.ext hX_eq
-- Z := Y3_pi + rest_pi
exact ⟨Y3_pi + rest_pi, hX_sub ▸ hstep_raw, ?_⟩
```

---

## Step 7 — Prove Z ≤ Y.1

Split on parity of k:

```lean
rcases Nat.even_or_odd k with ⟨t, hkt⟩ | ⟨t, hkt⟩
· -- k even:
  -- Key chain of sigma differences on Y (using cond_15_6):
  --   d_{k-1} - d_k  ≤  c_{k-2} - c_{k-1}   (cond_15_6, index k-2 even)
  --   c_{k-2} - c_{k-1}  ≤  d_{k-3} - d_{k-2}   (cond_15_6, index k-3 odd)
  --   d_{k-3} - d_{k-2}  ≤  c_{k-4} - c_{k-3}   (cond_15_6, index k-4 even)
  --   ...
  -- Since k is even, after k/2 steps the chain terminates at:
  --   ... ≤  d_0 - d_1
  -- Moreover, from the minimality of k, the sigma differences on X form a constant chain:
  --   b_0 - b_1 = a_1 - a_2 = b_2 - b_3 = ... = b_{k-1} - b_k
  -- (ends at b since k is even).
  --
  -- Now d_0 - d_1 < b_0 - b_1 because:
  --   b_0 = d_0  (from a_0 = c_0 and equal ranks: a_0 + b_0 = c_0 + d_0)
  --   b_1 < d_1  (analog of ha for the .2 component at level 1)
  -- Hence d_0 - d_1 < b_0 - b_1, bounding the chain from above.
  -- Putting the two chains together:
  --   d_{k-1} - d_k  ≤  d_0 - d_1  <  b_0 - b_1  =  b_{k-1} - b_k
  -- and similarly at each intermediate level.  This yields the strict inequalities:
  --   b_k < d_k,   a_{k-1} < c_{k-1},   b_{k-2} < d_{k-2},  ...,  a_2 < c_2
  -- (alternating .2 and .1 components, working down from level k to level 2).
  -- These strict inequalities combined with sigma(Y3, j) - sigma(X3, j) = (1,0) or (0,1)
  -- gives sigma(Y3, j) + sigma(Z_rest, j) ≤ sigma(Y.1, j) for all j.
  -- Hence Z ≤ Y.
  sorry
· -- k odd:
  -- Key chain of sigma differences on Y (using cond_15_6 and cond_15_7):
  --   c_{k-1} - c_k  ≤  d_{k-2} - d_{k-1}   (cond_15_7, index k-2 even)
  --   d_{k-2} - d_{k-1}  ≤  c_{k-3} - c_{k-2}   (cond_15_6, index k-3 even)
  --   c_{k-3} - c_{k-2}  ≤  d_{k-4} - d_{k-3}   (cond_15_7, index k-4 even)
  --   ...
  -- Since k is odd, after (k-1)/2 steps the chain terminates at:
  --   ... ≤  c_0 - c_1
  -- Moreover, from the minimality of k (g₂ has the smallest rank among
  -- ofRankAlt-Positive genes in X), X has no such gene of rank < k.
  -- This forces the sigma differences on X to form a constant chain:
  --   a_0 - a_1 = b_1 - b_2 = a_2 - a_3 = ... = a_{k-1} - a_k
  -- (each step loses exactly the contribution of the alternating pair).
  --
  -- Now c_0 - c_1 < a_0 - a_1 because:
  --   a_0 = c_0  (X and Y have the same rank, so sigma at level 0 has equal sum,
  --               and from ha₀_eq_c₀ proved earlier)
  --   a_1 < c_1  (this is exactly `ha`)
  -- Hence c_0 - c_1 < a_0 - a_1, bounding the chain from above.
  -- Putting the two chains together:
  --   c_{k-1} - c_k  ≤  c_0 - c_1  <  a_0 - a_1  =  a_{k-1} - a_k
  -- and similarly at each intermediate level.  This yields the strict inequalities:
  --   a_k < c_k,   b_{k-1} < d_{k-1},   a_{k-2} < c_{k-2},  ...,  b_2 < d_2
  -- (alternating .1 and .2 components, working down from level k to level 2).
  -- These strict inequalities are exactly sigma(X.1, j) < sigma(Y.1, j) componentwise
  -- for j in [2, k], which combined with sigma(Y3, j) - sigma(X3, j) = (1,0) or (0,1)
  -- gives sigma(Y3, j) + sigma(Z_rest, j) ≤ sigma(Y.1, j) for all j.
  -- Hence Z ≤ Y.
  sorry
```
