# Case 3, Odd Rank: Window Inequality Proof

**Context:** Same as the even case — Case 3 (`2 ≤ X(g₁)`), window `i ∈ {g₁.rank - 1, g₁.rank, g₁.rank + 1}` — but now `g₁.rank` is **odd**. Since `g₁.rank - 1` is even, `negOnePow(g₁.rank - 1) = 1`, so `g₁.type = Positive` (by `hε₁` and polarization). The window differences are therefore:

| index | diff `sigma Z - sigma X` |
|---|---|
| `g₁.rank - 1` | `(0, 1)` |
| `g₁.rank`     | `(1, 1)` |
| `g₁.rank + 1` | `(1, 0)` |

Compare with the even case: the `(1, 0)` and `(0, 1)` entries at rank±1 are **swapped**.

---

## Step 1: Auxiliary inequalities for the .1 component

We need `a_i < c_i` at `i = g₁.rank` and `i = g₁.rank + 1` (unlike the even case which needed `i = g₁.rank` and `i = g₁.rank - 1`). The chain is shifted by one compared to the even case:

`c₁ - c_{i+1} ≤ d₀ - d_i ≤ b₀ - b_i = a₁ - a_{i+1}`

combined with `hstrict` and `a₀ = c₀`.

```lean
-- c₁ - c_{i+1} ≤ d₀ - d_i  (some Sigma lemma, analogous to a1_ai_le_b0_bi_1)
have hc1_ci_rank  : ... := sorry  -- at i = g₁.rank - 1, giving bound for a_rank
have hc1_ci_rank1 : ... := sorry  -- at i = g₁.rank,     giving bound for a_{rank+1}

-- d₀ - d_i ≤ b₀ - b_i  (from sigma_zero equality + dominance at i)
have hd0_di_rank  : ... := sorry  -- at i = g₁.rank - 1
have hd0_di_rank1 : ... := sorry  -- at i = g₁.rank

-- b₀ - b_i = a₁ - a_{i+1}  (from x_actual_negative_prefix_equalities)
have hb0_bi       : ... := sorry
have hb0_bi_rank  := sorry        -- at i = g₁.rank - 1
have hb0_bi_rank1 := sorry        -- at i = g₁.rank

-- Conclude a_i < c_i
have ha_lt_c_rank  : (sigma X g₁.rank).1     < (sigma Y g₁.rank).1     := by sorry
have ha_lt_c_rank1 : (sigma X (g₁.rank+1)).1 < (sigma Y (g₁.rank+1)).1 := by sorry
```

---

## Step 2: Auxiliary inequalities for the .2 component

We need `b_i < d_i` at `i = g₁.rank - 1` and `i = g₁.rank` (unlike the even case which needed `i = g₁.rank` and `i = g₁.rank + 1`). The chain is a -1 shift of the even case (replacing `i` with `i-1` throughout):

`d₂ - d_i ≤ c₁ - c_{i-1} ≤ d₀ - d_{i-2} ≤ b₀ - b_{i-2} = b₂ - b_i`

combined with `hd2_gt_b2 : b₂ < d₂`. Instantiated at `i = g₁.rank - 1` (giving `b_{rank-1}`) and `i = g₁.rank` (giving `b_rank`).

```lean
-- d₂ - d_i ≤ c₁ - c_{i-1}  (from Sigma.b2_bi_2_le_a1_ai, shifted)
have hd2_c1_rank  : ... := sorry  -- at i = g₁.rank
have hd2_c1_rank1 : ... := sorry  -- at i = g₁.rank - 1

-- chain to d₀ - d_{i-2}
have hd2_di1_rank  : ... := sorry
have hd2_di1_rank1 : ... := sorry

-- a₁ - a_j = b₂ - b_{j+1}  (from x_actual_negative_prefix_equalities2)
have hb0_bi'      : ... := sorry
have ha1_ai_rank  : ... := sorry
have ha1_ai_rank1 : ... := sorry  -- at i = g₁.rank - 1

-- b₀ - b_{i-2} = b₂ - b_i
have hb0_b2_rank  : ... := sorry
have hb0_b2_rank1 : ... := sorry

-- Conclude b_i < d_i
have hb_lt_d_rank  : (sigma X g₁.rank).2     < (sigma Y g₁.rank).2     := by sorry
have hb_lt_d_rank1 : (sigma X (g₁.rank-1)).2 < (sigma Y (g₁.rank-1)).2 := by sorry
```

---

## Step 3: Window difference formula

Same structure as the even case, but now we need `g₁.type = Positive` (or equivalently `g₁.type ≠ Negative`). Since `¬ heven` and `g₁.rank - 1` is even, `negOnePow(g₁.rank - 1) • Negative = Negative`, so `hε₁` directly gives `g₁.type ≠ Negative`.

```lean
have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
    if i = g₁.rank then (1, 1)
    else if i = g₁.rank - 1 then (0, 1)
    else (1, 0) := by
  rw [hZ_split, hX_split, add_sub_add_right_eq_sub]
  have hibounds : g₁.rank - 1 ≤ i ∧ i ≤ g₁.rank + 1 := by
    rcases hi_range with rfl | rfl | rfl <;> omega
  rw [hwindow i hibounds.1 hibounds.2]
  -- g₁.type = .Positive: rank is odd so g₁.rank - 1 is even,
  -- negOnePow(g₁.rank - 1) • Negative = Negative, and hε₁ gives type ≠ Negative
  have htype_pos : g₁.type = .Positive := by
    sorry
  simp [htype_pos]
```

---

## Step 4: Three sub-cases

Same ext/rw/constructor skeleton as the even case, but with different diffs and strict inequality hypotheses.

### i = g₁.rank - 1  (diff = (0, 1))

The `.1` component gets `+0`, handled by `hXY_i.1`. The `.2` component gets `+1`, handled by `hb_lt_d_rank1` and `sigma_isNat` integrality.

```lean
-- diff simplifies to (0, 1)
simpa [show g₁.rank - 1 ≠ g₁.rank from by omega] using hZX_diff
-- .1: linarith [hXY_i.1]
-- .2: exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank1)
```

### i = g₁.rank  (diff = (1, 1))

Both components get `+1`; use `ha_lt_c_rank` for `.1` and `hb_lt_d_rank` for `.2`.

```lean
-- diff simplifies to (1, 1)
simpa using hZX_diff
-- .1: exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank)
-- .2: exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank)
```

### i = g₁.rank + 1  (diff = (1, 0))

The `.1` component gets `+1`, handled by `ha_lt_c_rank1` and `sigma_isNat` integrality. The `.2` component gets `+0`, handled by `hXY_i.2`.

```lean
-- diff simplifies to (1, 0)
simpa [show g₁.rank + 1 ≠ g₁.rank from by omega,
       show g₁.rank + 1 ≠ g₁.rank - 1 from by omega] using hZX_diff
-- .1: exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank1)
-- .2: linarith [hXY_i.2]
```
