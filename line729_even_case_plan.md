# Plan: Proving `(Sigma.sigma X.1.val i).2 < (Sigma.sigma Y.1.val i).2` (line 729)

This is the outer `suffices` hypothesis for the **even-index** branch of the mutation inequality
proof (Case 1, k-odd subcase, Step 6). We have `heven : Even i` and `hin : g₁.rank ≤ i ∧ i ≤
g₂.rank`, and must show the second sigma-component of X at column `i` is strictly below that of Y.

Let `P := (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1`.

---

## Step 1 — predecessor `pred := i - 1` exists and is odd

Since `hin.1 : g₁.rank ≤ i` and `g₁.rank_pos`, we have `i ≥ 1`, so `pred = i - 1 : ℕ` is
well-defined. Since `i` is even, `pred` is odd.

Since `g₂.rank = 2 * j + 1` is odd (`hk_odd`) and `i` is even, `i ≠ g₂.rank`, so `i < g₂.rank`
(from `hin.2`). Hence `pred < g₂.rank`.

```lean
have hi_pos : 1 ≤ i := Nat.le_trans g₁.rank_pos hin.1
have hi_lt  : i < g₂.rank := by
  rcases Nat.lt_or_eq_of_le hin.2 with h | h
  · exact h
  · exact absurd heven (h ▸ hk_odd ▸ Nat.odd_two_mul_add_one j |>.not_even)
have hpred_odd : ¬Even (i - 1) := by omega
```

---

## Step 2 — X's second-component difference at `pred` equals P

Apply `hXchain` at the odd index `i - 1` (selecting the `else` branch):

```lean
have hX_eq : (Sigma.sigma X.1 (i - 1)).2 - (Sigma.sigma X.1 i).2 =
    (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
  have h := hXchain (i - 1) (by omega)
  simp only [if_neg hpred_odd] at h
  exact h
```

---

## Step 3 — Y's second-component difference at `pred` is bounded by `c₀ − c₁`

Apply `Sigma.cond_15_6_compare_k_to_0` to Y at the odd index `i - 1` (selecting the `else` branch):

```lean
have hY_le : (Sigma.sigma Y.1.val (i - 1)).2 - (Sigma.sigma Y.1.val i).2 ≤
    (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
  have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (i - 1) Y.1.2
  simp only [if_neg hpred_odd] at h
  exact h
```

---

## Step 4 — Y dominates X at column `pred` (second component)

This follows directly from the global dominance `hXY.le` applied at column `i - 1`:

```lean
have hXY_pred : (Sigma.sigma X.1.val (i - 1)).2 ≤ (Sigma.sigma Y.1.val (i - 1)).2 :=
  (le_iff_dominates.mp hXY.le (i - 1)).2
```

---

## Step 5 — conclude by `linarith`

The four hypotheses close the goal `(Sigma.sigma X.1.val i).2 < (Sigma.sigma Y.1.val i).2`
via the chain:

```
σY(i−1).2 − σY(i).2  ≤  c₀ − c₁          [hY_le]
                      <   P                 [hstrict]
                      =   σX(i−1).2 − σX(i).2   [hX_eq]
```

Rearranging: `σX(i).2 − σY(i).2 < σX(i−1).2 − σY(i−1).2 ≤ 0` (using `hXY_pred`),
so `σX(i).2 < σY(i).2`.

```lean
linarith [hX_eq, hY_le, hstrict, hXY_pred]
```
