# Proof Sketch: Case 1 when $a_k < c_k$ (Djoković 1982, §15, p. 30)

## Setup

We are in sub-case **15.10**: $X, Y \in \Pi$, $X < Y$, $X$ contains **no** same-rank gene pair
$g^+(t) + g^-(t)$, and there exists $k \geq 1$ with $\operatorname{prime}^k(Y) \neq 0$ and

$$a_k < c_k \qquad (\text{i.e. } \sigma(X,k)_1 < \sigma(Y,k)_1).$$

Write $\sigma(X,j) = (a_j, b_j)$, $\sigma(Y,j) = (c_j, d_j)$.  From $X \leq Y$: $(a_j, b_j) \leq
(c_j, d_j)$ componentwise.  From sub-case 2b: $\sigma(X,j) \neq \sigma(Y,j)$ for all $j \geq 1$
with $\operatorname{prime}^j(Y) \neq 0$.

**Goal**: find $Z \in \Pi$ with $X \xrightarrow{\text{step}} Z$ and $Z \leq Y$.

**Skeleton**:

1. Extract $X_1 = g_1 + g_2$ from $X$, set $\mathrm{rest} = X - X_1$.
2. Apply the primitive mutation $X_1 \to Y_1$, yielding $Z = Y_1 + \mathrm{rest}$.
3. Verify $Z \leq Y$ by checking $\sigma(Z,j) \leq \sigma(Y,j)$ in three ranges:
   $j < m$, $m \leq j \leq k$, $j > k$.

---

## Case 1 — Type 1 mutation, $\varepsilon = -$ (small negative + large positive gene)

Here $g_\varepsilon(k) := g^{\varepsilon \cdot (-1)^{k-1}}(k)$ (Djoković §15, p. 30), so the sign of
$g_\varepsilon(k)$ alternates with $k$.

**Hypothesis**: $X$ contains a gene $g_1 := g_-(m)$ with $m$ minimal among all genes
in $X$, and a gene $g_2 := g_+(k)$ (a positive gene of rank $k$), with $m < k$.

**Existence of $g_2$**: We must show $X.\mathrm{val}(g_+(k)) > 0$.  Since $\varepsilon = -$, the
gene $g_{\varepsilon_1}(m)$ is negative (i.e. $\varepsilon_1 \cdot (-1)^{m-1} = -1$).  Combined
with the hypothesis that $X$ has no same-rank gene pair, $\text{prime}^k(X)$ contains only
positive genes at each rank, so $\sigma(X,k)_1 = a_k$ counts the positive genes in
$\text{prime}^k(X)$.  Since $\varepsilon = -$ forces $a_k \geq 1$ (the parity condition at level
$k$), $X$ contains a positive gene of rank exactly $k$, i.e. $g_2 = g_+(k) \in X$.

We take $k$ to be **minimal** among all indices with $\operatorname{prime}^k(Y) \neq 0$ and
$a_k < c_k$ (valid since the set is non-empty by hypothesis).  In particular, for all $j < k$
with $\operatorname{prime}^j(Y) \neq 0$ we have $a_j = c_j$.

**Mutation**:
$$g_-(m) + g_+(k) \;\longrightarrow\; g_-(m{-}1) + g_+(k{+}1).$$

So $Z = X - g_-(m) - g_+(k) + g_-(m{-}1) + g_+(k{+}1)$.

The proof that $Z \leq Y$ splits on the parity of $k$.

---

## Case 1a — $k$ odd

Since $k$ is odd, $(-1)^{k-1} = 1$, so:
$$g_+(k) = g^+(k), \qquad g_+(k{+}1) = g^-(k{+}1).$$

The mutation in terms of signed genes is:
$$g_-(m) + g^+(k) \;\longrightarrow\; g_-(m{-}1) + g^-(k{+}1).$$

### Why $Z \leq Y$

Since $k$ is odd, $g_+(k) = g^+(k)$, so the key sigma identity for this mutation is:
$$\sigma(Z,j) = \sigma(X,j) + (0,1) \cdot \mathbf{1}_{[m,k]}(j).$$

This follows from `mutation_type1_sigma` and the identity $\sigma(g^-(t{+}1)) = \sigma(g^+(t)) + (0,1)$.

- For $j \notin [m,k]$: $\sigma(Z,j) = \sigma(X,j) \leq \sigma(Y,j)$ by dominance.
- For $j \in [m,k]$: $\sigma(Z,j) = \sigma(X,j) + (0,1) \leq \sigma(Y,j)$ iff $b_j < d_j$,
  which holds by the **Propagation Lemma** below.

---

## Case 1b — $k$ even

Since $k$ is even, $(-1)^{k-1} = -1$, so:
$$g_+(k) = g^-(k), \qquad g_+(k{+}1) = g^+(k{+}1).$$

The mutation in terms of signed genes is:
$$g_-(m) + g^-(k) \;\longrightarrow\; g_-(m{-}1) + g^+(k{+}1).$$

*(The middle-range gain becomes $(1,0)$ instead of $(0,1)$, requiring $a_j < c_j$.
This follows directly from $\Delta a$ non-increasing and $\Delta a_k \geq 1$.  Proof to be filled in.)*

---

## Propagation Lemma: $b_j < d_j$ for $j \in [m,k]$ (used in Case 1a)

```lean
private lemma propagation_lemma_b_lt
    {X Y : Pi}
    (hXY : X < Y)
    (hsigeq : ∀ j : ℕ, 0 < j → prime^[j] Y.val ≠ 0 →
      Sigma.sigma X.val j ≠ Sigma.sigma Y.val j)
    {k : ℕ} (hkpos : 0 < k)
    (hYkne : prime^[k] Y.val ≠ 0)
    (hak : (Sigma.sigma X.val k).1 < (Sigma.sigma Y.val k).1)
    (hk_min : ∀ j : ℕ, 0 < j → prime^[j] Y.val ≠ 0 → j < k →
      (Sigma.sigma X.val j).1 = (Sigma.sigma Y.val j).1)
    {j : ℕ} (hjpos : 0 < j) (hjk : j ≤ k)
    (hYjne : prime^[j] Y.val ≠ 0) :
    (Sigma.sigma X.val j).2 < (Sigma.sigma Y.val j).2 := by
  sorry
```

**Proof sketch (see below).**



Define $\Delta a_j = c_j - a_j \geq 0$ and $\Delta b_j = d_j - b_j \geq 0$.

**Step 1** ($\operatorname{prime}^j(Y) \neq 0$ for $j \leq k$).  Since $X.\mathrm{val}(g_2) > 0$
(i.e. $X$ contains $g_+(k) = g^+(k)$), we get $(\operatorname{prime}^j X)(g^+(k{-}j)) > 0$, hence
$\sigma(X,j)_1 > 0$, and $\sigma(Y,j) \geq \sigma(X,j)$ forces $\sigma(Y,j)_1 > 0$,
so $\operatorname{prime}^j(Y) \neq 0$.

**Step 2** (strict inequality at each level).  From sub-case 2b, $(\Delta a_j, \Delta b_j) \neq
(0,0)$ for every $j \in [m,k]$, so $\Delta a_j + \Delta b_j \geq 1$.

**Step 3** (non-increasing $\Delta a$ and $\Delta b$ by reverse induction).  Conditions 15.6 and
15.7, applied to both $X$ and $Y$, yield the coupled inequalities (for appropriate parity of $j$):

$$\Delta a_j - \Delta a_{j+1} \;\geq\; \Delta b_{j+1} - \Delta b_{j+2},$$
$$\Delta b_j - \Delta b_{j+1} \;\geq\; \Delta a_{j+1} - \Delta a_{j+2}.$$

**Base** (eventually zero): by condition 15.2/15.3 both $\Delta a_K = \Delta b_K = 0$ for $K$
sufficiently large.

**Inductive step** (going backwards from $K$): if $\Delta a_{j+1} \geq \Delta a_{j+2}$ and
$\Delta b_{j+1} \geq \Delta b_{j+2}$, then both differences are $\geq 0$ by the two inequalities,
so $\Delta a_j \geq \Delta a_{j+1}$ and $\Delta b_j \geq \Delta b_{j+1}$.

Hence both $\Delta a$ and $\Delta b$ are **non-increasing**.

**Conclusion**: since $\Delta a_k \geq 1$ (from $a_k < c_k$), and both sequences are non-increasing,
the coupled recurrence gives $\Delta b_j \geq \Delta b_k \geq \Delta a_k \geq 1$ for $j \leq k$
(via the interlacing of the recurrence), so $b_j < d_j$ for all $j \in [m,k]$. $\square$
