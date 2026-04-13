# Proof Sketch: Cases 1–4 when $a_k < c_k$ (Djoković 1982, §15, p. 30)

## Setup

We are in sub-case **15.10**: $X, Y \in \Pi$, $X < Y$, $X$ contains **no** same-rank gene pair
$g^+(t) + g^-(t)$, and there exists $k \geq 1$ with $\operatorname{prime}^k(Y) \neq 0$ and

$$a_k < c_k \qquad (\text{i.e. } \sigma(X,k)_1 < \sigma(Y,k)_1).$$

Write $\sigma(X,j) = (a_j, b_j)$, $\sigma(Y,j) = (c_j, d_j)$.  From $X \leq Y$: $(a_j, b_j) \leq
(c_j, d_j)$ componentwise.  From sub-case 2b: $\sigma(X,j) \neq \sigma(Y,j)$ for all $j \geq 1$
with $\operatorname{prime}^j(Y) \neq 0$.

**Goal**: find $Z \in \Pi$ with $X \xrightarrow{\text{step}} Z$ and $Z \leq Y$.

**Common skeleton** in all four cases:

1. Extract a 2-gene sub-chromosome $X_1$ from $X$, set $\mathrm{rest} = X - X_1$.
2. Apply a primitive mutation $X_1 \to Y_1$, yielding $Z = Y_1 + \mathrm{rest}$.
3. Verify $Z \leq Y$ by checking $\sigma(Z,j) \leq \sigma(Y,j)$ in three ranges:
   $j < r$, $r \leq j \leq s$, $j > s$.

---

## Case 1 — Type 1 mutation, $\varepsilon = -$ (small negative + large positive gene)

See [Case1_Sketch.md](Case1_Sketch.md) for the full proof.

**Hypothesis**: $X$ contains $g^-(r)$ and $g^+(s)$ with $r < s$, $r \leq k$, $s \leq k$.

**Mutation**: $g^-(r) + g^+(s) \longrightarrow g^+(r{-}1) + g^-(s{+}1)$.

**Key point**: the signature gain at levels $j \in [r,s]$ is $(0,1)$, requiring $b_j < d_j$.
This follows from $\Delta b$ non-increasing (Propagation Lemma) and $\Delta b_k \geq \Delta a_k \geq 1$.

---

## Case 2 — Type 1 mutation, $\varepsilon = +$ (small positive + large negative gene)

**Hypothesis**: Case 1 fails.  $X$ contains $g^+(r)$ and $g^-(s)$ with $r < s$, $r \leq k$,
$s \leq k$.

**Mutation**:
$$g^+(r) + g^-(s) \;\longrightarrow\; g^-(r{-}1) + g^+(s{+}1).$$

**Why $Z \leq Y$**: Symmetric to Case 1.  The signature gain at level $j \in [r,s]$ is $(1,0)$
rather than $(0,1)$:
$$\sigma(Z,j) = \sigma(X,j) + (1,0).$$
Dominance gives $b_j \leq d_j$; we need $a_j < c_j$.  The same non-increasing argument applied to
$\Delta a$ (with $\Delta a_k \geq 1$ directly) gives $\Delta a_j \geq 1$ for $j \in [r,s]$,
hence $a_j < c_j$.

*(The precise parity constraint on $k$ that makes Case 1 vs Case 2 applicable is determined by the
sign of the ε parameter in the paper.)*

---

## Case 3 — Type 2 mutation, $\varepsilon = +$ (two positive genes, smallest rank $\geq 2$)

**Hypothesis**: Cases 1 and 2 fail (no opposite-type gene pair with both ranks $\leq k$).  $X$
contains two positive genes $g^+(r_1)$ and $g^+(r_2)$ with $r_1 \leq r_2$ and $r_1 \geq 2$.

**Mutation**:
$$g^+(r_1) + g^+(r_2) \;\longrightarrow\; g^+(r_1{-}2) + g^+(r_2{+}2).$$

**Why $Z \leq Y$** — four ranges:

- **$j < r_1 - 2$**: signatures equal by `mutation_type2_iterate_signature_eq`.
- **$r_1 - 2 \leq j < r_1$**: the lower gene moves from rank $r_1$ to $r_1 - 2$; dominance
  $\sigma(X,j) \leq \sigma(Y,j)$ absorbs the net change.
- **$j \in [r_1, r_2]$**: the net gain at level $j$ is $(1,0)$ (the shifted positive gene now
  contributes), absorbed by $\Delta a_j \geq 1$ from the same propagation argument.
- **$j > r_2$**: both gene pairs vanish; $\sigma(Z,j) = \sigma(X,j) \leq \sigma(Y,j)$.

---

## Case 4 — Type 2 mutation, $\varepsilon = -$ (two negative genes, smallest rank $\geq 2$)

**Hypothesis**: Cases 1–3 all fail.  $X$ contains two negative genes $g^-(r_1)$ and $g^-(r_2)$
with $r_1 \leq r_2$ and $r_1 \geq 2$.

**Mutation**:
$$g^-(r_1) + g^-(r_2) \;\longrightarrow\; g^-(r_1{-}2) + g^-(r_2{+}2).$$

**Why $Z \leq Y$**: Mirror image of Case 3.  The net signature change at intermediate levels is
$(0,1)$, and $\Delta b$ non-increasing (from the same coupled reverse induction) gives $b_j < d_j$
for the relevant range.

---

## Exhaustiveness

Cases 1–4 cover every $X$ that can appear here.  Since $\operatorname{prime}^k(X) \neq 0$ and $X$
has no same-rank pair (15.10), $X$ contains at least one gene of each relevant type.  Under this
constraint:

| Structure of $X$ | Case |
|---|---|
| $g^-(r)$ with $r \leq k$ and $g^+(s)$ with $s > r$, $s \leq k$ | Case 1 |
| $g^+(r)$ with $r \leq k$ and $g^-(s)$ with $s > r$, $s \leq k$ | Case 2 |
| Two positive genes, smallest rank $\geq 2$ | Case 3 |
| Two negative genes, smallest rank $\geq 2$ | Case 4 |

The constraint $r_1 \geq 2$ in Cases 3/4 follows because rank-1 genes cannot be mutated further;
an excess of rank-1 genes would saturate the $\sigma$ bound and contradict $X < Y$ with disjoint
supports.

---

## Summary

The heart of all four cases is the **Propagation Lemma**: conditions 15.6 and 15.7 imply that
$\Delta a_j = c_j - a_j$ and $\Delta b_j = d_j - b_j$ are jointly non-increasing (proved by
reverse induction from the eventually-zero boundary).  This converts the single hypothesis
$\Delta a_k \geq 1$ into $\Delta b_j \geq 1$ (Case 1, via the coupled recurrence) or
$\Delta a_j \geq 1$ (Case 2, directly) throughout the mutation's active range $[r, s]$, which
is exactly what is needed to show $\sigma(Z,j) \leq \sigma(Y,j)$ at the critical intermediate
levels.
