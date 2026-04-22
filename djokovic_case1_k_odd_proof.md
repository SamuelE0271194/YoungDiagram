# Proof of Case 1 ($k$ odd) in §15 of Djoković's paper

*Closures of Conjugacy Classes in Classical Real Linear Lie Groups, II*

## Goal

Prove statement (*): given $X, Y \in \Pi(n)$ with $X < Y$, there exists a $\Pi$-mutation $X \to Z$ with $Z \leq Y$.

This is a step in the proof of Theorem 6 for the variety $\Phi = \Pi$ of polarized chromosomes.

---

## 1. Setup after reductions

Writing

$$\sigma(X) = \begin{pmatrix} a_0 & a_1 & a_2 & \cdots \\ b_0 & b_1 & b_2 & \cdots \end{pmatrix}, \qquad \sigma(Y) = \begin{pmatrix} c_0 & c_1 & c_2 & \cdots \\ d_0 & d_1 & d_2 & \cdots \end{pmatrix},$$

where $(a_k, b_k) = \operatorname{sig} X^{(k)}$ and $(c_k, d_k) = \operatorname{sig} Y^{(k)}$, we use induction on $n$ and the lifting property (Lemma 9) to reduce to the case where:

- $a_0 = c_0$, $b_0 = d_0$, and $a_i \leq c_i$, $b_i \leq d_i$ for all $i$ (from $X \leq Y$).
- $X$ and $Y$ are **disjoint** (no shared gene).
- For all $i \geq 1$: if $Y^{(i)} \neq 0$, then $a_i < c_i$ or $b_i < d_i$ (condition (15.9)).
- $X \not\supset g^{+}(k) + g^{-}(k)$ for any $k \geq 1$ (condition (15.10)).

**Working hypothesis:** $a_1 < c_1$.

Let $g_1 = g_{\varepsilon_1}(m)$ be a gene of $X$ of minimal rank $m$, where the subscript convention is

$$g_{\varepsilon}(n) = g^{(-1)^{n-1}\varepsilon}(n).$$

**Case 1:** $\varepsilon_1 = -$.

---

## 2. Existence of $g_2 = g_{+}(k)$ in $X$

Using $\operatorname{sig}(g_{+}(n)) - \operatorname{sig}(g_{+}(n)') = (1, 0)$, the difference $a_0 - a_1$ equals the number of $g_{+}$-genes in $X$ (since $X$ is polarized under the reductions).

From $a_0 = c_0$ and $a_1 < c_1$:

$$a_0 - a_1 > c_0 - c_1 \geq 0,$$

so $X$ contains at least one gene $g_2 = g_{+}(k)$. Choose $k$ minimal.

---

## 3. The mutation

Define $X \to Z$ by

$$g_{-}(m) + g_{+}(k) \;\longrightarrow\; g_{-}(k+1) + g_{+}(m-1).$$

This is a primitive $\Pi$-mutation of type (8.1).

---

## 4. Computing $\sigma(Z) - \sigma(X)$

Direct computation (verified on examples $m=2, k=3$ and $m=3, k=7$) shows:

$$(e_i, f_i) - (a_i, b_i) = \begin{cases} (0, 0) & i < m \text{ or } i > k, \\ \text{either } (1, 0) \text{ or } (0, 1) & m \leq i \leq k, \end{cases}$$

where on the range $[m, k]$ the increment **alternates** between $(1,0)$ and $(0,1)$ in a pattern governed by parity.

For $k$ odd, the coordinates where $\sigma(Z)$ strictly exceeds $\sigma(X)$ are:

$$a_k, \; b_{k-1}, \; a_{k-2}, \; b_{k-3}, \; \ldots, \; b_2.$$

At each such coordinate, we need a strict inequality $a_j < c_j$ or $b_j < d_j$ to conclude $Z \leq Y$.

---

## 5. The chain of inequalities

The paper asserts:

$$\underbrace{c_{k-1} - c_k \leq d_{k-2} - d_{k-1} \leq \cdots \leq c_0 - c_1}_{Y\text{-side: weak}} \;<\; \underbrace{a_0 - a_1 = b_1 - b_2 = \cdots = a_{k-1} - a_k}_{X\text{-side: equalities}}.$$

The three ingredients:

- **Left (weak inequalities):** zig-zag inequalities (15.6)–(15.7) applied to $\sigma(Y)$.
- **Middle (strict inequality):** the Case 1 hypothesis $a_1 < c_1$ combined with $a_0 = c_0$.
- **Right (equalities):** zig-zag inequalities (15.6) applied to $\sigma(X)$, saturated to equalities.

> ### ⚠️ Unclear step: the $X$-side equalities
>
> The paper asserts that the zig-zag inequalities (15.6) applied to $\sigma(X)$ are saturated to **equalities** on the range $i = 1, \ldots, k$:
>
> $$a_0 - a_1 = b_1 - b_2 = a_2 - a_3 = \cdots = a_{k-1} - a_k.$$
>
> The structural reason these hold under the Case 1 reductions is not fully transparent. A rigorous justification would require writing $X = \sum_\alpha g_{\varepsilon_\alpha}(n_\alpha)$, expressing each column-difference $a_{i-1} - a_i$ and $b_{i-1} - b_i$ as a sum of indicators depending on gene ranks $n_\alpha$, subscripts $\varepsilon_\alpha$, and the parity of $i$, and showing these sums are constant on $[1, k]$.
>
> Heuristically: minimality of $m$ (overall rank) and minimality of $k$ (among $g_{+}$-ranks) together with the uniform head-sign behavior of the subscript convention $g_{\pm}(n)$ should force (15.6) to be saturated on this range. But the paper leaves the detailed verification implicit, and the claim is stronger than it might first appear — it requires controlling how *all* genes of $X$ (including $g_{-}$-genes of intermediate rank) contribute column by column.

---

## 6. Telescoping to conclude $Z \leq Y$

Stripping $j$ links from the left of the chain and using the $X$-side equalities gives, for $j = 0, 1, \ldots, k-2$:

$$(\text{$Y$-difference at index } k-j) \;<\; (\text{$X$-difference, equal to } a_{k-1} - a_k).$$

Combined with the weak inequality $a_{k-1-j} \leq c_{k-1-j}$ (or $b_{k-1-j} \leq d_{k-1-j}$), this yields:

| $j$ | strict inequality obtained |
|-----|-----------------------------|
| $0$ | $a_k < c_k$ |
| $1$ | $b_{k-1} < d_{k-1}$ |
| $2$ | $a_{k-2} < c_{k-2}$ |
| $3$ | $b_{k-3} < d_{k-3}$ |
| $\vdots$ | $\vdots$ |
| $k-2$ | $b_2 < d_2$ |

Each strict inequality falls at precisely the coordinate where $\sigma(Z)$ gained a unit over $\sigma(X)$. Combined with $X \leq Y$ at all other coordinates, this gives $Z \leq Y$. $\blacksquare$

---

## Big picture

The proof exhibits a tight interplay:

1. **The mutation** $g_{-}(m) + g_{+}(k) \to g_{-}(k+1) + g_{+}(m-1)$ redistributes one unit of "$-$ charge" rightward from column $m-1$ to column $k$, and one "$+$ charge" leftward, creating an alternating $(1,0)/(0,1)$ pattern of increments on columns $[m, k]$.

2. **The chain of inequalities** encodes how a single bit of slack ($a_1 < c_1$) propagates through:
   - the *monotone* zig-zag structure of $\sigma(Y)$ (weak $\leq$),
   - the *rigid* zig-zag structure of $\sigma(X)$ (equalities),
   
   to produce strict inequalities at exactly the columns where the mutation needs them.

3. **The alternation matches:** the alternating $c$/$d$ pattern on the $Y$-side of the chain corresponds one-for-one with the alternating $(1,0)$/$(0,1)$ pattern of $\sigma(Z) - \sigma(X)$ on $[m, k]$. This matching is what makes the specific mutation formula the "right" choice in Case 1.

---

## References

- D. Ž. Djoković, *Closures of conjugacy classes in classical real linear Lie groups. II*, Trans. Amer. Math. Soc. **270** (1982), 217–252.
- Proof of Case 1 ($k$ odd) appears on page 246.
