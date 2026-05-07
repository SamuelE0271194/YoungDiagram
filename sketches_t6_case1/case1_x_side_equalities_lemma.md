# The $X$-side equalities: context, statement, and proof

*A lemma supporting the proof of Case 1 in §15 of Djoković's paper*
*"Closures of Conjugacy Classes in Classical Real Linear Lie Groups, II"*

---

## Context

We are in §15 of Djoković's paper, working in the variety $\Phi = \Pi$ of polarized chromosomes. The proof of statement (*) (that $X < Y$ admits a mediating $\Pi$-mutation $X \to Z$ with $Z \leq Y$) proceeds by induction on the rank $n$ and reduces, via the lifting property and disjointness arguments, to a setting in which the following hold for $X, Y \in \Pi(n)$:

1. $\sigma(X) = \begin{pmatrix} a_0 & a_1 & \cdots \\ b_0 & b_1 & \cdots \end{pmatrix}$ and $\sigma(Y) = \begin{pmatrix} c_0 & c_1 & \cdots \\ d_0 & d_1 & \cdots \end{pmatrix}$ with $(a_i, b_i) \leq (c_i, d_i)$ for all $i \geq 0$, and $a_0 = c_0$, $b_0 = d_0$.
2. $X$ is polarized; in particular $X = \sum_{\alpha} g_{\varepsilon_\alpha}(n_\alpha)$, where each $\varepsilon_\alpha \in \{+, -\}$ and $n_\alpha \geq 1$, and the subscript convention is $g_{\varepsilon}(n) = g^{(-1)^{n-1}\varepsilon}(n)$.
3. $X$ contains no pair $g^{+}(\ell) + g^{-}(\ell)$ for any $\ell \geq 1$.
4. **Working hypothesis (Case 1):** $a_1 < c_1$, and the gene $g_1 = g_{\varepsilon_1}(m)$ of $X$ of minimal rank $m$ has $\varepsilon_1 = -$.
5. By the existence argument of Section 2 of the previous summary, $X$ contains a gene of the form $g_2 = g_{+}(k)$, and we choose $k$ to be **minimal** among the ranks of $g_{+}$-genes of $X$.

---

## Statement

**Lemma ($X$-side equalities).** *Under the context above,*

$$a_0 - a_1 \;=\; b_1 - b_2 \;=\; a_2 - a_3 \;=\; b_3 - b_4 \;=\; \cdots \;=\; b_{k-2} - b_{k-1} \;=\; a_{k-1} - a_k.$$

*More precisely, for every odd $i \in \{1, 3, 5, \ldots, k\}$,*

$$a_{i-1} - a_i = P,$$

*and for every even $i \in \{2, 4, \ldots, k-1\}$,*

$$b_{i-1} - b_i = P,$$

*where $P$ denotes the total number of $g_{+}$-genes in $X$ (equivalently, the multiplicity of all positive subscript genes in the decomposition of $X$). Moreover $P \geq 1$.*

(For $k$ odd, the chain ends with $a_{k-1} - a_k$. For $k$ even, the chain ends with $b_{k-1} - b_k$. In both cases the final link corresponds to column $i = k$, and the alternation between $a$- and $b$-differences is governed by the parity of the column index.)

---

## Proof

### Step 1: Column-count formula

Define, for each integer $i \geq 1$,

$$P_i := \#\{\alpha : \varepsilon_\alpha = + \text{ and } n_\alpha \geq i\}, \qquad N_i := \#\{\alpha : \varepsilon_\alpha = - \text{ and } n_\alpha \geq i\}.$$

That is, $P_i$ (resp. $N_i$) counts the genes of $X$ with positive (resp. negative) subscript whose rank is at least $i$ — equivalently, the genes that "survive" to column $i$ of the diagram of $X$.

We claim:

$$a_{i-1} - a_i = \begin{cases} P_i & i \text{ odd}, \\ N_i & i \text{ even}, \end{cases} \qquad b_{i-1} - b_i = \begin{cases} N_i & i \text{ odd}, \\ P_i & i \text{ even}. \end{cases} \tag{$\ast$}$$

*Proof of $(\ast)$.* The signature of a chromosome is additive over its genes, so

$$a_{i-1} - a_i = \sum_{\alpha} \bigl[\operatorname{sig}(g_{\varepsilon_\alpha}(n_\alpha)^{(i-1)})_1 - \operatorname{sig}(g_{\varepsilon_\alpha}(n_\alpha)^{(i)})_1\bigr],$$

where $(\,\cdot\,)_1$ denotes the first coordinate of the signature. Each summand equals the indicator that the $i$-th column of the diagram of $g_{\varepsilon_\alpha}(n_\alpha)$ exists and carries a $+$ sign.

By the subscript convention, $g_{+}(n)$ has head sign $+$ and signs alternate column by column, so its column $i$ (when $i \leq n$) carries a $+$ iff $i$ is odd. Symmetrically, $g_{-}(n)$ has head sign $-$, so its column $i$ carries a $+$ iff $i$ is even.

Therefore the sum equals:
- the number of $g_{+}$-genes with $n_\alpha \geq i$ (i.e., $P_i$) if $i$ is odd,
- the number of $g_{-}$-genes with $n_\alpha \geq i$ (i.e., $N_i$) if $i$ is even.

The formula for $b_{i-1} - b_i$ follows by symmetry (count $-$ signs instead of $+$ signs in column $i$). This proves $(\ast)$.

### Step 2: Minimality of $k$ implies $P_i$ is constant on $[1, k]$

By definition, $k$ is the minimum rank of a $g_{+}$-gene in $X$. Therefore, for every gene $g_{+}(n_\alpha)$ in $X$, we have $n_\alpha \geq k$.

Hence for every $i \in \{1, 2, \ldots, k\}$:

$$P_i = \#\{\alpha : \varepsilon_\alpha = + \text{ and } n_\alpha \geq i\} = \#\{\alpha : \varepsilon_\alpha = +\} = P,$$

where $P$ is the total number of $g_{+}$-genes in $X$. The first equality is the definition; the second uses that $n_\alpha \geq k \geq i$ holds automatically for every $g_{+}$-gene.

In particular, $P_1 = P_2 = \cdots = P_k = P$.

### Step 3: Combining

Apply $(\ast)$ to each $i \in \{1, 2, \ldots, k\}$ and use the constancy from Step 2:

| $i$ | parity | difference | value |
|-----|--------|------------|-------|
| $1$ | odd | $a_0 - a_1$ | $P_1 = P$ |
| $2$ | even | $b_1 - b_2$ | $P_2 = P$ |
| $3$ | odd | $a_2 - a_3$ | $P_3 = P$ |
| $4$ | even | $b_3 - b_4$ | $P_4 = P$ |
| $\vdots$ | $\vdots$ | $\vdots$ | $\vdots$ |
| $k-1$ | (parity of $k-1$) | $\begin{cases} b_{k-2} - b_{k-1} & k \text{ odd} \\ a_{k-2} - a_{k-1} & k \text{ even} \end{cases}$ | $P$ |
| $k$ | (parity of $k$) | $\begin{cases} a_{k-1} - a_k & k \text{ odd} \\ b_{k-1} - b_k & k \text{ even} \end{cases}$ | $P$ |

Reading the right-hand column gives the chain of equalities asserted in the lemma.

### Step 4: $P \geq 1$

Since $g_2 = g_{+}(k) \in X$ exists by hypothesis, $X$ contains at least one $g_{+}$-gene, so $P \geq 1$. $\blacksquare$

---

## Remarks

**Remark 1 (role of $g_{-}$-genes).** The proof uses minimality of $k$ but not minimality of $m$. The $N_i$ counts (number of $g_{-}$-genes surviving to column $i$) appear in the formulas $(\ast)$ in the *opposite* coordinate from where the chain runs, so their non-constancy on $[1, k]$ is invisible to this chain. If instead we tried to write a parallel chain $b_0 - b_1 = a_1 - a_2 = b_2 - b_3 = \cdots$, we would need $N_i$ constant, which fails in general because $g_{-}$-genes of intermediate ranks may exist.

**Remark 2 (sharpness).** The chain of equalities terminates at $i = k$ because $P_{k+1}$ may differ from $P_k$ — specifically, $g_2 = g_{+}(k)$ drops out, so $P_{k+1} = P_k - 1 = P - 1$. Thus

$$a_k - a_{k+1} \quad \text{or} \quad b_k - b_{k+1}$$

(whichever has the appropriate parity) equals $P - 1$, breaking the equality chain at the next step. This is consistent with the chain ending precisely at column $k$.

**Remark 3 (use of condition (15.10)).** The hypothesis that $X$ contains no pair $g^{+}(\ell) + g^{-}(\ell)$ is not directly used in this lemma; it was used earlier to ensure $X$ is genuinely polarized (no nonpolarized genes). The lemma actually only requires polarization of $X$.

---

## Lean statement

The lemma is stated for an arbitrary `X : Pi` (no rank constraint needed). The index `j` runs over `[0, g₂.rank)`, and the alternation between the `.1` and `.2` components of the sigma pair is captured by `if Even j`. All sigma values are in `ℚ × ℚ`; the differences live in `ℚ`.

```lean
private lemma x_side_equalities
    {X : Pi}
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.val g ∧ 0 < X.val h)
    {g₂ : Gene}
    (hg₂type : Gene.ofRankAlt g₂.rank GeneType.Positive = Finsupp.single g₂ 1)
    (hg₂pos : 0 < X.val g₂)
    (hg₂min : ∀ g' : Gene,
      Gene.ofRankAlt g'.rank GeneType.Positive = Finsupp.single g' 1 →
      0 < X.val g' → g₂.rank ≤ g'.rank)
    {j : ℕ} (hj : j < g₂.rank) :
    (if Even j then
      (Sigma.sigma X j).1 - (Sigma.sigma X (j + 1)).1
    else
      (Sigma.sigma X j).2 - (Sigma.sigma X (j + 1)).2) =
    (Sigma.sigma X 0).1 - (Sigma.sigma X 1).1 := by
  sorry
```

**Parameters:**
- `hXpn` — condition (15.10): no gene pair `g⁺(ℓ), g⁻(ℓ)` in `X`.
- `hg₂type`, `hg₂pos`, `hg₂min` — `g₂` is the minimal-rank subscript-positive gene; its identity as a gene is recovered from the `Gene.ofRankAlt` form.
- `hj : j < g₂.rank` — `j` ranges over `{0, 1, …, k−1}` where `k = g₂.rank`.

---

## References

- D. Ž. Djoković, *Closures of conjugacy classes in classical real linear Lie groups. II*, Trans. Amer. Math. Soc. **270** (1982), 217–252.
