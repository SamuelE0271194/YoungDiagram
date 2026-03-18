import YoungDiagram.Variety

/-!
# Nilpotent Orbits and the Chromosome Bijection

This file establishes the combinatorial bridge between nilpotent orbits of
classical real linear Lie groups and chromosomes, following [Djoković 1982].

## References

* [Djoković 1982, §1 Table I, §4, §5 Table IV, §6 (6.2), §7 Lemma 4]
-/

open Finsupp Chromosome

/-! ## Series Index -/

/-- The series index j for classical groups where nilpotent orbit closures
are characterized by chromosome dominance. [§1 Table I]

| `SeriesIndex` | j  | G           | F | Form f           |
|---------------|----|-------------|---|------------------|
| `U`           | 4  | U(k, n−k)   | ℂ | hermitian         |
| `O`           | 6  | O(k, n−k)   | ℝ | symmetric         |
| `Ostar`       | 7  | O*(2n)      | ℍ | skew-hermitian    |
| `SpR`         | 9  | Sp_{2n}(ℝ)  | ℝ | skew-symmetric    |
| `SpH`         | 10 | Sp(k, n−k)  | ℍ | hermitian         |
-/
inductive SeriesIndex
  | U     -- j = 4
  | O     -- j = 6
  | Ostar -- j = 7
  | SpR   -- j = 9
  | SpH   -- j = 10
  deriving DecidableEq, Repr

namespace SeriesIndex

/-- Whether a Jordan block with parameter m carries a polarized sign in series j.
When true, the indecomposable type is Δᵉₘ(0) with ε ∈ {+, −}.
When false, it is Δₘ(0,0) (nonpolarized, unique type).
[§5 Table IV, column Δ: the split between Δᵉₘ(0) and Δₘ(0,0) rows] -/
def isPolarizedBlock : SeriesIndex → ℕ → Prop
  | .U,     _ => True
  | .O,     m => Even m
  | .Ostar, m => Odd m
  | .SpR,   m => Odd m
  | .SpH,   m => Even m

instance (j : SeriesIndex) (m : ℕ) : Decidable (j.isPolarizedBlock m) := by
  cases j <;> simp only [isPolarizedBlock] <;> infer_instance

/-- The variety Φⱼ associated to each series. [§5 Table IV, last column; §6 formula (6.2)]

| j    | Variety  | Label     |
|------|----------|-----------|
| j=4  | Π        | `Label 0` |
| j=6  | (2Λ, Π)  | `Label 3` |
| j=7  | (Π, Λ)   | `Label 2` |
| j=9  | (Π, 2Λ)  | `Label 4` |
| j=10 | (Λ, Π)   | `Label 1` |
-/
noncomputable def variety : SeriesIndex → Variety
  | .U     => .Label 0
  | .O     => .Label 3
  | .Ostar => .Label 2
  | .SpR   => .Label 4
  | .SpH   => .Label 1

end SeriesIndex

/-! ## Nilpotent Blocks -/

/-- The combinatorial data of a single indecomposable nilpotent block for series j.
[§5 Table IV]

In the block decomposition V = V₁ ⊕ ⋯ ⊕ Vᵣ of a nilpotent x ∈ L, each
summand Vₖ is characterized by two pieces of data:
- `param` (= m): controls the Jordan block size (= m + 1). [§5, formulas (5.1)–(5.2)]
- `sign` (= ε): the polarization, `Positive`/`Negative` for type Δᵉₘ(0),
  or `NonPolarized` for type Δₘ(0,0). [§5 Table IV, column Δ]

Whether a block is polarized depends on j and the parity of m; use `IsValid`
to check that `sign` is consistent with `param`. Use `blockDim` for dim Vₖ. -/
structure NilpotentBlock (j : SeriesIndex) where
  param : ℕ
  sign : GeneType
  deriving DecidableEq, Repr

namespace NilpotentBlock

variable {j : SeriesIndex}

/-- A block is valid when its sign matches Table IV: [§5 Table IV, column Δ]
- Polarized (`isPolarizedBlock j m`) → type Δᵉₘ(0), ε = ±
- NonPolarized → type Δₘ(0,0) -/
def IsValid (b : NilpotentBlock j) : Prop :=
  if j.isPolarizedBlock b.param
  then b.sign ≠ .NonPolarized
  else b.sign = .NonPolarized

instance (b : NilpotentBlock j) : Decidable b.IsValid := by
  simp only [IsValid]; split_ifs <;> infer_instance

/-- Construct a valid polarized block (Δᵉₘ(0) type). [§5 Table IV] -/
def mkPolarized (m : ℕ) (ε : GeneType)
    (_ : j.isPolarizedBlock m) (_ : ε ≠ .NonPolarized) : NilpotentBlock j :=
  ⟨m, ε⟩

/-- Construct a valid nonpolarized block (Δₘ(0,0) type). [§5 Table IV] -/
def mkNonpolarized (m : ℕ) (_ : ¬j.isPolarizedBlock m) : NilpotentBlock j :=
  ⟨m, .NonPolarized⟩

lemma mkPolarized_isValid {m : ℕ} {ε : GeneType} {hpol : j.isPolarizedBlock m}
    {hε : ε ≠ .NonPolarized} : (mkPolarized m ε hpol hε).IsValid := by
  simp [IsValid, mkPolarized, hpol, hε]

lemma mkNonpolarized_isValid {m : ℕ} {hnpol : ¬j.isPolarizedBlock m} :
    (mkNonpolarized m hnpol : NilpotentBlock j).IsValid := by
  simp [IsValid, mkNonpolarized, hnpol]

/-- The dimension of the indecomposable subspace for a block. [§5, representative triples]

- For polarized blocks (Δᵉₘ), the subspace has a single Jordan block of size m+1,
so `blockDim = m + 1`. [§5, formulas (5.1)–(5.2)]
- For nonpolarized blocks (Δₘ) in j=6 (m odd) and j=9 (m even), the form pairs
two Jordan blocks, giving `blockDim = 2(m + 1)`. [§5, p.225, Δₘ(0,0) representatives] -/
def blockDim (b : NilpotentBlock j) : ℕ :=
  match j with
  | .U     => b.param + 1
  | .O     => if Even b.param then b.param + 1 else 2 * (b.param + 1)
  | .Ostar => b.param + 1
  | .SpR   => if Even b.param then 2 * (b.param + 1) else b.param + 1
  | .SpH   => b.param + 1

/-- The chromosome X(Δ) of a single indecomposable nilpotent block. [§5 Table IV, column X]

| j   | m even                 | m odd                   |
|-----|------------------------|-------------------------|
| U   | gᵉ(m+1)                | gᵉ(m+1)                 |
| O   | gᵉ(m+1)                | 2·g(m+1)                |
| O*  | g(m+1)                 | gᵉ(m+1)                 |
| SpR | 2·g(m+1)               | gᵉ(m+1)                 |
| SpH | gᵉ(m+1)                | g(m+1)                  |
-/
noncomputable def toChromosome (b : NilpotentBlock j) : Chromosome :=
  match j with
  | .U     => Gene.ofRank (b.param + 1) b.sign
  | .O     => if Even b.param then Gene.ofRank (b.param + 1) b.sign
              else 2 • Gene.ofRank (b.param + 1) .NonPolarized
  | .Ostar => if Even b.param then Gene.ofRank (b.param + 1) .NonPolarized
              else Gene.ofRank (b.param + 1) b.sign
  | .SpR   => if Even b.param then 2 • Gene.ofRank (b.param + 1) .NonPolarized
              else Gene.ofRank (b.param + 1) b.sign
  | .SpH   => if Even b.param then Gene.ofRank (b.param + 1) b.sign
              else Gene.ofRank (b.param + 1) .NonPolarized

/-- For j = U (series 4), the chromosome is simply the gene gᵉ(m+1). [§5 Table IV, j=4 row] -/
@[simp] lemma toChromosome_U (b : NilpotentBlock .U) :
    b.toChromosome = Gene.ofRank (b.param + 1) b.sign := rfl

/-- A valid block's chromosome lies in the variety Φⱼ.
[§5 Table IV: the Φⱼ column records exactly which variety each indecomposable type belongs to] -/
theorem toChromosome_mem_variety (b : NilpotentBlock j) (hb : b.IsValid) :
    b.toChromosome ∈ j.variety := by
  sorry

end NilpotentBlock

/-! ## Nilpotent Types -/

/-- A nilpotent type for series j is a formal sum of Jordan block specifications.
This is the combinatorial data extracted from a nilpotent element x ∈ L
via its Jordan block decomposition. [§5: "each type Δ can be expressed as a sum
of indecomposable types and such a decomposition is unique"] -/
abbrev NilpotentType (j : SeriesIndex) := NilpotentBlock j →₀ ℕ

namespace NilpotentType

variable {j : SeriesIndex}

/-- A nilpotent type is valid when all its constituent blocks are valid.
[§5 Table IV: each indecomposable summand must satisfy the sign constraint for its j and m] -/
def IsValid (Δ : NilpotentType j) : Prop :=
  ∀ b ∈ Δ.support, b.IsValid

/-- The chromosome X(Δ) of a nilpotent type, extended linearly from blocks.
[§6: X(Δ) is defined as the sum of the chromosomes of its indecomposable summands;
 §7: this X(Δ) is the label used in Lemma 4 and Theorem 5] -/
noncomputable def toChromosome : NilpotentType j →+ Chromosome where
  toFun Δ := Δ.sum fun b n ↦ n • b.toChromosome
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ zero_nsmul _) fun _ _ _ ↦ add_nsmul ..

/-- The total dimension of V = Σᵢ blockDim(bᵢ) × multiplicity.
[§5: dim V = dim V₁ + ⋯ + dim Vᵣ where V = V₁ ⊕ ⋯ ⊕ Vᵣ is the block decomposition]

For j=4, 7, 10 this equals Σᵢ (mᵢ + 1) × nᵢ. For j=6 and j=9, nonpolarized
blocks contribute 2(m + 1) per occurrence (§5, p.225). -/
def totalDim (Δ : NilpotentType j) : ℕ :=
  Δ.sum fun b n ↦ n * b.blockDim

lemma toChromosome_single (b : NilpotentBlock j) (n : ℕ) :
    toChromosome (single b n) = n • b.toChromosome := by
  simp [toChromosome]

/-- For valid nilpotent types, the chromosome lies in the variety Φⱼ.
[§5 Table IV last column + §6 (6.2): varieties are closed under addition,
 so X(Δ) = ΣX(Δᵢ) ∈ Φⱼ whenever each indecomposable X(Δᵢ) ∈ Φⱼ] -/
theorem toChromosome_mem_variety (Δ : NilpotentType j) (hΔ : Δ.IsValid) :
    Δ.toChromosome ∈ j.variety := by
  sorry

/-- The rank of the chromosome equals the total dimension of V. [§6: r(X) = n where dim V = n;
 §5 Table IV: rank of X(Δᵉₘ) = m+1 and rank of X(Δₘ(0,0)) = 2(m+1) for j=6,9] -/
lemma toChromosome_rank (Δ : NilpotentType j) :
    Δ.toChromosome.rank = Δ.totalDim := by
  sorry

end NilpotentType

/-! ## Combinatorial core of the chromosome bijection [§5 Table IV; used by §7 Lemma 4]

The paper's Lemma 4 (§7) states that θ ↦ X(θ) is a bijection from nilpotent
G-orbits onto {X ∈ Φⱼ | sig(X) = sig(f)}.  The **full** Lemma 4 on orbits
is stated as `chromosomeBijection` in `LieAlgebra/OrbitClosure.lean`.

This section provides the **combinatorial core**: the map `NilpotentType → Chromosome`
is injective on valid types, and every X ∈ Φⱼ arises from some valid type.
These are purely combinatorial facts about Table IV, independent of Lie theory. -/

/-- [§7 Lemma 4, injectivity] Different valid nilpotent types produce different
chromosomes. This is a purely combinatorial fact about Table IV: each gene in
the chromosome uniquely determines the block that produced it (via rank, type,
and parity). The Lie-algebraic statement (orbits biject with types) is in
`LieAlgebra/JordanBlock.lean`. -/
theorem NilpotentType.toChromosome_injective (j : SeriesIndex) :
    Function.Injective
      (fun (Δ : {Δ : NilpotentType j // Δ.IsValid}) ↦ Δ.1.toChromosome) := by
  sorry

/-- [§7 Lemma 4, surjectivity] Every chromosome in Φⱼ arises from some valid
nilpotent type. This is a purely combinatorial fact: the variety constraints
(e.g., even multiplicities in 2Λ) exactly match the structure of Table IV,
so any X ∈ Φⱼ can be decomposed into valid blocks. [§5 Table IV; §6 (6.2)] -/
theorem NilpotentType.toChromosome_surjective (j : SeriesIndex)
    (X : Chromosome) (hX : X ∈ j.variety) :
    ∃ Δ : NilpotentType j, Δ.IsValid ∧ Δ.toChromosome = X := by
  sorry
