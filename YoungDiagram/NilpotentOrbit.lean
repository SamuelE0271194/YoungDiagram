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
  | U
  | O
  | Ostar
  | SpR
  | SpH
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

instance {j : SeriesIndex} {m : ℕ} : Decidable (j.isPolarizedBlock m) := by
  cases j <;> dsimp only [isPolarizedBlock] <;> infer_instance

/-- The variety Φⱼ associated to each series. [§5 Table IV, last column; §6 formula (6.2)]

| `SeriesIndex`  | Variety                 | Label     |
|----------------|-------------------------|-----------|
| `U`            | `Pi`                    | 0         |
| `O`            | `Mix (2 • Lambda, Pi)`  | 3         |
| `Ostar`        | `Mix (Pi, Lambda)`      | 2         |
| `SpR`          | `Mix (Pi, 2 • Lambda)`  | 4         |
| `SpH`          | `Mix (Lambda, Pi)`      | 1         |
-/
noncomputable def variety : SeriesIndex → Variety
  | .U     => .Label 0
  | .O     => .Label 3
  | .Ostar => .Label 2
  | .SpR   => .Label 4
  | .SpH   => .Label 1

lemma variety_def_U : variety .U = .Pi := rfl

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

open Variety

namespace NilpotentBlock

variable {j : SeriesIndex}

/-- A block is valid when its sign matches Table IV: [§5 Table IV, column Δ]
- Polarized (`isPolarizedBlock j m`) → type Δᵉₘ(0), ε = ±
- NonPolarized → type Δₘ(0,0) -/
def IsValid (b : NilpotentBlock j) : Prop :=
  if j.isPolarizedBlock b.param then b.sign ≠ .NonPolarized
    else b.sign = .NonPolarized

instance {b : NilpotentBlock j} : Decidable b.IsValid := by
  dsimp only [IsValid]; split_ifs <;> infer_instance

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

lemma toChromosome_def_U (b : NilpotentBlock .U) :
  b.toChromosome = Gene.ofRank (b.param + 1) b.sign := rfl

lemma toChromosome_mem_variety_U {b : NilpotentBlock .U} (hb : b.IsValid) :
    b.toChromosome ∈ SeriesIndex.U.variety := by
  rwa [toChromosome_def_U, SeriesIndex.variety_def_U,
      mem_Pi_iff, IsPolarized_ofRank (Nat.le_add_left ..)]

lemma toChromosome_mem_variety_O {b : NilpotentBlock .O} (hb : b.IsValid) :
    b.toChromosome ∈ SeriesIndex.O.variety := sorry

lemma toChromosome_mem_variety_Ostar {b : NilpotentBlock .Ostar} (hb : b.IsValid) :
    b.toChromosome ∈ SeriesIndex.Ostar.variety := sorry

lemma toChromosome_mem_variety_SpR {b : NilpotentBlock .SpR} (hb : b.IsValid) :
    b.toChromosome ∈ SeriesIndex.SpR.variety := sorry

lemma toChromosome_mem_variety_SpH {b : NilpotentBlock .SpH} (hb : b.IsValid) :
    b.toChromosome ∈ SeriesIndex.SpH.variety := sorry

/-- A valid block's chromosome lies in the variety Φⱼ.
[§5 Table IV: the Φⱼ column records exactly which variety each indecomposable type belongs to] -/
theorem toChromosome_mem_variety {b : NilpotentBlock j} (hb : b.IsValid) :
    b.toChromosome ∈ j.variety :=
  match j with
  | .U => toChromosome_mem_variety_U hb
  | .O => toChromosome_mem_variety_O hb
  | .Ostar => toChromosome_mem_variety_Ostar hb
  | .SpR => toChromosome_mem_variety_SpR hb
  | .SpH => toChromosome_mem_variety_SpH hb

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

lemma IsValid_iff_add {Δ₁ Δ₂ : NilpotentType j} :
    (Δ₁ + Δ₂).IsValid ↔ Δ₁.IsValid ∧ Δ₂.IsValid := by
  unfold IsValid
  rw [support_add_eq', Finset.forall_mem_union]

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
  simp only [toChromosome, AddMonoidHom.coe_mk, ZeroHom.coe_mk, zero_nsmul, sum_single_index]

lemma toChromosome_mem_variety_U {Δ : NilpotentType .U} (hΔ : Δ.IsValid) :
    Δ.toChromosome ∈ SeriesIndex.U.variety := by
  induction Δ using Finsupp.induction
  · rw [map_zero]; exact zero_mem _
  · expose_names
    rw [map_add]
    refine add_mem ?_ ?_
    · rw [toChromosome_single]
      refine nsmul_mem (NilpotentBlock.toChromosome_mem_variety (hΔ a ?_)) b
      rw [support_add_eq']
      refine Finset.mem_union_left f.support ?_
      rwa [mem_support_iff, single_eq_same, ne_eq]
    · exact h_2 (IsValid_iff_add.1 hΔ).2

lemma toChromosome_mem_variety_O {Δ : NilpotentType .O} (hΔ : Δ.IsValid) :
    Δ.toChromosome ∈ SeriesIndex.O.variety := sorry

lemma toChromosome_mem_variety_Ostar {Δ : NilpotentType .Ostar} (hΔ : Δ.IsValid) :
    Δ.toChromosome ∈ SeriesIndex.Ostar.variety := sorry

lemma toChromosome_mem_variety_SpR {Δ : NilpotentType .SpR} (hΔ : Δ.IsValid) :
    Δ.toChromosome ∈ SeriesIndex.SpR.variety := sorry

lemma toChromosome_mem_variety_SpH {Δ : NilpotentType .SpH} (hΔ : Δ.IsValid) :
    Δ.toChromosome ∈ SeriesIndex.SpH.variety := sorry

/-- For valid nilpotent types, the chromosome lies in the variety Φⱼ.
[§5 Table IV last column + §6 (6.2): varieties are closed under addition,
 so X(Δ) = ΣX(Δᵢ) ∈ Φⱼ whenever each indecomposable X(Δᵢ) ∈ Φⱼ] -/
theorem toChromosome_mem_variety {Δ : NilpotentType j} (hΔ : Δ.IsValid) :
    Δ.toChromosome ∈ j.variety :=
  match j with
  | .U => toChromosome_mem_variety_U hΔ
  | .O => toChromosome_mem_variety_O hΔ
  | .Ostar => toChromosome_mem_variety_Ostar hΔ
  | .SpR => toChromosome_mem_variety_SpR hΔ
  | .SpH => toChromosome_mem_variety_SpH hΔ

/-- The rank of the chromosome equals the total dimension of V. [§6: r(X) = n where dim V = n;
 §5 Table IV: rank of X(Δᵉₘ) = m+1 and rank of X(Δₘ(0,0)) = 2(m+1) for j=6,9] -/
lemma toChromosome_rank (Δ : NilpotentType j) :
    Δ.toChromosome.rank = Δ.totalDim := by
  sorry

end NilpotentType

noncomputable def NilpotentType.toChromosome_bijective (j : SeriesIndex) :
    {Δ : NilpotentType j | Δ.IsValid} ≃ j.variety := by
  refine Equiv.ofBijective (fun Δ ↦
    ⟨Δ.1.toChromosome, Δ.1.toChromosome_mem_variety Δ.2⟩) ⟨?_, ?_⟩
  · sorry
  · sorry
