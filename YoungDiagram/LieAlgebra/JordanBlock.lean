import YoungDiagram.LieAlgebra.ClassicalSetup

/-!
# Jordan Block Decomposition for Nilpotent Elements

For a nilpotent element x in the Lie algebra L of a classical group G,
the vector space V decomposes into an orthogonal direct sum of
indecomposable x-invariant f-nondegenerate subspaces:

  V = V₁ ⊕ V₂ ⊕ ⋯ ⊕ Vᵣ

Each Vᵢ is an indecomposable summand. For polarized types (Δᵉₘ),
this is a single Jordan block of size m+1 with sign ε determined
by the form (conditions (5.3)–(5.5)). For nonpolarized types (Δₘ),
the form pairs two Jordan blocks of size m+1 into one indecomposable
summand of dimension 2(m+1) (occurs for j=6 m odd, j=9 m even).

The collection of all these indecomposable types, counted with
multiplicity, gives the nilpotent type `Δ(x) : NilpotentType j`.

## Main definitions

* `extractNilpotentType`: Given a classical setup and a nilpotent x ∈ L,
  extract its combinatorial type `NilpotentType j`.

## Main results (sorry'd)

* `extractNilpotentType_valid`: The extracted type is valid.
* `extractNilpotentType_totalDim`: The total dimension matches dim V.
* `extractNilpotentType_signature`: The chromosome signature matches sig(f).

## Prerequisites from mathlib (not yet available)

* Jordan normal form for nilpotent endomorphisms over a field.
* Classification of indecomposable types for skew-adjoint nilpotent
  endomorphisms (w.r.t. bilinear/sesquilinear forms).
* The sign condition (5.3)–(5.5) from [Djoković 1982].

## References

* [Djoković 1982, §5]
-/

namespace YoungDiagram.LieAlgebra

open NilpotentType

variable {j : SeriesIndex} (S : ClassicalSetup j)

/-! ### Jordan block decomposition of a nilpotent endomorphism

A nilpotent endomorphism x on a finite-dimensional vector space V has a
unique Jordan normal form: V decomposes as a direct sum of cyclic subspaces
  V = ⟨v₁⟩ ⊕ ⟨v₂⟩ ⊕ ⋯ ⊕ ⟨vᵣ⟩
where ⟨vᵢ⟩ = span{vᵢ, xvᵢ, …, x^{mᵢ}vᵢ} has dimension mᵢ + 1.

The Jordan block sizes form a partition of n = dim V. -/

/-- The Jordan partition of a nilpotent endomorphism: the multiset of
block sizes, sorted in decreasing order.

This is the partition λ such that dim(ker x^k) = λ₁' + … + λₖ'
where λ' is the conjugate partition.

TODO: Define via `Module.End.genEigenspace` and generalized eigenspaces
in mathlib. -/
noncomputable def jordanPartition
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (x : Module.End F V) (hx : IsNilpotent x) : Multiset ℕ :=
  sorry

/-- The Jordan partition is a partition of dim V. -/
theorem jordanPartition_sum
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (x : Module.End F V) (hx : IsNilpotent x) :
    (jordanPartition x hx).sum = Module.finrank F V := by
  sorry

/-- All parts of the Jordan partition are positive. -/
theorem jordanPartition_pos
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (x : Module.End F V) (hx : IsNilpotent x) :
    ∀ m ∈ jordanPartition x hx, 0 < m := by
  sorry

/-- The rank of x^k equals the sum of (block_size - k) over blocks of size > k. -/
theorem jordanPartition_rank
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (x : Module.End F V) (hx : IsNilpotent x) (k : ℕ) :
    Module.finrank F (LinearMap.range (x ^ k)) =
      (((jordanPartition x hx).filter (· > k)).map (· - k)).sum := by
  sorry

/-! ### Extraction of nilpotent types

For a nilpotent element x in a classical Lie algebra L, each Jordan block
carries additional sign information determined by the form f.
The sign ε ∈ {+, −} of a block of size m + 1 is determined by the
conditions (5.3)–(5.5):

- j = 4: `(-i)^m · ε · f(v, x^m v) ≥ 0`
- j = 6, 10: `i^m · ε · f(v, x^m v) ≥ 0`
- j = 7, 9: `i^{m-1} · ε · f(v, x^m v) ≥ 0`

where v is a cyclic generator of the Jordan block. -/

/-- Extract the `NilpotentType j` from a nilpotent element x ∈ L.

Decomposes V into indecomposable f-nondegenerate x-invariant summands,
determines the sign ε for each polarized summand via (5.3)–(5.5),
and produces a formal sum of `NilpotentBlock j`.

Note: for nonpolarized cases (j=6 m odd, j=9 m even), one indecomposable
summand of dim 2(m+1) contains two paired Jordan blocks and maps to a
single `NilpotentBlock` with `param = m`.

TODO: Construct from `jordanPartition` + sign conditions (5.3)–(5.5). -/
noncomputable def extractNilpotentType
    (x : S.Elem) (hx : S.IsNilpotentElem x) : NilpotentType j :=
  sorry

/-- The extracted nilpotent type is valid (signs match Table IV). -/
theorem extractNilpotentType_valid
    (x : S.Elem) (hx : S.IsNilpotentElem x) :
    (extractNilpotentType S x hx).IsValid := by
  sorry

/-- The total dimension of the extracted type equals dim V. -/
theorem extractNilpotentType_totalDim
    (x : S.Elem) (hx : S.IsNilpotentElem x) :
    (extractNilpotentType S x hx).totalDim = S.dim := by
  sorry

/-- The chromosome signature of the extracted type equals sig(f). -/
theorem extractNilpotentType_signature
    (x : S.Elem) (hx : S.IsNilpotentElem x) :
    (extractNilpotentType S x hx).toChromosome.signature = S.formSig := by
  sorry

/-- The chromosome of the extracted type lies in the variety Φⱼ. -/
theorem extractNilpotentType_mem_variety
    (x : S.Elem) (hx : S.IsNilpotentElem x) :
    (extractNilpotentType S x hx).toChromosome ∈ j.variety := by
  exact NilpotentType.toChromosome_mem_variety _ (extractNilpotentType_valid S x hx)

end YoungDiagram.LieAlgebra
