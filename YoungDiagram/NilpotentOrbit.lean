import YoungDiagram.Variety

/-!
# Nilpotent Orbits and the Chromosome Bijection

This file establishes the combinatorial bridge between nilpotent orbits of
classical real linear Lie groups and chromosomes, following [Djoković 1982].

## Main definitions

* `SeriesIndex`: The series index j ∈ {4, 6, 7, 9, 10} labeling classical groups.
* `NilpotentBlock`: A Jordan block specification (parameter m, sign ε) for series j.
* `NilpotentBlock.toChromosome`: Maps a single block to its chromosome (Table IV).
* `NilpotentType`: A formal sum of blocks — the combinatorial data of a nilpotent orbit.
* `NilpotentType.toChromosome`: Extends the map linearly.

## Key results

* `NilpotentBlock.toChromosome_mem_variety`: Valid blocks map into the variety Φⱼ.
* `NilpotentType.toChromosome_mem_variety`: Valid types map into Φⱼ.
* `toChromosome_injective` (sorry): Lemma 4 injectivity.
* `toChromosome_surjective` (sorry): Lemma 4 surjectivity.

## Sorry'd components

The sorry'd theorems (`toChromosome_injective`, `toChromosome_surjective`,
`toChromosome_mem_variety`, `toChromosome_rank`) are purely combinatorial
facts about Table IV that do not require any Lie algebra theory.
The Lie algebra connection lives in `LieAlgebra/JordanBlock.lean`.

## References

* [Djoković 1982, §5 Table IV, §7 Lemma 4, §7 Theorem 5]
-/

open Finsupp Chromosome

/-! ## Series Index -/

/-- The series index j for classical groups where nilpotent orbit closures
are characterized by chromosome dominance.

Only j ∈ {4, 6, 7, 9, 10} are needed; cases j ∈ {1, 2, 3, 5, 8} are handled
by Theorem 3 (Gerstenhaber–Hesselink) via rank conditions alone.

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
When false, it is Δₘ(0,0) (nonpolarized, unique type). -/
def isPolarizedBlock : SeriesIndex → ℕ → Prop
  | .U,     _ => True
  | .O,     m => Even m
  | .Ostar, m => Odd m
  | .SpR,   m => Odd m
  | .SpH,   m => Even m

instance (j : SeriesIndex) (m : ℕ) : Decidable (j.isPolarizedBlock m) := by
  cases j <;> simp only [isPolarizedBlock] <;> infer_instance

/-- The variety Φⱼ associated to each series (Table IV, last column).

Convention: `Mix (v₁, v₂)` means even-rank genes ∈ v₁, odd-rank genes ∈ v₂.
| j=4  | Π        | `Label 0` |
| j=6  | (2Λ, Π)  | `Label 3` |
| j=7  | (Π, Λ)   | `Label 2` |
| j=9  | (Π, 2Λ)  | `Label 4` |
| j=10 | (Λ, Π)   | `Label 1` |
-/
noncomputable def variety : SeriesIndex → Variety
  | .U     => Variety.Label 0
  | .O     => Variety.Label 3
  | .Ostar => Variety.Label 2
  | .SpR   => Variety.Label 4
  | .SpH   => Variety.Label 1

/-- The index into `Variety.Label` for each series. -/
def toLabelIndex : SeriesIndex → Fin 5
  | .U     => 0
  | .O     => 3
  | .Ostar => 2
  | .SpR   => 4
  | .SpH   => 1

@[simp] lemma variety_eq_label (j : SeriesIndex) :
    j.variety = Variety.Label j.toLabelIndex := by
  cases j <;> rfl

end SeriesIndex

/-! ## Nilpotent Blocks -/

/-- A Jordan block specification for series j.
`param` is the parameter m from §5 (Jordan block size = m + 1).
`sign` is the polarization type ε.

The sign is meaningful (Positive or Negative) when `j.isPolarizedBlock m`;
otherwise (Δₘ(0,0) type) it should be `NonPolarized`.
Use `IsValid` to enforce this constraint.

Note: for nonpolarized blocks (j=6 m odd, j=9 m even), the indecomposable
subspace has dimension 2(m+1), not m+1, because the form pairs two Jordan
blocks of size m+1 (see §5, p.225). Use `blockDim` for the true dimension. -/
structure NilpotentBlock (j : SeriesIndex) where
  param : ℕ
  sign : GeneType
  deriving DecidableEq, Repr

namespace NilpotentBlock

variable {j : SeriesIndex}

/-- A block is valid when its sign matches Table IV:
- Polarized (≠ NonPolarized) when `isPolarizedBlock j m`
- NonPolarized otherwise -/
def IsValid (b : NilpotentBlock j) : Prop :=
  if j.isPolarizedBlock b.param
  then b.sign ≠ .NonPolarized
  else b.sign = .NonPolarized

instance (b : NilpotentBlock j) : Decidable b.IsValid := by
  simp only [IsValid]; split_ifs <;> infer_instance

/-- Construct a valid polarized block (Δᵉₘ(0) type). -/
def mkPolarized (m : ℕ) (ε : GeneType)
    (_ : j.isPolarizedBlock m) (_ : ε ≠ .NonPolarized) : NilpotentBlock j :=
  ⟨m, ε⟩

/-- Construct a valid nonpolarized block (Δₘ(0,0) type). -/
def mkNonpolarized (m : ℕ) (_ : ¬j.isPolarizedBlock m) : NilpotentBlock j :=
  ⟨m, .NonPolarized⟩

lemma mkPolarized_isValid {m : ℕ} {ε : GeneType} {hpol : j.isPolarizedBlock m}
    {hε : ε ≠ .NonPolarized} : (mkPolarized m ε hpol hε).IsValid := by
  simp [IsValid, mkPolarized, hpol, hε]

lemma mkNonpolarized_isValid {m : ℕ} {hnpol : ¬j.isPolarizedBlock m} :
    (mkNonpolarized m hnpol : NilpotentBlock j).IsValid := by
  simp [IsValid, mkNonpolarized, hnpol]

/-- The dimension of the indecomposable subspace for a block (§5).

For polarized blocks (Δᵉₘ), the subspace has a single Jordan block of size m+1,
so `blockDim = m + 1`. For nonpolarized blocks (Δₘ) in j=6 (m odd) and j=9
(m even), the form pairs two Jordan blocks, giving `blockDim = 2(m + 1)`. -/
def blockDim (b : NilpotentBlock j) : ℕ :=
  match j with
  | .U     => b.param + 1
  | .O     => if Even b.param then b.param + 1 else 2 * (b.param + 1)
  | .Ostar => b.param + 1
  | .SpR   => if Even b.param then 2 * (b.param + 1) else b.param + 1
  | .SpH   => b.param + 1

/-- The chromosome X(Δ) of a single indecomposable nilpotent block (Table IV).

| j   | m even                  | m odd                    |
|-----|-------------------------|--------------------------|
| U   | gᵉ(m+1)                | gᵉ(m+1)                 |
| O   | gᵉ(m+1)                | 2·g(m+1)                |
| O*  | g(m+1)                 | gᵉ(m+1)                 |
| SpR | 2·g(m+1)               | gᵉ(m+1)                 |
| SpH | gᵉ(m+1)                | g(m+1)                  |
-/
noncomputable def toChromosome (b : NilpotentBlock j) : Chromosome :=
  let m := b.param
  let ε := b.sign
  match j with
  | .U     => Gene.ofRank (m + 1) ε
  | .O     => if Even m then Gene.ofRank (m + 1) ε
              else 2 • Gene.ofRank (m + 1) .NonPolarized
  | .Ostar => if Even m then Gene.ofRank (m + 1) .NonPolarized
              else Gene.ofRank (m + 1) ε
  | .SpR   => if Even m then 2 • Gene.ofRank (m + 1) .NonPolarized
              else Gene.ofRank (m + 1) ε
  | .SpH   => if Even m then Gene.ofRank (m + 1) ε
              else Gene.ofRank (m + 1) .NonPolarized

/-- For j = U (series 4), the chromosome is simply the gene gᵉ(m+1). -/
@[simp] lemma toChromosome_U (b : NilpotentBlock .U) :
    b.toChromosome = Gene.ofRank (b.param + 1) b.sign := rfl

/-- A valid block's chromosome lies in the variety Φⱼ. -/
theorem toChromosome_mem_variety (b : NilpotentBlock j) (hb : b.IsValid) :
    b.toChromosome ∈ j.variety := by
  sorry

end NilpotentBlock

/-! ## Nilpotent Types -/

/-- A nilpotent type for series j is a formal sum of Jordan block specifications.
This is the combinatorial data extracted from a nilpotent element x ∈ L
via its Jordan block decomposition. -/
abbrev NilpotentType (j : SeriesIndex) := NilpotentBlock j →₀ ℕ

namespace NilpotentType

variable {j : SeriesIndex}

/-- A nilpotent type is valid when all its constituent blocks are valid. -/
def IsValid (Δ : NilpotentType j) : Prop :=
  ∀ b ∈ Δ.support, b.IsValid

/-- The chromosome X(Δ) of a nilpotent type, extended linearly from blocks. -/
noncomputable def toChromosome (Δ : NilpotentType j) : Chromosome :=
  Δ.sum fun b n => n • b.toChromosome

/-- The total dimension of V = Σᵢ blockDim(bᵢ) × multiplicity.

For j=4, 7, 10 this equals Σᵢ (mᵢ + 1) × nᵢ. For j=6 and j=9, nonpolarized
blocks contribute 2(m + 1) per occurrence (§5, p.225). -/
def totalDim (Δ : NilpotentType j) : ℕ :=
  Δ.sum fun b n => n * b.blockDim

@[simp] lemma toChromosome_zero : (0 : NilpotentType j).toChromosome = 0 :=
  sum_zero_index

lemma toChromosome_add (Δ₁ Δ₂ : NilpotentType j) :
    (Δ₁ + Δ₂).toChromosome = Δ₁.toChromosome + Δ₂.toChromosome :=
  sum_add_index' (fun _ => zero_nsmul _) fun _ _ _ => add_nsmul ..

lemma toChromosome_single (b : NilpotentBlock j) (n : ℕ) :
    toChromosome (single b n) = n • b.toChromosome := by
  simp [toChromosome]

/-- The chromosome map as an additive monoid homomorphism. -/
noncomputable def toChromosomeHom : NilpotentType j →+ Chromosome where
  toFun := toChromosome
  map_zero' := toChromosome_zero
  map_add' := toChromosome_add

/-- For valid nilpotent types, the chromosome lies in the variety Φⱼ. -/
theorem toChromosome_mem_variety (Δ : NilpotentType j) (hΔ : Δ.IsValid) :
    Δ.toChromosome ∈ j.variety := by
  sorry

/-- The rank of the chromosome equals the total dimension. -/
lemma toChromosome_rank (Δ : NilpotentType j) :
    Δ.toChromosome.rank = Δ.totalDim := by
  sorry

end NilpotentType

/-! ## Lemma 4: The Chromosome Bijection

The map θ ↦ X(θ) from nilpotent G-orbits in L to chromosomes is a bijection
onto {X ∈ Φⱼ | sig(X) = sig(f)}.

Since we lack Jordan normal form theory in mathlib, we state the two halves
(injectivity and surjectivity) as sorry'd theorems. The combinatorial content
(chromosomes, varieties, mutations, dominance) is fully proved elsewhere. -/

/-- [Lemma 4, injectivity] Different valid nilpotent types produce different
chromosomes. This is a purely combinatorial fact about Table IV: each gene in
the chromosome uniquely determines the block that produced it (via rank, type,
and parity). -/
theorem NilpotentType.toChromosome_injective (j : SeriesIndex) :
    Function.Injective
      (fun (Δ : {Δ : NilpotentType j // Δ.IsValid}) => Δ.1.toChromosome) := by
  sorry

/-- [Lemma 4, surjectivity] Every chromosome in Φⱼ arises from some valid
nilpotent type. This is a purely combinatorial fact: the variety constraints
(e.g., even multiplicities in 2Λ) exactly match the structure of Table IV,
so any X ∈ Φⱼ can be decomposed into valid blocks. -/
theorem NilpotentType.toChromosome_surjective (j : SeriesIndex)
    (X : Chromosome) (hX : X ∈ j.variety) :
    ∃ Δ : NilpotentType j, Δ.IsValid ∧ Δ.toChromosome = X := by
  sorry

/-! ## Theorem 5: Orbit Closure Criterion (Interface)

The main theorem [Djoković 1982, Theorem 5] states:

  θ₁ ⊆ cl(θ₂)  ⟺  X(θ₁) ≤ X(θ₂)

where ≤ is the chromosome dominance order (already defined on `Chromosome`).

**Necessity** (⟹): Proved via rank inequalities [Djoković 1980].
**Sufficiency** (⟸): Uses Theorem 6 (enough mutations, being formalized in
`Mutations.lean` / `Lifting.lean`) + explicit one-parameter family constructions
for each primitive mutation type (§§9–12).

Both directions require the algebraic connection (Lemma 4) between orbits and
chromosomes. Once that bridge is established, the combinatorial machinery
already in this project provides the core of the sufficiency proof. -/

-- Future work: formalize Theorem 5 once the Lie algebra bridge is in place.
-- The key algebraic ingredients are:
-- 1. Lemma 4 (above, sorry'd)
-- 2. For each primitive Φⱼ-mutation X → Y (formulas 8.1–8.17),
--    construct an explicit x(t) = x₀ + t·x₁ ∈ L with
--    x(0) ∈ θ₁ and x(t) ∈ θ₂ for t > 0 (§§9–12).
-- 3. Theorem 6: enough mutations (being formalized in Mutations.lean).
