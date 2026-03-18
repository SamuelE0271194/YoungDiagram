import Mathlib.GroupTheory.GroupAction.Defs
import YoungDiagram.LieAlgebra.JordanBlock

/-!
# Orbit Closure and the Main Theorem

The classical group G acts on its Lie algebra L via the adjoint representation:
  Ad(g)(x) = g · x · g⁻¹

Two nilpotent elements x, y ∈ L are in the same G-orbit iff they have
the same nilpotent type (same Jordan blocks with same signs).

The main theorem (Theorem 5) states that for nilpotent G-orbits θ₁, θ₂:

  θ₁ ⊆ cl(θ₂)  ⟺  X(θ₁) ≤ X(θ₂)

where X(θ) is the chromosome of the orbit and ≤ is the dominance order.

## Main definitions

* `ClassicalSetup.adjointAction`: The adjoint action of G on L.
* `ClassicalSetup.nilpotentOrbit`: The G-orbit of a nilpotent element.
* `ClassicalSetup.orbitChromosome`: The chromosome X(θ) of an orbit.

## Main results (sorry'd)

* `extractNilpotentType_orbit_invariant`: Nilpotent type is constant on orbits.
* `orbit_closure_iff_dominance`: Theorem 5 — orbit closure ↔ chromosome dominance.

## Proof structure for Theorem 5

**Necessity** (⟹): If θ₁ ⊆ cl(θ₂) then rank(x^k) ≤ rank(y^k) for all k,
which implies sig(X(θ₁)^(k)) ≤ sig(X(θ₂)^(k)), i.e., X(θ₁) ≤ X(θ₂).
[Proved in Djoković 1980]

**Sufficiency** (⟸): If X(θ₁) ≤ X(θ₂), Theorem 6 (enough mutations) provides
a chain X(θ₁) = X₀ → X₁ → ⋯ → Xₘ = X(θ₂) of primitive Φⱼ-mutations.
For each mutation Xᵢ → Xᵢ₊₁, an explicit one-parameter family
x(t) = x₀ + t·x₁ ∈ L is constructed (§§9–12) with x(0) ∈ θᵢ and x(t) ∈ θᵢ₊₁.

The combinatorial core (Theorem 6) is being formalized in `Mutations.lean`
and `Lifting.lean`. The algebraic constructions of x(t) are the remaining
sorry'd components.

## References

* [Djoković 1982, §7 Theorem 5, §§9–12]
-/

namespace YoungDiagram.LieAlgebra

variable {j : SeriesIndex} (S : ClassicalSetup j)

/-! ### The adjoint action

The classical group G acts on L by conjugation: Ad(g)(x) = g·x·g⁻¹.
Since G preserves the form f, Ad(g) maps L to L. -/

/-- The classical group G as a subgroup of GL(V).
G = {g ∈ GL_F(V) : f(gv, gw) = f(v, w) ∀ v, w}. -/
noncomputable def classicalGroup : Subgroup (S.V ≃ₗ[S.F] S.V) :=
  sorry

/-- The adjoint action of G on L.
For g ∈ G, the map Ad(g) sends x ∈ L to g·x·g⁻¹ ∈ L. -/
noncomputable def adjointAction :
    classicalGroup S → S.Elem → S.Elem :=
  sorry

/-- The adjoint action preserves nilpotency. -/
theorem adjointAction_preserves_nilpotent
    (g : classicalGroup S) (x : S.Elem) (hx : S.IsNilpotentElem x) :
    S.IsNilpotentElem (adjointAction S g x) := by
  sorry

/-! ### Nilpotent orbits -/

/-- Two nilpotent elements are in the same G-orbit if one is conjugate
to the other by an element of G. -/
def NilpotentOrbitRel : S.nilpotentSet → S.nilpotentSet → Prop :=
  fun ⟨x, _⟩ ⟨y, _⟩ =>
    ∃ g : classicalGroup S, adjointAction S g x = y

/-- The orbit relation is an equivalence relation. -/
theorem nilpotentOrbitRel_equivalence :
    Equivalence (NilpotentOrbitRel S) := by
  sorry

/-- The nilpotent type is constant on G-orbits:
if y = Ad(g)(x) then Δ(y) = Δ(x). -/
theorem extractNilpotentType_orbit_invariant
    (x y : S.Elem) (hx : S.IsNilpotentElem x) (hy : S.IsNilpotentElem y)
    (g : classicalGroup S) (hg : adjointAction S g x = y) :
    extractNilpotentType S x hx = extractNilpotentType S y hy := by
  sorry

/-- The chromosome X(θ) of a nilpotent orbit θ.
Well-defined by `extractNilpotentType_orbit_invariant`. -/
noncomputable def orbitChromosome
    (x : S.Elem) (hx : S.IsNilpotentElem x) : Chromosome :=
  (extractNilpotentType S x hx).toChromosome

/-! ### Orbit closure -/

/-- The closure of a nilpotent orbit.
θ₁ ⊆ cl(θ₂) means every neighborhood of every point in θ₁ meets θ₂.
Equivalently (for algebraic groups), θ₁ is in the Zariski closure of θ₂.

For our purposes, this is characterized algebraically:
θ₁ ⊆ cl(θ₂) iff there exists a family x(t) with x(0) ∈ θ₁ and x(t) ∈ θ₂
for t > 0 (or t ≠ 0). -/
def orbitClosureContains
    (x₁ x₂ : S.Elem) (hx₁ : S.IsNilpotentElem x₁) (hx₂ : S.IsNilpotentElem x₂) :
    Prop :=
  sorry

/-! ### The Main Theorem (Theorem 5)

For nilpotent G-orbits θ₁, θ₂ of G in its Lie algebra L:

  θ₁ ⊆ cl(θ₂)  ⟺  X(θ₁) ≤ X(θ₂)

where ≤ is the chromosome dominance order (defined in `Chromosome.lean`). -/

/-- **Theorem 5, Necessity** (⟹):
If θ₁ ⊆ cl(θ₂) then X(θ₁) ≤ X(θ₂).
Proved via: rank(x^k) is upper semicontinuous, so
rank(x₁^k) ≤ rank(x₂^k) for all k, which translates to
sig(X(θ₁)^(k)) ≤ sig(X(θ₂)^(k)).
[Originally proved in Djoković 1980 / Hesselink 1976] -/
theorem orbit_closure_implies_dominance
    (x₁ x₂ : S.Elem) (hx₁ : S.IsNilpotentElem x₁) (hx₂ : S.IsNilpotentElem x₂)
    (hcl : orbitClosureContains S x₁ x₂ hx₁ hx₂) :
    orbitChromosome S x₁ hx₁ ≤ orbitChromosome S x₂ hx₂ := by
  sorry

/-- **Theorem 5, Sufficiency** (⟸):
If X(θ₁) ≤ X(θ₂) then θ₁ ⊆ cl(θ₂).

Proof sketch:
1. By Theorem 6 (enough mutations), there is a chain of Φⱼ-mutations
   X(θ₁) = X₀ → X₁ → ⋯ → Xₘ = X(θ₂).
2. For each primitive mutation Xᵢ → Xᵢ₊₁, construct an explicit
   one-parameter family x(t) = x₀ + t·x₁ ∈ L with x(0) ∈ θᵢ
   and x(t) ∈ θᵢ₊₁ for t > 0 (§§9–12).
3. This shows θᵢ ⊆ cl(θᵢ₊₁) for each step, hence θ₁ ⊆ cl(θ₂)
   by transitivity of orbit closure.

The combinatorial step (1) is being formalized in `Mutations.lean`.
The algebraic step (2) is the content of §§9–12, with explicit matrix
constructions for each mutation type (8.1)–(8.17). -/
theorem dominance_implies_orbit_closure
    (x₁ x₂ : S.Elem) (hx₁ : S.IsNilpotentElem x₁) (hx₂ : S.IsNilpotentElem x₂)
    (hdom : orbitChromosome S x₁ hx₁ ≤ orbitChromosome S x₂ hx₂) :
    orbitClosureContains S x₁ x₂ hx₁ hx₂ := by
  sorry

/-- **Theorem 5** (Main Theorem):
θ₁ ⊆ cl(θ₂) if and only if X(θ₁) ≤ X(θ₂). -/
theorem orbit_closure_iff_dominance
    (x₁ x₂ : S.Elem) (hx₁ : S.IsNilpotentElem x₁) (hx₂ : S.IsNilpotentElem x₂) :
    orbitClosureContains S x₁ x₂ hx₁ hx₂ ↔
    orbitChromosome S x₁ hx₁ ≤ orbitChromosome S x₂ hx₂ :=
  ⟨orbit_closure_implies_dominance S x₁ x₂ hx₁ hx₂,
   dominance_implies_orbit_closure S x₁ x₂ hx₁ hx₂⟩

end YoungDiagram.LieAlgebra
