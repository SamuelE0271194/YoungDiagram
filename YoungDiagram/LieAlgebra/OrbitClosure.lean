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

* `adjointAction`: The adjoint action of G on L.
* `NilpotentOrbit`: The quotient type of nilpotent orbits (equivalence classes). [§7]
* `orbitChromosome`: The chromosome X(x) of a nilpotent element (on representatives).
* `orbitChromosomeQuot`: The chromosome X(θ) lifted to orbits. [§7 Lemma 4]
* `chromosomeSet`: The target set {X ∈ Φⱼ | sig(X) = sig(f)}. [§7 Lemma 4]

## Main results (sorry'd)

* `extractNilpotentType_orbit_invariant`: Nilpotent type is constant on orbits.
* `lemma4_chromosome_bijection`: θ ↦ X(θ) is a bijection onto chromosomeSet. [§7 Lemma 4]
* `orbit_closure_iff_dominance`: Theorem 5 — orbit closure ↔ chromosome dominance. [§7]

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

* [Djoković 1982, §7 Lemma 4, §7 Theorem 5, §§9–12]
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

/-! ### The adjoint action as a MulAction

We equip the Lie algebra elements and the nilpotent set with a group action
by the classical group, using mathlib's `MulAction` infrastructure.
This gives us `MulAction.orbitRel` and `MulAction.orbitRel.Quotient` for free. -/

/-- The conjugation action of G on L: g • x = Ad(g)(x) = g·x·g⁻¹. -/
noncomputable instance adjointSMul : SMul (classicalGroup S) S.Elem where
  smul g x := adjointAction S g x

/-- The adjoint action is a group action. -/
noncomputable instance adjointMulAction : MulAction (classicalGroup S) S.Elem where
  one_smul := sorry
  mul_smul := sorry

/-- The adjoint action restricts to nilpotent elements. -/
noncomputable instance nilpotentSMul : SMul (classicalGroup S) S.nilpotentSet where
  smul g p := ⟨g • p.1, adjointAction_preserves_nilpotent S g p.1 p.2⟩

/-- The restricted action on nilpotent elements is a group action. -/
noncomputable instance nilpotentMulAction :
    MulAction (classicalGroup S) S.nilpotentSet where
  one_smul := sorry
  mul_smul := sorry

/-! ### Nilpotent orbits

Using mathlib's `MulAction.orbitRel.Quotient`, the orbit equivalence relation
and quotient type come for free from the group action. -/

/-- The nilpotent type is constant on G-orbits:
if y = g • x then Δ(y) = Δ(x). -/
theorem extractNilpotentType_orbit_invariant
    (x : S.Elem) (hx : S.IsNilpotentElem x)
    (g : classicalGroup S) :
    extractNilpotentType S (g • x)
      (adjointAction_preserves_nilpotent S g x hx) =
    extractNilpotentType S x hx := by
  sorry

/-- The chromosome X(θ) of a nilpotent orbit θ.
Well-defined by `extractNilpotentType_orbit_invariant`. -/
noncomputable def orbitChromosome
    (x : S.Elem) (hx : S.IsNilpotentElem x) : Chromosome :=
  (extractNilpotentType S x hx).toChromosome

/-- The chromosome of an orbit is well-defined (independent of representative).
This combines `extractNilpotentType_orbit_invariant` with `toChromosome`. -/
theorem orbitChromosome_eq_of_smul
    (x : S.Elem) (hx : S.IsNilpotentElem x)
    (g : classicalGroup S) :
    orbitChromosome S (g • x)
      (adjointAction_preserves_nilpotent S g x hx) =
    orbitChromosome S x hx := by
  simp only [orbitChromosome]
  rw [extractNilpotentType_orbit_invariant S x hx g]

/-- The set of nilpotent G-orbits in L, using mathlib's orbit quotient. [§7]
Each element of this type is an equivalence class θ = G · x. -/
noncomputable abbrev NilpotentOrbit :=
  MulAction.orbitRel.Quotient (classicalGroup S) S.nilpotentSet

/-- The chromosome map X(θ) lifted to orbits (equivalence classes).
Well-defined by `orbitChromosome_eq_of_smul`. [§7 Lemma 4] -/
noncomputable def orbitChromosomeQuot : NilpotentOrbit S → Chromosome :=
  Quotient.lift
    (fun (p : S.nilpotentSet) => orbitChromosome S p.1 p.2)
    (fun a b h => by
      -- h : a ∈ MulAction.orbit (classicalGroup S) b, i.e. ∃ g, g • b = a
      -- The proof uses orbitChromosome_eq_of_smul and the fact that
      -- conjugate elements have the same nilpotent type.
      sorry)

/-! ### The target set of Lemma 4

The chromosome bijection lands in {X ∈ Φⱼ | sig(X) = sig(f)}. -/

/-- The set of chromosomes with the right variety and signature. [§7 Lemma 4]
This is the codomain of the chromosome bijection. -/
def chromosomeSet : Set Chromosome :=
  {X : Chromosome | X ∈ j.variety ∧ X.signature = S.formSig}

/-- The chromosome of any orbit lands in `chromosomeSet`. -/
theorem orbitChromosome_mem_chromosomeSet
    (x : S.Elem) (hx : S.IsNilpotentElem x) :
    orbitChromosome S x hx ∈ chromosomeSet S := by
  exact ⟨extractNilpotentType_mem_variety S x hx,
         extractNilpotentType_signature S x hx⟩

/-! ### Lemma 4: The Chromosome Bijection [§7 Lemma 4]

The map θ ↦ X(θ) is a bijection from `NilpotentOrbit S` onto `chromosomeSet S`.

The proof assembles four components:
- **Well-definedness**: `orbitChromosome_eq_of_orbit` (orbit invariance)
- **Image containment**: `orbitChromosome_mem_chromosomeSet`
- **Injectivity**: `toChromosome_injective` (combinatorial, NilpotentOrbit.lean) +
  `extractNilpotentType_orbit_invariant` (elements with same type are in same orbit)
- **Surjectivity**: `toChromosome_surjective` (combinatorial, NilpotentOrbit.lean) +
  `realizeNilpotentType` (every valid type is realized, JordanBlock.lean)
-/

/-- **[§7 Lemma 4]** The chromosome map θ ↦ X(θ) is an equivalence
from the set of nilpotent G-orbits in L to {X ∈ Φⱼ | sig(X) = sig(f)}.

This packages the full content of Lemma 4 as an `Equiv`:
- `chromosomeBijection.toFun`: orbit → chromosome (via `orbitChromosomeQuot`)
- `chromosomeBijection.invFun`: chromosome → orbit (realizability, §5)
- `chromosomeBijection.left_inv` / `right_inv`: the two directions cancel -/
noncomputable def chromosomeBijection :
    NilpotentOrbit S ≃ chromosomeSet S := by
  sorry

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
