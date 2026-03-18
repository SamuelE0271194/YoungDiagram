import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Data.Complex.Basic
import YoungDiagram.NilpotentOrbit

/-!
# Classical Lie Algebras for Each Series

For each series index j, the classical group G preserves a nondegenerate
form f on a finite-dimensional F-vector space V. The Lie algebra L of G
consists of the f-skew-adjoint endomorphisms of V:

  L = {x ∈ End_F(V) : f(xv, w) + f(v, xw) = 0  ∀ v, w ∈ V}

This file establishes the connection between the abstract `SeriesIndex`
from `NilpotentOrbit.lean` and mathlib's Lie algebra infrastructure.

## Mathlib connections

| Series | F | Form          | Mathlib Lie algebra                          |
|--------|---|---------------|----------------------------------------------|
| j = 6  | ℝ | symmetric     | `skewAdjointLieSubalgebra B` (B symmetric)   |
| j = 9  | ℝ | skew-symmetric| `skewAdjointLieSubalgebra B` (B skew-sym.)   |
| j = 4  | ℂ | hermitian     | TODO: sesquilinear `skewAdjoint` analogue    |
| j = 7  | ℍ | skew-hermitian| TODO: quaternionic module theory              |
| j = 10 | ℍ | hermitian     | TODO: quaternionic module theory              |

## References

* [Djoković 1982, §1 Table I, §2]
-/

namespace YoungDiagram.LieAlgebra

/-! ### The Lie algebra of a bilinear form

For j = 6 (symmetric bilinear form over ℝ) and j = 9 (skew-symmetric
bilinear form over ℝ), the Lie algebra L is directly
`skewAdjointLieSubalgebra B` from mathlib.

Recall: `skewAdjointLieSubalgebra B` consists of those `f : End R M` satisfying
`B (f v) w + B v (f w) = 0` for all `v, w`. -/

section BilinearForm

variable (R : Type*) [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The Lie algebra of the classical group preserving a bilinear form B.
This is `{x ∈ End(V) | B(xv, w) + B(v, xw) = 0 ∀ v, w}`. -/
def lieAlgebraOfBilinForm (B : LinearMap.BilinForm R V) :
    LieSubalgebra R (Module.End R V) :=
  skewAdjointLieSubalgebra B

/-- An element x of `lieAlgebraOfBilinForm B` is nilpotent when it is
nilpotent as an endomorphism of V. -/
def lieAlgebraOfBilinForm.IsNilpotent (B : LinearMap.BilinForm R V)
    (x : lieAlgebraOfBilinForm R B) : Prop :=
  _root_.IsNilpotent (x.val : Module.End R V)

end BilinearForm

/-! ### Sesquilinear form case (j = 4)

For G = U(p,q), the Lie algebra consists of endomorphisms x satisfying
  H(xv, w) + H(v, xw) = 0
where H is a nondegenerate hermitian form on a ℂ-vector space V.

Mathlib has sesquilinear maps but does not yet provide
`skewAdjointLieSubalgebra` for sesquilinear forms.
We define the Lie algebra as `sorry` for now. -/

section Hermitian
--
-- For G = U(p,q), the Lie algebra is the set of skew-hermitian endomorphisms.
-- To define `LieSubalgebra ℂ (Module.End ℂ V)` we need `Algebra ℂ (Module.End ℂ V)`
-- which requires `SMulCommClass ℂ ℂ V`. This holds for concrete V but
-- is not automatic for abstract V. We defer this to concrete instantiation.
--
-- TODO: `def lieAlgebra_U (H : SesquilinearForm ℂ V) : LieSubalgebra ℂ (Module.End ℂ V)`

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

instance : IsScalarTower ℂ ℂ V := IsScalarTower.left ℂ

instance : LieAlgebra ℂ (Module.End ℂ V) :=
  LieAlgebra.ofAssociativeAlgebra

noncomputable def lieAlgebra_U : LieSubalgebra ℂ (Module.End ℂ V) := sorry

end Hermitian

/-! ### Quaternionic cases (j = 7, j = 10)

For G = O*(2n) (j = 7) and G = Sp(p,q) (j = 10), the underlying vector
space is over the quaternions ℍ = `Quaternion ℝ`.

Mathlib provides `Quaternion ℝ` as a type, but the module theory over
non-commutative division rings is not yet developed. These cases are
deferred to future work. -/

-- Future: `lieAlgebra_Ostar` and `lieAlgebra_SpH`

/-! ### Unified interface

We package the Lie algebra data for each series into a single structure
that `JordanBlock.lean` and `OrbitClosure.lean` can depend on. -/

/-- The algebraic data of a classical Lie algebra of series j.
Bundles a commutative field F, a finite-dimensional F-vector space V,
the Lie subalgebra L ⊆ End_F(V), and the form signature sig(f).

Note: For the quaternionic series (j = 7, 10), F should be ℍ (a division
ring, not a field). We use `Field` as a temporary placeholder. -/
structure ClassicalSetup (j : SeriesIndex) where
  /-- The base field -/
  F : Type*
  /-- The vector space -/
  V : Type*
  [instField : Field F]
  [instACG : AddCommGroup V]
  [instMod : Module F V]
  [instFD : FiniteDimensional F V]
  /-- The Lie algebra L ⊆ End_F(V) -/
  L : LieSubalgebra F (Module.End F V)
  /-- The form signature sig(f) = (p, q) from Table I -/
  formSig : ℚ × ℚ
  formSig_nonneg : 0 ≤ formSig.1 ∧ 0 ≤ formSig.2

namespace ClassicalSetup

variable {j : SeriesIndex} (S : ClassicalSetup j)

-- Register the bundled instances for use within proofs.
instance : Field S.F := S.instField
instance : AddCommGroup S.V := S.instACG
instance : Module S.F S.V := S.instMod
instance : FiniteDimensional S.F S.V := S.instFD

/-- The F-dimension of V. -/
noncomputable def dim : ℕ := Module.finrank S.F S.V

/-- An element of the Lie algebra, viewed as an endomorphism of V. -/
abbrev Elem := S.L

/-- An element x ∈ L is nilpotent (as an endomorphism of V). -/
def IsNilpotentElem (x : S.Elem) : Prop :=
  IsNilpotent (x.val : Module.End S.F S.V)

/-- The set of nilpotent elements in L. -/
def nilpotentSet : Set S.Elem :=
  {x | S.IsNilpotentElem x}

/-- Zero is nilpotent. -/
lemma zero_mem_nilpotentSet : (0 : S.Elem) ∈ S.nilpotentSet := by
  exact ⟨1, by simp⟩

end ClassicalSetup

/-! ### Concrete instances (sorry'd)

Each series j determines a specific classical group and form type.
The full construction requires:
- j = 4: hermitian form over ℂ → `lieAlgebra_U`
- j = 6: symmetric bilinear form over ℝ → `lieAlgebraOfBilinForm`
- j = 7: skew-hermitian form over ℍ → TODO
- j = 9: skew-symmetric bilinear form over ℝ → `lieAlgebraOfBilinForm`
- j = 10: hermitian form over ℍ → TODO

For now we provide sorry'd existence statements. -/

/-- A form signature is admissible for series j when it satisfies the
constraints from Table I (§1) and §7:
- j = 4, 6, 10: sig(f) = (k, n−k) where k, n−k ∈ ℕ with k + (n−k) ≥ 1
- j = 7, 9: sig(f) = (n/2, n/2) where n ≥ 1 (p.227: "When j = 7 or 9
  we have sig(f) = (n/2, n/2)") -/
def ClassicalSetup.IsAdmissibleSig (j : SeriesIndex) (sig : ℚ × ℚ) : Prop :=
  0 < sig.1 + sig.2 ∧
  match j with
  | .U | .O | .SpH => ∃ p q : ℕ, sig = (↑p, ↑q)
  | .Ostar | .SpR  => ∃ n : ℕ, sig = ((n : ℚ) / 2, (n : ℚ) / 2)

/-- Every admissible form signature admits a classical setup of the given series. -/
theorem ClassicalSetup.exists (j : SeriesIndex) (sig : ℚ × ℚ)
    (hsig : ClassicalSetup.IsAdmissibleSig j sig) :
    ∃ S : ClassicalSetup j, S.formSig = sig := by
  sorry

end YoungDiagram.LieAlgebra
