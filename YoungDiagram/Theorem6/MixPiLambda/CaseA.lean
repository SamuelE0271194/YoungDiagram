import YoungDiagram.Theorem6.MixPiLambda.Case1
import YoungDiagram.Theorem6.MixPiLambda.Case3

/-!
# §16 Case A core for `Mix (Pi, Lambda)` (label 2).

Symmetric to `MixLambdaPi/CaseA.lean`: dispatch the Case A core on the
polarization of the minimal-rank gene `g₁` of `X`.  For `Mix (Pi, Lambda)` the
even/odd parity roles are swapped (nonpolarized genes sit at odd rank), and level
`1` is the asymmetric (integer) level, so the global Case A hypothesis
`a_X(1) < a_Y(1)` already fixes the deficient charge.

* **Branch A** (`g₁` nonpolarized): paper Cases 1–2;
* **Branch B** (`g₁` polarized): paper Cases 3–5.

Both branches are the current formalization targets.  The propagation machinery
(half-integer drop inequalities and window signature identities, analogous to
`MixLambdaPi/Drops.lean` and `MixLambdaPi/SigmaWindow.lean`) is still to be ported
for this variety.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- **Branch A** of §16 Case A for `Mix (Pi, Lambda)`: minimal-rank gene `g₁`
nonpolarized.  Paper Cases 1–2. -/
lemma exists_mutation_le_caseA_branchA (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

/-- **Branch B** of §16 Case A for `Mix (Pi, Lambda)`: minimal-rank gene `g₁`
polarized.  Paper Cases 3–5. -/
lemma exists_mutation_le_caseA_branchB (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pol : g₁.type ≠ .NonPolarized) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

/-- §16 Case A core for `Mix (Pi, Lambda)`: extract the minimal-rank gene of `X`
and dispatch on its polarization. -/
lemma exists_mutation_le_caseA (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXne : X.1.1 ≠ 0 := by
    intro h
    have hr0 : X.1.1.rank = 0 := rank_zero_iff.mpr h
    have hr : X.1.1.rank = m + 2 := X.2
    omega
  obtain ⟨g₁, hg₁mem, hg₁min⟩ := Finset.exists_min_image X.1.1.support Gene.rank
    (Finsupp.support_nonempty_iff.mpr hXne)
  rw [Finsupp.mem_support_iff] at hg₁mem
  have hXg₁ : 0 < X.1.1 g₁ := Nat.pos_of_ne_zero hg₁mem
  by_cases hpol : g₁.type = .NonPolarized
  · exact exists_mutation_le_caseA_branchA m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁
      hg₁min hpol
  · exact exists_mutation_le_caseA_branchB m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁
      hg₁min hpol

end MixPiLambda
