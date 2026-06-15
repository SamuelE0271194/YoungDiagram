import YoungDiagram.Theorem6.MixLambdaPi.Case1
import YoungDiagram.Theorem6.MixLambdaPi.Case3
import YoungDiagram.Theorem6.MixLambdaPi.Drops
import YoungDiagram.Theorem6.MixLambdaPi.SigmaWindow

/-!
# §16 Case A core for `Mix (Lambda, Pi)` (label 1).

This file dispatches the Case A core of §15.10 / §16 on the polarization of the
minimal-rank gene `g₁` of `X`, mirroring `Pi.exists_mutation_le_fifteen_ten_caseA`
in `YoungDiagram/Theorem6/Pi/CaseA.lean`.

Following §16 (Djoković), after the disjoint / sigma-agreement / polarized-pair
reductions (handled by the dispatcher in `MixVarietyJoint`), we let `g₁` be a gene
of minimal rank `m` in `X` and split:

* **Branch A** (`g₁ = g(m)` nonpolarized): paper Cases 1–2 (primitives type4–7);
* **Branch B** (`g₁ = g^±(m)` polarized): paper Cases 3–5 (primitives type6–8).

Each branch propagates a single strict level `a_m < c_m` / `b_m < d_m` across a
window using `cond_15_6/7_Mix_Lambda_Pi` (`Drops.lean`) and the window signature
identities in `SigmaWindow.lean`, half-integer increments handled as in
`half_le_sigma_diff_at_r`.  The two branches are the current formalization
targets.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixLambdaPi

/-- **Branch A** of §16 Case A: the minimal-rank gene `g₁` of `X` is nonpolarized
(`g₁ = g(m)`, so `m` is even).  Paper Cases 1–2. -/
lemma exists_mutation_le_caseA_branchA (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

/-- **Branch B** of §16 Case A: the minimal-rank gene `g₁` of `X` is polarized
(`g₁ = g^±(m)`, so `m` is odd).  Paper Cases 3–5. -/
lemma exists_mutation_le_caseA_branchB (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pol : g₁.type ≠ .NonPolarized) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

/-- §16 Case A core for `Mix (Lambda, Pi)`: extract the minimal-rank gene of `X`
and dispatch on its polarization. -/
lemma exists_mutation_le_caseA (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
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

end MixLambdaPi
