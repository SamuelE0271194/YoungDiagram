import YoungDiagram.Theorem6.MixLambdaPi
import YoungDiagram.Theorem6.MixPiLambda

/-!
# Joint induction for `MixLambdaPi.exists_mutation_le` and
`MixPiLambda.exists_mutation_le`.

The "disjoint supports, some sigma column agrees" sub-case (Case 2) needs an
inductive hypothesis at a smaller rank. After dropping to `prime^[k] X` /
`prime^[k] Y`, the parity of `k` determines which variety the prime-iterate
lands in:

- For `X ∈ Mix (Lambda, Pi)`:
  - even `k`: `prime^[k] X ∈ Mix (Lambda, Pi)` → use the `Mix (Lambda, Pi)` IH.
  - odd `k`:  `prime^[k] X ∈ Mix (Pi, Lambda)` → use the `Mix (Pi, Lambda)` IH.

Symmetrically for `X ∈ Mix (Pi, Lambda)`. So the two `exists_mutation_le`
theorems need a **joint** induction.

This file ports the structure of `Pi.exists_mutation_le_disjoint_sigma_eq`
(in `YoungDiagram/Theorem6/Pi/Prelim.lean`) for the two Mix varieties,
parameterized by both IHs.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixVarietyJoint

/-! ## Case 2 for `Mix (Lambda, Pi)`, even-k branch -/

/-- Even-k branch of Case 2 for `MixLambdaPi`. Drop to `prime^[2j] X`, which
remains in `Mix (Lambda, Pi)`, apply the `Mix (Lambda, Pi)` IH, then lift back
via `MixLambdaPi.mutation_lifting_even`. -/
lemma exists_mutation_le_disjoint_sigma_eq_LP_even (m : ℕ)
    (ihLP : ∀ k, k < m + 2 → ∀ X Y : nMixLambdaPi k, X.1 < Y.1 →
      ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixLambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (k : ℕ) (hkpos : 0 < k) (hkeven : Even k)
    (hYkne : Chromosome.prime^[k] Y.1.1 ≠ 0)
    (hk : Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hle_k : Chromosome.prime^[k] X.1.1 ≤ Chromosome.prime^[k] Y.1.1 := by
    intro j
    simp_rw [← Function.iterate_add_apply]
    exact le_iff_dominates.mp hXY.le (j + k)
  have hdisj_k : ∀ (g' : Gene), 0 < (Chromosome.prime^[k] X.1.1) g' →
      (Chromosome.prime^[k] Y.1.1) g' = 0 := by
    intro g' hg'
    rw [prime_iterate_coeff k X.1.1 g'] at hg'
    rw [prime_iterate_coeff k Y.1.1 g']
    exact Nat.eq_zero_of_le_zero
      (hcommon ⟨g'.rank + k, g'.type, by linarith [g'.rank_pos]⟩ hg')
  -- Drop to the prime-iterate level, which stays inside `Mix (Lambda, Pi)`.
  have hXk_mem : Chromosome.prime^[k] X.1.1 ∈ Mix (Lambda, Pi) := by
    have := Variety.prime_mem_Mix_Lambda_Pi_iterate X.1.2 k
    rwa [if_pos hkeven] at this
  have hYk_mem : Chromosome.prime^[k] Y.1.1 ∈ Mix (Lambda, Pi) := by
    have := Variety.prime_mem_Mix_Lambda_Pi_iterate Y.1.2 k
    rwa [if_pos hkeven] at this
  let Xk : Mix (Lambda, Pi) := ⟨Chromosome.prime^[k] X.1.1, hXk_mem⟩
  let Yk : Mix (Lambda, Pi) := ⟨Chromosome.prime^[k] Y.1.1, hYk_mem⟩
  have hXk_Yk_rank : Xk.1.rank = Yk.1.rank := by
    have h := congr_arg (fun p : ℚ × ℚ => p.1 + p.2) hk
    simp only [Sigma.sigma, signature_sum_eq_rank] at h
    exact_mod_cast h
  have hXk_rank_lt : Xk.1.rank < m + 2 := by
    rw [hXk_Yk_rank, ← Y.2]
    exact prime_iterate_rank_lt_of_ne_zero hkpos hYkne
  have hlt_k : Xk < Yk := by
    change Yk.1.Dominates Xk.1 ∧ ¬Xk.1.Dominates Yk.1
    refine ⟨le_iff_dominates.mp hle_k, fun hcontra => ?_⟩
    have hXkYk_eq : Xk.1 = Yk.1 := le_antisymm hle_k hcontra
    obtain ⟨g', hg'⟩ : ∃ g', 0 < Yk.1 g' := by
      obtain ⟨g', hg'mem⟩ := Finsupp.support_nonempty_iff.mpr hYkne
      exact ⟨g', Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'mem)⟩
    have hXkg' : 0 < Xk.1 g' := by rwa [hXkYk_eq]
    have hYkg'zero := hdisj_k g' hXkg'
    simp only [Yk] at hg'
    omega
  obtain ⟨U, hU_step, hU_le⟩ :
      ∃ U : Mix (Lambda, Pi), MixLambdaPi.Step Xk U ∧ U ≤ Yk :=
    ihLP Xk.1.rank hXk_rank_lt ⟨Xk, rfl⟩ ⟨Yk, hXk_Yk_rank.symm⟩ hlt_k
  obtain ⟨Z, hZ, hZ_step, hZ_prime, hZ_sig⟩ :=
    MixLambdaPi.mutation_lifting_even X.1.2 U.2 hkeven hU_step
  refine ⟨⟨Z, hZ⟩, hZ_step, ?_⟩
  change Z ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  by_cases hjk : j ≤ k
  · rw [← hZ_sig j hjk]
    exact le_iff_dominates.mp hXY.le j
  · push_neg at hjk
    have hj_eq : j = (j - k) + k := (Nat.sub_add_cancel hjk.le).symm
    conv_lhs => rw [hj_eq, Function.iterate_add_apply, hZ_prime]
    have hUYk : signature (Chromosome.prime^[j - k] U.1) ≤
        signature (Chromosome.prime^[j - k] Yk.1) :=
      le_iff_dominates.mp hU_le (j - k)
    have : signature (Chromosome.prime^[j - k] Yk.1) =
        signature (Chromosome.prime^[j] Y.1.1) := by
      simp only [Yk, ← Function.iterate_add_apply, Nat.sub_add_cancel hjk.le]
    rw [this] at hUYk
    exact hUYk

/-! ## Case 2 for `Mix (Pi, Lambda)`, even-k branch -/

/-- Even-k branch of Case 2 for `MixPiLambda`. Drop to `prime^[2j] X`, which
remains in `Mix (Pi, Lambda)`, apply the `Mix (Pi, Lambda)` IH, then lift back
via `MixPiLambda.mutation_lifting_even`. -/
lemma exists_mutation_le_disjoint_sigma_eq_PL_even (m : ℕ)
    (ihPL : ∀ k, k < m + 2 → ∀ X Y : nMixPiLambda k, X.1 < Y.1 →
      ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixPiLambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (k : ℕ) (hkpos : 0 < k) (hkeven : Even k)
    (hYkne : Chromosome.prime^[k] Y.1.1 ≠ 0)
    (hk : Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hle_k : Chromosome.prime^[k] X.1.1 ≤ Chromosome.prime^[k] Y.1.1 := by
    intro j
    simp_rw [← Function.iterate_add_apply]
    exact le_iff_dominates.mp hXY.le (j + k)
  have hdisj_k : ∀ (g' : Gene), 0 < (Chromosome.prime^[k] X.1.1) g' →
      (Chromosome.prime^[k] Y.1.1) g' = 0 := by
    intro g' hg'
    rw [prime_iterate_coeff k X.1.1 g'] at hg'
    rw [prime_iterate_coeff k Y.1.1 g']
    exact Nat.eq_zero_of_le_zero
      (hcommon ⟨g'.rank + k, g'.type, by linarith [g'.rank_pos]⟩ hg')
  -- Drop to the prime-iterate level, which stays inside `Mix (Pi, Lambda)`.
  have hXk_mem : Chromosome.prime^[k] X.1.1 ∈ Mix (Pi, Lambda) := by
    have := Variety.prime_mem_Mix_Pi_Lambda_iterate X.1.2 k
    rwa [if_pos hkeven] at this
  have hYk_mem : Chromosome.prime^[k] Y.1.1 ∈ Mix (Pi, Lambda) := by
    have := Variety.prime_mem_Mix_Pi_Lambda_iterate Y.1.2 k
    rwa [if_pos hkeven] at this
  let Xk : Mix (Pi, Lambda) := ⟨Chromosome.prime^[k] X.1.1, hXk_mem⟩
  let Yk : Mix (Pi, Lambda) := ⟨Chromosome.prime^[k] Y.1.1, hYk_mem⟩
  have hXk_Yk_rank : Xk.1.rank = Yk.1.rank := by
    have h := congr_arg (fun p : ℚ × ℚ => p.1 + p.2) hk
    simp only [Sigma.sigma, signature_sum_eq_rank] at h
    exact_mod_cast h
  have hXk_rank_lt : Xk.1.rank < m + 2 := by
    rw [hXk_Yk_rank, ← Y.2]
    exact prime_iterate_rank_lt_of_ne_zero hkpos hYkne
  have hlt_k : Xk < Yk := by
    change Yk.1.Dominates Xk.1 ∧ ¬Xk.1.Dominates Yk.1
    refine ⟨le_iff_dominates.mp hle_k, fun hcontra => ?_⟩
    have hXkYk_eq : Xk.1 = Yk.1 := le_antisymm hle_k hcontra
    obtain ⟨g', hg'⟩ : ∃ g', 0 < Yk.1 g' := by
      obtain ⟨g', hg'mem⟩ := Finsupp.support_nonempty_iff.mpr hYkne
      exact ⟨g', Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'mem)⟩
    have hXkg' : 0 < Xk.1 g' := by rwa [hXkYk_eq]
    have hYkg'zero := hdisj_k g' hXkg'
    simp only [Yk] at hg'
    omega
  obtain ⟨U, hU_step, hU_le⟩ :
      ∃ U : Mix (Pi, Lambda), MixPiLambda.Step Xk U ∧ U ≤ Yk :=
    ihPL Xk.1.rank hXk_rank_lt ⟨Xk, rfl⟩ ⟨Yk, hXk_Yk_rank.symm⟩ hlt_k
  obtain ⟨Z, hZ, hZ_step, hZ_prime, hZ_sig⟩ :=
    MixPiLambda.mutation_lifting_even X.1.2 U.2 hkeven hU_step
  refine ⟨⟨Z, hZ⟩, hZ_step, ?_⟩
  change Z ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  by_cases hjk : j ≤ k
  · rw [← hZ_sig j hjk]
    exact le_iff_dominates.mp hXY.le j
  · push_neg at hjk
    have hj_eq : j = (j - k) + k := (Nat.sub_add_cancel hjk.le).symm
    conv_lhs => rw [hj_eq, Function.iterate_add_apply, hZ_prime]
    have hUYk : signature (Chromosome.prime^[j - k] U.1) ≤
        signature (Chromosome.prime^[j - k] Yk.1) :=
      le_iff_dominates.mp hU_le (j - k)
    have : signature (Chromosome.prime^[j - k] Yk.1) =
        signature (Chromosome.prime^[j] Y.1.1) := by
      simp only [Yk, ← Function.iterate_add_apply, Nat.sub_add_cancel hjk.le]
    rw [this] at hUYk
    exact hUYk

end MixVarietyJoint
