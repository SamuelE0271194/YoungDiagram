import YoungDiagram.Theorem6.Mix2LambdaPi.Case1
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34
import YoungDiagram.Theorem6.MixPi2Lambda.Case1
import YoungDiagram.Theorem6.MixPi2Lambda.Case34

/-!
# Joint induction for Labels 3 and 4

An odd prime iterate exchanges `Mix (2 • Lambda, Pi)` and
`Mix (Pi, 2 • Lambda)`.  Thus the sigma-agreement reduction preceding
equation (17.1) requires the two inductive hypotheses simultaneously.
-/

open Variety hiding prime prime_def
open Chromosome
open Pointwise

namespace Mix2LambdaJoint

private lemma exists_mutation_le_disjoint_sigma_eq_aux
    {V W : Variety}
    (StepV : V → V → Prop) (StepW : W → W → Prop)
    {N k : ℕ}
    (ihW : ∀ r, r < N → ∀ A B : {T : W // T.1.rank = r}, A.1.1 < B.1.1 →
      ∃ U : W, StepW A.1 U ∧ U.1 ≤ B.1.1)
    (X Y : {T : V // T.1.rank = N})
    (hXY : X.1.1 < Y.1.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (hkpos : 0 < k)
    (hYkne : Chromosome.prime^[k] Y.1.1 ≠ 0)
    (hsig : Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXk_mem : Chromosome.prime^[k] X.1.1 ∈ W)
    (hYk_mem : Chromosome.prime^[k] Y.1.1 ∈ W)
    (eq_of_bile : ∀ A B : W, A.1 ≤ B.1 → B.1 ≤ A.1 → A.1 = B.1)
    (liftStep :
      ∀ {U : Chromosome} (hU : U ∈ W),
        StepW
          ⟨Chromosome.prime^[k] X.1.1, hXk_mem⟩
          ⟨U, hU⟩ →
        ∃ (Z : Chromosome) (hZ : Z ∈ V),
          StepV X.1 ⟨Z, hZ⟩ ∧
          Chromosome.prime^[k] Z = U ∧
          ∀ i ≤ k, signature (Chromosome.prime^[i] X.1.1) =
            signature (Chromosome.prime^[i] Z)) :
    ∃ Z : V, StepV X.1 Z ∧ Z.1 ≤ Y.1.1 := by
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
  let Xk : W := ⟨Chromosome.prime^[k] X.1.1, hXk_mem⟩
  let Yk : W := ⟨Chromosome.prime^[k] Y.1.1, hYk_mem⟩
  have hXk_Yk_rank : Xk.1.rank = Yk.1.rank := by
    have h := congr_arg (fun p : ℚ × ℚ => p.1 + p.2) hsig
    simp only [Sigma.sigma, signature_sum_eq_rank] at h
    exact_mod_cast h
  have hXk_rank_lt : Xk.1.rank < N := by
    rw [hXk_Yk_rank, ← Y.2]
    exact prime_iterate_rank_lt_of_ne_zero hkpos hYkne
  have hlt_k : Xk.1 < Yk.1 := by
    change (Chromosome.prime^[k] Y.1.1).Dominates
        (Chromosome.prime^[k] X.1.1) ∧
      ¬(Chromosome.prime^[k] X.1.1).Dominates
        (Chromosome.prime^[k] Y.1.1)
    refine ⟨le_iff_dominates.mp hle_k, fun hcontra => ?_⟩
    have hXkYk_eq : Chromosome.prime^[k] X.1.1 =
        Chromosome.prime^[k] Y.1.1 := eq_of_bile Xk Yk hle_k hcontra
    obtain ⟨g', hg'⟩ : ∃ g', 0 < Yk.1 g' := by
      obtain ⟨g', hg'mem⟩ := Finsupp.support_nonempty_iff.mpr hYkne
      exact ⟨g', Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'mem)⟩
    have hXkg' : 0 < (Chromosome.prime^[k] X.1.1) g' := by
      rwa [hXkYk_eq]
    have hYkg'zero := hdisj_k g' hXkg'
    simp only [Yk] at hg'
    omega
  obtain ⟨U, hU_step, hU_le⟩ :=
    ihW Xk.1.rank hXk_rank_lt
      ⟨Xk, rfl⟩ ⟨Yk, hXk_Yk_rank.symm⟩ hlt_k
  obtain ⟨Z, hZ, hZ_step, hZ_prime, hZ_sig⟩ :=
    liftStep U.2 hU_step
  refine ⟨⟨Z, hZ⟩, hZ_step, ?_⟩
  change Z ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  by_cases hjk : j ≤ k
  · rw [← hZ_sig j hjk]
    exact le_iff_dominates.mp hXY.le j
  · push Not at hjk
    have hj_eq : j = (j - k) + k := (Nat.sub_add_cancel hjk.le).symm
    conv_lhs => rw [hj_eq, Function.iterate_add_apply, hZ_prime]
    have hUYk : signature (Chromosome.prime^[j - k] U.1) ≤
        signature (Chromosome.prime^[j - k] Yk.1) :=
      le_iff_dominates.mp hU_le (j - k)
    have hYk_eq : signature (Chromosome.prime^[j - k] Yk.1) =
        signature (Chromosome.prime^[j] Y.1.1) := by
      simp only [Yk, ← Function.iterate_add_apply, Nat.sub_add_cancel hjk.le]
    rwa [hYk_eq] at hUYk

lemma exists_mutation_le_disjoint_sigma_eq_L3 (m : ℕ)
    (ih3 : ∀ r, r < m + 2 → ∀ X Y : nMix2LambdaPi r, X.1 < Y.1 →
      ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (ih4 : ∀ r, r < m + 2 → ∀ X Y : nMixPi2Lambda r, X.1 < Y.1 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (hsigeq : ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨k, hkpos, hYkne, hsig⟩ := hsigeq
  by_cases hk : Even k
  · have hXk := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 k
    have hYk := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 k
    rw [if_pos hk] at hXk hYk
    exact exists_mutation_le_disjoint_sigma_eq_aux
      Mix2LambdaPi.Step Mix2LambdaPi.Step ih3 X Y hXY hcommon hkpos hYkne hsig
      hXk hYk (fun A B hAB hBA =>
        Subtype.val_inj.2 (le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA)))
      (fun hU hstep =>
        Mix2LambdaPi.mutation_lifting_even X.1.2 hU hk hstep)
  · have hXk := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 k
    have hYk := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 k
    rw [if_neg hk] at hXk hYk
    exact exists_mutation_le_disjoint_sigma_eq_aux
      Mix2LambdaPi.Step MixPi2Lambda.Step ih4 X Y hXY hcommon hkpos hYkne hsig
      hXk hYk (fun A B hAB hBA =>
        Subtype.val_inj.2 (le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA)))
      (fun hU hstep =>
        Mix2LambdaPi.mutation_lifting_odd X.1.2 hU hk hstep)

lemma exists_mutation_le_disjoint_sigma_eq_L4 (m : ℕ)
    (ih3 : ∀ r, r < m + 2 → ∀ X Y : nMix2LambdaPi r, X.1 < Y.1 →
      ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (ih4 : ∀ r, r < m + 2 → ∀ X Y : nMixPi2Lambda r, X.1 < Y.1 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (hsigeq : ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨k, hkpos, hYkne, hsig⟩ := hsigeq
  by_cases hk : Even k
  · have hXk := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 k
    have hYk := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 k
    rw [if_pos hk] at hXk hYk
    exact exists_mutation_le_disjoint_sigma_eq_aux
      MixPi2Lambda.Step MixPi2Lambda.Step ih4 X Y hXY hcommon hkpos hYkne hsig
      hXk hYk (fun A B hAB hBA =>
        Subtype.val_inj.2 (le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA)))
      (fun hU hstep =>
        MixPi2Lambda.mutation_lifting_even X.1.2 hU hk hstep)
  · have hXk := Variety.prime_mem_Mix_Pi_2Lambda_iterate X.1.2 k
    have hYk := Variety.prime_mem_Mix_Pi_2Lambda_iterate Y.1.2 k
    rw [if_neg hk] at hXk hYk
    exact exists_mutation_le_disjoint_sigma_eq_aux
      MixPi2Lambda.Step Mix2LambdaPi.Step ih3 X Y hXY hcommon hkpos hYkne hsig
      hXk hYk (fun A B hAB hBA =>
        Subtype.val_inj.2 (le_antisymm (show A ≤ B from hAB) (show B ≤ A from hBA)))
      (fun hU hstep =>
        MixPi2Lambda.mutation_lifting_odd X.1.2 hU hk hstep)

private lemma exists_mutation_le_joint_L3_aux (n : ℕ)
    (ih : ∀ r, r < n →
      (∀ X Y : nMix2LambdaPi r, X.1 < Y.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∧
      (∀ X Y : nMixPi2Lambda r, X.1 < Y.1 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1))
    (X Y : nMix2LambdaPi n) (hXY : X.1 < Y.1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  match n, X, Y, hXY with
  | 0, X, Y, hXY => exact Mix2LambdaPi.exists_mutation_le_rank_zero hXY
  | 1, X, Y, hXY => exact Mix2LambdaPi.exists_mutation_le_rank_one hXY
  | m + 2, X, Y, hXY =>
    have ih3 := fun r hr => (ih r hr).1
    have ih4 := fun r hr => (ih r hr).2
    by_cases hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g
    · exact Mix2LambdaPi.exists_mutation_le_shared_gene m ih3 X Y hXY hcommon
    · push Not at hcommon
      by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
          Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k
      · exact exists_mutation_le_disjoint_sigma_eq_L3 m ih3 ih4 X Y hXY hcommon hsigeq
      · exact Mix2LambdaPi.exists_mutation_le_reduced m X Y hXY (by
          push Not
          exact hcommon) hsigeq

private lemma exists_mutation_le_joint_L4_aux (n : ℕ)
    (ih : ∀ r, r < n →
      (∀ X Y : nMix2LambdaPi r, X.1 < Y.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∧
      (∀ X Y : nMixPi2Lambda r, X.1 < Y.1 →
        ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1))
    (X Y : nMixPi2Lambda n) (hXY : X.1 < Y.1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  match n, X, Y, hXY with
  | 0, X, Y, hXY => exact MixPi2Lambda.exists_mutation_le_rank_zero hXY
  | 1, X, Y, hXY => exact MixPi2Lambda.exists_mutation_le_rank_one hXY
  | m + 2, X, Y, hXY =>
    have ih3 := fun r hr => (ih r hr).1
    have ih4 := fun r hr => (ih r hr).2
    by_cases hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g
    · exact MixPi2Lambda.exists_mutation_le_shared_gene m ih4 X Y hXY hcommon
    · push Not at hcommon
      by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
          Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k
      · exact exists_mutation_le_disjoint_sigma_eq_L4 m ih3 ih4 X Y hXY hcommon hsigeq
      · exact MixPi2Lambda.exists_mutation_le_reduced m X Y hXY (by
          push Not
          exact hcommon) hsigeq

theorem exists_mutation_le_joint (n : ℕ) :
    (∀ X Y : nMix2LambdaPi n, X.1 < Y.1 →
      ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∧
    (∀ X Y : nMixPi2Lambda n, X.1 < Y.1 →
      ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1) :=
  Nat.strongRecOn n fun n ih =>
    ⟨exists_mutation_le_joint_L3_aux n ih,
     exists_mutation_le_joint_L4_aux n ih⟩

end Mix2LambdaJoint
