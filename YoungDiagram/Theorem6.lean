import YoungDiagram.Theorem6.CaseA
import YoungDiagram.Theorem6.Dual

open Variety hiding prime prime_def
open Chromosome

/-! ## (15.10): X has no positive-negative gene pair of equal rank -/
/-- Dispatcher for Cases A and B of §15.10.
Case A is proved in `YoungDiagram.Theorem6.CaseA`; Case B is its sign-dual. -/
private lemma exists_mutation_le_fifteen_ten (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X.1 k = Sigma.sigma Y.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1
  · exact exists_mutation_le_fifteen_ten_caseA m ih X Y hXY hcommon hsigeq hXpn ha
  · have ha_le : (Sigma.sigma X.1 1).1 ≤ (Sigma.sigma Y.1 1).1 :=
      (le_iff_dominates.mp hXY.le 1).1
    have ha_eq : (Sigma.sigma X.1 1).1 = (Sigma.sigma Y.1 1).1 :=
      le_antisymm ha_le (le_of_not_gt ha)
    have hYprime_ne : prime^[1] Y.1.val ≠ 0 := by
      intro hYprime
      have hXprime_zero : prime^[1] X.1.val = 0 := by
        have hle1 := le_iff_dominates.mp hXY.le 1
        simp only [hYprime, map_zero] at hle1
        exact signature_eq_zero (le_antisymm hle1 (signature_nonneg _))
      have hsig_all : ∀ k,
          signature (prime^[k] X.1.val) = signature (prime^[k] Y.1.val) := by
        have hXprime : prime X.1.val = 0 := by simpa using hXprime_zero
        have hYprime' : prime Y.1.val = 0 := by simpa using hYprime
        intro k
        cases k with
        | zero =>
            simpa only [Sigma.sigma, Function.iterate_zero, id_eq] using
              sigma_zero_eq X Y hXY.le
        | succ k =>
            simp [Function.iterate_succ_apply, hXprime, hYprime']
      have hXYeq : X.1.val = Y.1.val :=
        eq_of_sigma_eq X.1.2 Y.1.2 hsig_all
      exact (ne_of_lt hXY) (Subtype.val_injective hXYeq)
    have hsig_ne : Sigma.sigma X.1 1 ≠ Sigma.sigma Y.1 1 := by
      intro hsig
      exact hsigeq ⟨1, by norm_num, hYprime_ne, hsig⟩
    have hb_le : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
      (le_iff_dominates.mp hXY.le 1).2
    have hb_ne : (Sigma.sigma X.1 1).2 ≠ (Sigma.sigma Y.1 1).2 := by
      intro hb_eq
      exact hsig_ne (Prod.ext ha_eq hb_eq)
    have hb_lt : (Sigma.sigma X.1 1).2 < (Sigma.sigma Y.1 1).2 :=
      lt_of_le_of_ne hb_le hb_ne
    let Xd : nPi (m + 2) :=
      ⟨Pi.dual X.1, by simpa [Pi.dual] using X.2⟩
    let Yd : nPi (m + 2) :=
      ⟨Pi.dual Y.1, by simpa [Pi.dual] using Y.2⟩
    have hXYd : Xd.1 < Yd.1 := by
      exact Pi.dual_lt_dual_iff.mpr hXY
    have hcommond : ¬∃ g : Gene, 0 < Xd.1.val g ∧ 0 < Yd.1.val g := by
      rintro ⟨g, hgX, hgY⟩
      apply hcommon
      exact ⟨g.dual, by simpa [Xd, Pi.dual] using hgX,
        by simpa [Yd, Pi.dual] using hgY⟩
    have hsigeqd : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Yd.1.val ≠ 0 ∧
        Sigma.sigma Xd.1 k = Sigma.sigma Yd.1 k := by
      rintro ⟨k, hkpos, hYd_ne, hsig⟩
      apply hsigeq
      refine ⟨k, hkpos, ?_, ?_⟩
      · intro hYzero
        apply hYd_ne
        change prime^[k] (Pi.dual Y.1).val = 0
        rw [Pi.dual_val, ← Chromosome.dual_prime_iterate, hYzero,
          Chromosome.dual_zero]
      · have hsig_swap := congrArg Prod.swap hsig
        change (signature (prime^[k] (Chromosome.dual X.1.val))).swap =
          (signature (prime^[k] (Chromosome.dual Y.1.val))).swap at hsig_swap
        rw [← Chromosome.dual_prime_iterate X.1.val k,
          ← Chromosome.dual_prime_iterate Y.1.val k,
          Chromosome.signature_dual, Chromosome.signature_dual,
          Prod.swap_swap, Prod.swap_swap] at hsig_swap
        exact hsig_swap
    have hXpnd : ¬∃ (g h : Gene), g.rank = h.rank ∧
        g.type = .Positive ∧ h.type = .Negative ∧
        0 < Xd.1.val g ∧ 0 < Xd.1.val h := by
      rintro ⟨g, h, hrank, hgpos, hhneg, hgX, hhX⟩
      apply hXpn
      refine ⟨h.dual, g.dual, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hrank]
      · simp [Gene.dual, hhneg]
      · simp [Gene.dual, hgpos]
      · simpa [Xd, Pi.dual] using hhX
      · simpa [Xd, Pi.dual] using hgX
    have had : (Sigma.sigma Xd.1 1).1 < (Sigma.sigma Yd.1 1).1 := by
      change (signature (prime^[1] (Chromosome.dual X.1.val))).1 <
        (signature (prime^[1] (Chromosome.dual Y.1.val))).1
      rw [← Chromosome.dual_prime_iterate X.1.val 1,
        ← Chromosome.dual_prime_iterate Y.1.val 1,
        Chromosome.signature_dual, Chromosome.signature_dual]
      simpa using hb_lt
    obtain ⟨W, hstepW, hWY⟩ :=
      exists_mutation_le_fifteen_ten_caseA m ih Xd Yd hXYd hcommond hsigeqd hXpnd had
    let Z : Pi := Pi.dual W
    refine ⟨Z, ?_, ?_⟩
    · have hstep_dual : Pi.Step (Pi.dual X.1) (Pi.dual Z) := by
        simpa [Z] using hstepW
      exact Pi.Step.of_dual hstep_dual
    · have hdual_le :=
        (Pi.dual_le_dual_iff (X := W) (Y := Pi.dual Y.1)).mpr hWY
      simpa [Z] using hdual_le
/-! ## Main theorem -/

/--
Proposition after (15.7) [Djoković 1982, p. 29]:
Let X, Y ∈ Π(n) with X < Y.  Then there exists a Π-mutation X → Z such that Z ≤ Y.
-/
theorem exists_mutation_le (n : ℕ) (X Y : nPi n)
    (hXY : X.1 < Y.1) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  revert X Y hXY
  refine Nat.strongRecOn n ?_
  intro n ih X Y hXY
  cases n with
  | zero =>
    exfalso
    have hX0 : X.1.val = 0 := rank_zero X.2
    have hY0 : Y.1.val = 0 := rank_zero Y.2
    exact absurd (Subtype.ext (hX0.trans hY0.symm)) (ne_of_lt hXY)
  | succ n =>
    cases n with
    | zero =>
      exfalso
      have hsig_le : signature X.1.val ≤ signature Y.1.val :=
        (le_iff_dominates.mp hXY.le) 0
      have hXsum : (signature X.1.val).1 + (signature X.1.val).2 = 1 := by
        rcases rank_one_pi_sig X.1.2 X.2 with h | h <;> simp [h]
      have hYsum : (signature Y.1.val).1 + (signature Y.1.val).2 = 1 := by
        rcases rank_one_pi_sig Y.1.2 Y.2 with h | h <;> simp [h]
      have hsig_eq : signature X.1.val = signature Y.1.val := by
        obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
        exact Prod.ext (le_antisymm h1_le (by linarith [h2_le]))
                       (le_antisymm h2_le (by linarith [h1_le]))
      exact absurd (Subtype.ext (Pi_rank_one_eq_of_sig_eq X.1.2 Y.1.2 X.2 Y.2 hsig_eq))
                   (ne_of_lt hXY)
    | succ m =>
      have ha₀_eq_c₀ := sigma_zero_fst_eq X Y hXY.le
      by_cases hcommon : ∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g
      · exact exists_mutation_le_shared_gene m ih X Y hXY hcommon
      · by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
            Sigma.sigma X.1 k = Sigma.sigma Y.1 k
        · exact exists_mutation_le_disjoint_sigma_eq m ih X.1 Y hXY hcommon hsigeq
        · by_cases hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
              g.type = .Positive ∧ h.type = .Negative ∧
              0 < X.1.val g ∧ 0 < X.1.val h
          · exact exists_mutation_le_disjoint_pair X.1 Y.1 hXY hcommon hsigeq hXpn
          · exact exists_mutation_le_fifteen_ten m ih X Y hXY hcommon hsigeq hXpn
