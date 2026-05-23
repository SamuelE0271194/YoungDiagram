import YoungDiagram.Theorem6.CaseA
import YoungDiagram.Theorem6.Dual

open Variety hiding prime prime_def
open Chromosome Sigma

/-! ## (15.10): X has no positive-negative gene pair of equal rank -/
/-- Dispatcher for Cases A and B of §15.10.
Case A is proved in `YoungDiagram.Theorem6.CaseA`; Case B is its sign-dual. -/
private lemma exists_mutation_le_fifteen_ten {m : ℕ}
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X < Y →
      ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y)
    (X Y : nPi (m + 2)) (hXY : X < Y)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y ≠ 0 ∧ sigma X k = sigma Y k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.1 g ∧ 0 < X.1.1 h) :
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y := by
  by_cases ha : (sigma X 1).1 < (sigma Y 1).1
  · exact exists_mutation_le_fifteen_ten_caseA m ih X Y hXY hcommon hsigeq hXpn ha
  · have ha_eq : (sigma X 1).1 = (sigma Y 1).1 :=
      le_antisymm (le_iff_dominates.mp hXY.le 1).1 (le_of_not_gt ha)
    have hYprime_ne : prime Y ≠ 0 := by
      intro hYprime
      have hXprime_zero : prime X = 0 := by
        have hle1 := le_iff_dominates.mp hXY.le 1
        simp only [Function.iterate_one, hYprime, map_zero] at hle1
        exact signature_eq_zero (le_antisymm hle1 (signature_nonneg _))
      have hsig_all (k : ℕ):
          (prime^[k] X).signature = (prime^[k] Y).signature := by
        cases k with
        | zero => simpa only [sigma, Function.iterate_zero, id_eq] using
            sigma_zero_eq X Y hXY.le
        | succ k => simp only [Function.iterate_succ_apply, hXprime_zero,
            iterate_map_zero, map_zero, hYprime]
      exact (ne_of_lt hXY) <| Subtype.val_injective
        <| Subtype.val_injective <| eq_of_sigma_eq X.1.2 Y.1.2 hsig_all
    have hsig_ne : sigma X 1 ≠ sigma Y 1 := fun hsig ↦ hsigeq ⟨1, Nat.one_pos, hYprime_ne, hsig⟩
    have hb_ne : (sigma X 1).2 ≠ (sigma Y 1).2 := fun hb_eq ↦ hsig_ne (Prod.ext ha_eq hb_eq)
    have hb_lt : (sigma X 1).2 < (sigma Y 1).2 :=
      lt_of_le_of_ne (le_iff_dominates.mp hXY.le 1).2 hb_ne
    let Xd : nPi (m + 2) :=
      ⟨Pi.dual X.1, by simpa [Pi.dual] using X.2⟩
    let Yd : nPi (m + 2) :=
      ⟨Pi.dual Y.1, by simpa [Pi.dual] using Y.2⟩
    have hcommond : ¬∃ g : Gene, 0 < Xd.1.1 g ∧ 0 < Yd.1.1 g := by
      refine fun ⟨g, hgX, hgY⟩ ↦ hcommon ⟨g.dual, ?_, ?_⟩
      · simpa [Xd, Pi.dual] using hgX
      · simpa [Yd, Pi.dual] using hgY
    have hsigeqd : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Yd ≠ 0 ∧
        sigma Xd k = sigma Yd k := by
      refine fun ⟨k, hkpos, hYd_ne, hsig⟩ ↦ hsigeq ⟨k, hkpos, ?_, ?_⟩
      · refine fun hYzero ↦ hYd_ne ?_
        rw [Pi.dual_val, ← dual_prime_iterate, hYzero, dual_zero]
      · have hsig_swap : (prime^[k] (dual X)).signature.swap =
          (prime^[k] (dual Y)).signature.swap := congrArg Prod.swap hsig
        rwa [← dual_prime_iterate X k, ← dual_prime_iterate Y k,
          signature_dual, signature_dual, Prod.swap_swap, Prod.swap_swap] at hsig_swap
    have hXpnd : ¬∃ (g h : Gene), g.rank = h.rank ∧
        g.type = .Positive ∧ h.type = .Negative ∧
        0 < Xd.1.1 g ∧ 0 < Xd.1.1 h := by
      refine fun ⟨g, h, hrank, hgpos, hhneg, hgX, hhX⟩ ↦
        hXpn ⟨h.dual, g.dual, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Gene.dual_rank, hrank]
      · simp only [Gene.dual, hhneg, GeneType.neg_negative]
      · simp only [Gene.dual, hgpos, GeneType.neg_positive]
      · simpa only [Pi.dual, dual_apply] using hhX
      · simpa only [Pi.dual, dual_apply] using hgX
    have had : (sigma Xd 1).1 < (sigma Yd 1).1 := by
      change (prime^[1] (dual X)).signature.1 <
        (prime^[1] (dual Y)).signature.1
      rw [← dual_prime_iterate X 1, ← dual_prime_iterate Y 1,
        signature_dual, signature_dual]
      simpa only [Function.iterate_one, Prod.fst_swap] using hb_lt
    obtain ⟨W, hstepW, hWY⟩ := exists_mutation_le_fifteen_ten_caseA m ih Xd Yd
      (Pi.dual_lt_dual_iff.2 hXY) hcommond hsigeqd hXpnd had
    let Z : Pi := Pi.dual W
    refine ⟨Z, ?_, ?_⟩
    · exact Pi.Step.of_dual (by simpa only [Pi.dual_dual, Z] using hstepW)
    · simpa only [Pi.dual_dual] using (Pi.dual_le_dual_iff (Y := Pi.dual Y)).2 hWY

private lemma exists_mutation_le_rank_zero {X Y : nPi 0} (hXY : X < Y) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_zero X.2).trans (rank_zero Y.2).symm) (ne_of_lt hXY)

private lemma exists_mutation_le_rank_one {X Y : nPi 1} (hXY : X < Y) :
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y :=
  have hsig_le : signature X ≤ signature Y := hXY.le 0
  have hXsum : (signature X).1 + (signature X).2 = 1 := by
    rcases rank_one_pi_sig X.1.2 X.2 with h | h <;> simp only [h, zero_add, add_zero]
  have hYsum : (signature Y).1 + (signature Y).2 = 1 := by
    rcases rank_one_pi_sig Y.1.2 Y.2 with h | h <;> simp only [h, zero_add, add_zero]
  have hsig_eq : signature X = signature Y := by
    obtain ⟨h1_le, h2_le⟩ := Prod.le_def.1 hsig_le
    exact Prod.ext (h1_le.antisymm (by linarith [h2_le])) (h2_le.antisymm (by linarith [h1_le]))
  absurd (Pi_rank_one_eq_of_sig_eq X.1.2 Y.1.2 X.2 Y.2 hsig_eq) (ne_of_lt hXY)

/--
Proposition after (15.7) [Djoković 1982, p. 29]:
Let X, Y ∈ Π(n) with X < Y.  Then there exists a Π-mutation X → Z such that Z ≤ Y.
-/
theorem exists_mutation_le {n : ℕ} : ∀ (X Y : nPi n), X < Y →
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y :=
  Nat.strongRecOn n fun n ih X Y hXY ↦
  match n with
  | 0 => exists_mutation_le_rank_zero hXY
  | 1 => exists_mutation_le_rank_one hXY
  | m + 2 => by
    by_cases hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g
    · exact exists_mutation_le_shared_gene m ih X Y hXY hcommon
    · by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ prime^[k] Y ≠ 0 ∧ sigma X k = sigma Y k
      · exact exists_mutation_le_disjoint_sigma_eq m ih X Y hXY hcommon hsigeq
      · by_cases hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
            g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h
        · exact exists_mutation_le_disjoint_pair X Y hXY hcommon hsigeq hXpn
        · exact exists_mutation_le_fifteen_ten ih X Y hXY hcommon hsigeq hXpn
