import YoungDiagram.Sigma.Basic

open Chromosome Finsupp

namespace Sigma

variable (X : Chromosome) (k : ℕ)

local notation "a" X:max k:max => Prod.fst (sigma X k)

local notation "b" X:max k:max => Prod.snd (sigma X k)

lemma cond_15_6_compare_drop_to_0 (hX : X ∈ Variety.Pi) :
    if Even k then (drop X k).1 ≤ (drop X 0).1
              else (drop X k).2 ≤ (drop X 0).1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h15_6 := cond_15_6 X k hX
    split_ifs with heven
    · -- Even (k+1), so ¬Even k
      have hkodd : ¬Even k := by rwa [Nat.even_add_one] at heven
      simp only [hkodd, ↓reduceIte] at ih h15_6
      exact h15_6.trans ih
    · -- ¬Even (k+1), so Even k
      have hkeven : Even k := by rwa [Nat.even_add_one, not_not] at heven
      simp only [hkeven, ↓reduceIte] at ih h15_6
      exact h15_6.trans ih

/-- (15.6) a₀ − a₁ ≥ bκ − bκ₊₁ (or a depending on sign of k) -/
lemma cond_15_6_compare_k_to_0 (hX : X ∈ Variety.Pi) :
    if Even k then a X k - a X (k + 1) ≤ a X 0 - a X 1
              else b X k - b X (k + 1) ≤ a X 0 - a X 1 := by
  simpa using cond_15_6_compare_drop_to_0 X k hX

lemma a1_ai_le_b0_bi_1 (hX : X ∈ Variety.Pi) {i : ℕ} (h : i ≥ 1) :
  (b X 0 - b X (i - 1)) ≥ (a X 1 - a X i) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => simp
  | succ j ih =>
    induction j with
    | zero => exact cond_15_7 X 0 hX
    | succ j ih =>
      by_cases hei : Even (j + 2)
      · have hei1 : ¬ (Even (j + 1)) := Nat.even_add_one.mp hei
        have : b X (j + 1) - b X (j + 2) ≥ a X (j + 2) - a X (j + 3) := by
          have h := cond_15_6 X (j + 1) hX
          rw [if_neg hei1] at h
          exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
                   show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
                   show j + 3 - 1 = j + 2 from by omega]
        linarith
      · have hei1 : Even (j + 1) := by rwa [Nat.even_add_one, not_not] at hei
        have : b X (j + 1) - b X (j + 2) ≥ a X (j + 2) - a X (j + 3) := by
          have h := cond_15_7 X (j + 1) hX
          rw [if_pos hei1] at h
          exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
                   show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
                   show j + 3 - 1 = j + 2 from by omega]
        linarith

lemma b2_bi_2_le_a1_ai (hX : X ∈ Variety.Pi) {i : ℕ} (h : i ≥ 2) :
  b X 2 - b X (i + 1) ≤ (a X 1 - a X i) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero =>
    have := cond_15_7 X 1 hX
    exact this
  | succ j ih =>
    by_cases hei : Even (j + 2)
    · have step : b X (j + 3) - b X (j + 4) ≤ a X (j + 2) - a X (j + 3) := by
        have h := cond_15_6 X (j + 2) hX
        rw [if_pos hei] at h
        exact h
      have ih' : b X 2 - b X (2 + j + 1) ≤ a X 1 - a X (2 + j) := ih (by omega)
      have h1 : 2 + (j + 1) + 1 = j + 4 := by omega
      have h2 : 2 + (j + 1) = j + 3 := by omega
      rw [h1, h2]
      simp only [show j + 2 + 1 = j + 3 from by omega,
                  show 2 + j = j + 2 from by omega] at ih'
      linarith
    · have step : b X (j + 3) - b X (j + 4) ≤ a X (j + 2) - a X (j + 3) := by
        have h := cond_15_7 X (j + 2) hX
        rw [if_neg hei] at h
        exact h
      have ih' : b X 2 - b X (2 + j + 1) ≤ a X 1 - a X (2 + j) := ih (by omega)
      have h1 : 2 + (j + 1) + 1 = j + 4 := by omega
      have h2 : 2 + (j + 1) = j + 3 := by omega
      rw [h1, h2]
      simp only [show j + 2 + 1 = j + 3 from by omega,
                  show 2 + j = j + 2 from by omega] at ih'
      linarith

end Sigma
