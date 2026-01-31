import YoungDiagram.Chromosome

namespace Chromosome

noncomputable def sigma_k (c : Chromosome) (k : ℕ) : ℚ × ℚ :=
  signature (prime^[k] c)

lemma prime_prime : (X : Chromosome) → (k : ℕ) → prime^[k + 1] X = prime^[k] (prime X) := by
  intro X k
  induction k with
  | zero => rfl
  | succ n ih => simp

lemma prime_prime_other : (k : ℕ) → (X : Chromosome) → prime^[k + 1] X = prime (prime^[k] X) := by
  intro k
  induction k with
  | zero =>
    intro X
    rfl
  | succ n ih =>
    intro X
    simp
    rw [← ih (prime X)]
    simp

lemma sigma_nonneg_1 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).1 ≥ 0 := by
  intro X k
  rw [sigma_k]
  have h : (signature (prime^[k] X)) ≥ 0 :=
    signature_nonneg (prime^[k] X)
  exact h.left

lemma sigma_nonneg_2 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).2 ≥ 0 := by
  intro X k
  rw [sigma_k]
  have h : (signature (prime^[k] X)) ≥ 0 :=
    signature_nonneg (prime^[k] X)
  exact h.right

lemma sig_prime_le_sig_1 : (X : Chromosome) → (signature (prime X)).1 ≤ (signature X).1 := by
  sorry

lemma sig_prime_le_sig_2 : (X : Chromosome) → (signature (prime X)).2 ≤ (signature X).2 := by
  sorry

-- If a_k of a chromosome X is 0, then a_k+1 is also 0
lemma if_0_then_next_is_zero_1 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).1 = 0 →
  (sigma_k X (k+1)).1 = 0 := by
    intro X k h
    rw [sigma_k] at h
    rw [sigma_k]
    have hle : (signature (prime^[k] (prime X))).1 ≤ (signature (prime^[k] X)).1 := by
      rw [← prime_prime X k]
      rw [prime_prime_other k X]
      apply sig_prime_le_sig_1 (prime^[k] X)
    have hle1 : (signature (prime^[k] (prime X))).1 ≤ 0 := by
      simpa [h] using hle
    have hle2 : (signature (prime^[k] (prime X))).1 ≥ 0 :=
      sigma_nonneg_1 X (k + 1)
    exact le_antisymm hle1 hle2

-- If b_k of a chromosome X is 0, then b_k+1 is also 0
lemma if_0_then_next_is_zero_2 : (X : Chromosome) → (k : ℕ) → (sigma_k X k).2 = 0 →
  (sigma_k X (k+1)).2 = 0 := by
    intro X k h
    rw [sigma_k] at h
    rw [sigma_k]
    have hle : (signature (prime^[k] (prime X))).2 ≤ (signature (prime^[k] X)).2 := by
      rw [← prime_prime X k]
      rw [prime_prime_other k X]
      apply sig_prime_le_sig_2 (prime^[k] X)
    have hle1 : (signature (prime^[k] (prime X))).2 ≤ 0 := by
      simpa [h] using hle
    have hle2 : (signature (prime^[k] (prime X))).2 ≥ 0 :=
      sigma_nonneg_2 X (k + 1)
    exact le_antisymm hle1 hle2

lemma cond15_2_0_case : (X : Chromosome) →
  ∃ k : ℕ, sigma_k X k = 0 := by sorry

lemma cond15_2_and_3 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k) ≥ (sigma_k X k + 1) := by sorry

lemma cond15_4_and_5_1 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).1 ≥ (sigma_k X k + 1).2 := by sorry

lemma cond15_4_and_5_2 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).2 ≥ (sigma_k X k + 1).1 := by sorry

lemma cond15_6_and_7_1 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).1 - (sigma_k X (k+1)).1 ≥ (sigma_k X (k+1)).2 - (sigma_k X (k+2)).2 :=
  by sorry

lemma cond15_6_and_7_2 : (X : Chromosome) →
  ∀ k : ℕ, (sigma_k X k).2 - (sigma_k X (k+1)).2 ≥ (sigma_k X (k+1)).1 - (sigma_k X (k+2)).1 :=
  by sorry

-- lemma existence_of_mut_0 : (X Y : Chromosome) → (h : X < Y)

lemma cond15_8 : (X Y : Chromosome) → (h : X ≤ Y) →
  ∀ k : ℕ, sigma_k X k ≤ sigma_k Y k := by
  intro X Y h k
  sorry
