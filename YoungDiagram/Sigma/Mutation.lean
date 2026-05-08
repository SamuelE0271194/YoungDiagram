import YoungDiagram.Sigma.Basic

open Chromosome Finsupp

namespace Sigma

noncomputable def type3Increment (ε : GeneType) (m n i : ℕ) : ℚ × ℚ :=
  if m ≤ i ∧ i ≤ n then
    if Even i then (Gene.ofRank 1 ε).signature else (Gene.ofRank 1 (-ε)).signature
  else (0, 0)

/-- For a type-3 primitive mutation, `σ(Y3)_i = σ(X3)_i + increment(i)`, where
`increment(i) = (0, 1)` if `i` is even, `(1, 0)` if `i` is odd, for `i ∈ [m, n]`,
and `(0, 0)` outside that range. -/
lemma mutation_type3_sigma_eq_increment {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) (i : ℕ) :
    sigma (Pi.Y3 hε h_le hm).val i =
    sigma (Pi.X3 hε h_le hm).val i + type3Increment ε m n i := by
  unfold type3Increment
  simp only [sigma, Pi.Y3_eq, Pi.X3_eq, iterate_map_add, map_add]
  rw [@prime_iterate_ofRankAlt i (m - 1), @prime_iterate_ofRankAlt i (n + 1),
    @prime_iterate_ofRankAlt i m, @prime_iterate_ofRankAlt i n]
  split_ifs with h hei
  · have h1 : m - 1 - i = 0 := by omega
    have h3 : m - i = 0 := by omega
    simp [h1, h3]
    have h_sign_i_1 : ((↑i : ℤ).negOnePow) • ε = ε := by
      simp [GeneType.negOnePow_smul', hei]
    have h_sign_i_2 : (↑i + 1 : ℤ).negOnePow • ε = -ε := by
      rw [← GeneType.neg_negOnePow_smul, h_sign_i_1]
    simp [h_sign_i_1, h_sign_i_2, show n + 1 - i = (n - i) + 1 from by omega]
    simp [signature_ofRankAlt_general' hε]
  · -- m ≤ i ∧ i ≤ n, ¬Even i
    have h1 : m - 1 - i = 0 := by omega
    have h3 : m - i = 0 := by omega
    simp [h1, h3]
    have h_sign_i_1 : ((↑i : ℤ).negOnePow) • ε = -ε := by
      simp [GeneType.negOnePow_smul', hei]
    have h_sign_i_2 : (↑i + 1 : ℤ).negOnePow • ε = ε := by
      rw [← GeneType.neg_negOnePow_smul, h_sign_i_1]
      simp
    simp [h_sign_i_1, h_sign_i_2, show n + 1 - i = (n - i) + 1 from by omega]
    have hε_neg : -ε ≠ .NonPolarized := GeneType.neg_ne_nonPolarized_iff.mp hε
    simp [signature_ofRankAlt_general' hε_neg]
    --
  · -- ¬(m ≤ i ∧ i ≤ n)
    push Not at h
    by_cases hlt : i < m
    · simp only [GeneType.smul_neg, ← map_add,
                 show m - 1 - i = m - i - 1 from by omega,
                 show n + 1 - i = n - i + 1 from by omega]
      have h00 : (0, 0) = (0 : ℚ × ℚ) := rfl
      rw [h00, add_zero]
      exact (mutation_type3_signature_eq
        ((GeneType.smul_ne_nonPolarized_iff (n := (i : ℤ))).mp hε)
        (Nat.sub_le_sub_right h_le i)
        (by omega)).symm
    · have hgt : n < i := by omega
      simp only [Gene.ofRankAlt_def]
      have h1 : m - 1 - i = 0 := by omega
      have h2 : n + 1 - i = 0 := by omega
      have h3 : m - i = 0 := by omega
      have h4 : n - i = 0 := by omega
      simp [h1, h2, h3, h4]
      rfl

/-- For a type-3 primitive mutation, `σ(Y3)_i = σ(X3)_i + increment(i)`, where
`increment(i) = (0, 1)` if `i` is even, `(1, 0)` if `i` is odd, for `i ∈ [m, n]`,
and `(0, 0)` outside that range. -/
lemma mutation_type3_sigma_eq {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m n : ℕ} (h_le : m ≤ n) (hm : 1 ≤ m) (i : ℕ) :
    sigma (Pi.Y3 hε h_le hm).val i =
    sigma (Pi.X3 hε h_le hm).val i +
    if m ≤ i ∧ i ≤ n then
      if Even i then (Gene.ofRank 1 ε).signature else (Gene.ofRank 1 (-ε)).signature
    else (0, 0) := by
  simpa [type3Increment] using mutation_type3_sigma_eq_increment hε h_le hm i

end Sigma
