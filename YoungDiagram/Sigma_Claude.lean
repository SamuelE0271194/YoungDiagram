import YoungDiagram.SigmaAux_Claude

open Chromosome

namespace Sigma

variable (X : Chromosome) (k : ℕ)

/--
For `X ∈ Π`, `σ(X)` is the 2×∞ nonneg integral matrix whose k-th column is
`(aₖ, bₖ) = sig X^(k)`, as defined in [Djoković 1982, (15.1)].

Represented as a function `ℕ → ℚ × ℚ`, where the first component is `aₖ`
and the second is `bₖ`.
-/
noncomputable def sigma : ℕ → ℚ × ℚ :=
  fun k ↦ signature (prime^[k] X)

local notation "a" X:max k:max => Prod.fst (sigma X k)

local notation "b" X:max k:max => Prod.snd (sigma X k)

lemma antitone : Antitone (sigma X) := by
  refine antitone_nat_of_succ_le (fun _ ↦ ?_)
  simp only [sigma, Function.iterate_succ_apply']
  exact (signature_prime_le _).trans inf_le_left

lemma eventually_zero : ∃ K, ∀ k ≥ K, sigma X k = 0 := by
  refine ⟨X.maxRank, fun k hk ↦ ?_⟩
  simp only [sigma]
  have hprime_zero : prime^[X.maxRank] X = 0 := by
    have h : prime^[X.maxRank] (X.below X.maxRank) = 0 := prime_below le_rfl
    rwa [below_maxRank] at h
  rw [← Nat.sub_add_cancel hk, Function.iterate_add_apply,
    hprime_zero, iterate_map_zero, map_zero]

lemma cond_15_2 : (∀ k, a X (k + 1) ≤ a X k) ∧ (∃ K, ∀ k ≥ K, a X k = 0) :=
  ⟨fun k ↦ (Prod.le_def.1 (antitone X (Nat.le_add_right k 1))).1,
    (eventually_zero X).imp fun _ h1 k h2 ↦ congr_arg Prod.fst (h1 k h2)⟩

lemma cond_15_3 : (∀ k, b X (k + 1) ≤ b X k) ∧ (∃ K, ∀ k ≥ K, b X k = 0) :=
  ⟨fun k ↦ (antitone X (Nat.le_add_right k 1)).2,
    (eventually_zero X).imp fun _ h1 k h2 ↦ congr_arg Prod.snd (h1 k h2)⟩

/-- (15.4) a₀ ≥ b₁ ≥ a₂ ≥ b₃ ≥ … -/
lemma cond_15_4 : if Even k then b X (k + 1) ≤ a X k
    else a X (k + 1) ≤ b X k := by
  split_ifs <;> simp only [sigma, Function.iterate_succ_apply']
  · exact ((signature_prime_le _).trans inf_le_right).2
  · exact ((signature_prime_le _).trans inf_le_right).1

/-- (15.5) b₀ ≥ a₁ ≥ b₂ ≥ a₃ ≥ … -/
lemma cond_15_5 : if Even k then a X (k + 1) ≤ b X k
    else b X (k + 1) ≤ a X k := by
  split_ifs <;> simp only [sigma, Function.iterate_succ_apply']
  · exact ((signature_prime_le _).trans inf_le_right).1
  · exact ((signature_prime_le _).trans inf_le_right).2

/-- (15.6) a₀ − a₁ ≥ b₁ − b₂ ≥ a₂ − a₃ ≥ b₃ − b₄ ≥ … -/
lemma cond_15_6 (hX : X ∈ Variety.Pi) :
    if Even k then b X (k + 1) - b X (k + 2) ≤ a X k - a X (k + 1)
              else a X (k + 1) - a X (k + 2) ≤ b X k - b X (k + 1) := by
  have h := cond_15_6_Pi (Variety.prime_mem_Pi_iterate hX (k := k))
  split_ifs with heven <;> simp only [sigma, Function.iterate_succ_apply']
  · exact (Prod.mk_le_swap.1 h).1
  · exact (Prod.mk_le_swap.1 h).2

/-- (15.7) b₀ − b₁ ≥ a₁ − a₂ ≥ b₂ − b₃ ≥ a₃ − a₄ ≥ … -/
lemma cond_15_7 (hX : X ∈ Variety.Pi) :
    if Even k then a X (k + 1) - a X (k + 2) ≤ b X k - b X (k + 1)
              else b X (k + 1) - b X (k + 2) ≤ a X k - a X (k + 1) := by
  have h := cond_15_6_Pi (Variety.prime_mem_Pi_iterate hX (k := k))
  split_ifs with heven <;> simp only [sigma, Function.iterate_succ_apply']
  · exact (Prod.mk_le_swap.1 h).2
  · exact (Prod.mk_le_swap.1 h).1

/-- (15.8) If `X < Y` in `Π` then `aₖ ≤ cₖ` and `bₖ ≤ dₖ` for all `k`,
where `(aₖ, bₖ) = σ(X)ₖ` and `(cₖ, dₖ) = σ(Y)ₖ`. -/
lemma cond_15_8 {X Y : Variety.Pi} (h : X < Y) (k : ℕ) :
    a X k ≤ a Y k ∧ b X k ≤ b Y k := le_iff_dominates.1 h.le k

end Sigma
