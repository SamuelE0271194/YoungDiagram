import YoungDiagram.Sigma

open Chromosome Finsupp

section antisymm

variable {A B : Chromosome} (hA : A ∈ Variety.Pi) (hB : B ∈ Variety.Pi)

include hA hB

lemma below_one_eq_of_signature_eq (h : signature (A.below 1) = signature (B.below 1)) :
    A.below 1 = B.below 1 := by
  ext g
  by_cases hg : ¬ g.rank ≤ 1
  · rw [below_def, below_def, filter_apply_neg _ A hg, filter_apply_neg _ B hg]
  · replace hg : g.rank = 1 := Nat.le_antisymm (by tauto) g.rank_pos
    rw [below_def, below_def, filter_apply_pos _ A (Nat.le_of_eq hg),
      filter_apply_pos _ B (Nat.le_of_eq hg)]
    rw [IsPolarized_signature hA, IsPolarized_signature hB] at h
    cases htype : g.type
    · rw [Finsupp.notMem_support_iff.1 (fun h ↦ IsPolarized_def'.1 hA g h htype),
        Finsupp.notMem_support_iff.1 (fun h ↦ IsPolarized_def'.1 hB g h htype)]
    · simpa [← hg, ← htype] using (Prod.ext_iff.1 h).1
    · simpa [← hg, ← htype] using (Prod.ext_iff.1 h).2

lemma below_one_eq_of_sig_eq (hsig : A.signature = B.signature)
    (habove : A.above 1 = B.above 1) : A.below 1 = B.below 1 := by
  apply below_one_eq_of_signature_eq hA hB
  rwa [congr_arg signature (rank_decomposition A 1), congr_arg signature
    (rank_decomposition B 1), map_add, map_add, congr_arg signature habove,
    add_right_cancel_iff] at hsig

lemma eq_of_prime_eq_sig_eq (hprime : A.prime = B.prime)
    (hsig : A.signature = B.signature) : A = B := by
  have habove := above_one_eq_of_prime_eq hprime
  rw [rank_decomposition A 1, habove, below_one_eq_of_sig_eq hA hB hsig habove,
    ← rank_decomposition]

/-- The sigma sequence uniquely determines a polarized chromosome. -/
lemma eq_of_sigma_eq (h : ∀ k, signature (prime^[k] A) = signature (prime^[k] B)) :
    A = B := by
  suffices ∀ n (A B), A ∈ Variety.Pi → B ∈ Variety.Pi →
      max A.maxRank B.maxRank ≤ n →
      (∀ k, signature (prime^[k] A) = signature (prime^[k] B)) → A = B from
    this _ _ _ hA hB le_rfl h
  intro n; induction n with
  | zero =>
    intro _ _ _ _ hn _
    have ⟨hA, hB⟩ := max_le_iff.1 hn
    rw [maxRank_eq_zero (Nat.le_zero.1 hA), maxRank_eq_zero (Nat.le_zero.1 hB)]
  | succ n ih =>
    intro A B hA hB hn h
    have hsig : signature A = signature B := by
      simpa only [Function.iterate_zero, id_eq] using h 0
    by_cases hA0 : A = 0
    · rw [hA0, map_zero] at hsig
      rw [hA0, signature_eq_zero hsig.symm]
    · have hB0 : B ≠ 0 := fun h ↦ hA0 <| signature_eq_zero <| by rw [hsig, h, map_zero]
      refine eq_of_prime_eq_sig_eq hA hB ?_ hsig
      · refine ih A.prime B.prime (Variety.prime_mem_Pi hA)
          (Variety.prime_mem_Pi hB) ?_ ?_
        · have := maxRank_prime_lt hA0; have := maxRank_prime_lt hB0; omega
        · intro k; rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply]
          exact h (k + 1)

lemma pi_chromosome_antisymm
    (hAB : A ≤ B) (hBA : B ≤ A) : A = B :=
  eq_of_sigma_eq hA hB fun k ↦ le_antisymm (hAB k) (hBA k)

end antisymm

section aux

lemma signature_pi_isNat {X : Chromosome} (hX : X ∈ Variety.Pi) :
    ∃ n : ℕ × ℕ, X.signature = (↑n.1, ↑n.2) := by
  induction X using Finsupp.induction with
  | zero => use 0; rfl
  | single_add g n X hg hn h =>
    replace hX := Variety.mem_Pi_iff_add.1 hX
    obtain ⟨k, hk⟩ := h hX.2
    obtain ⟨m, hm⟩ : ∃ m : ℕ × ℕ, signature (single g n) = (↑m.1, ↑m.2) := by
      rw [← Gene.ofRank_eq_gene_smul, map_nsmul, signature_ofRank]
      split_ifs
      · use 0; rw [smul_zero]; rfl
      · have polar := (IsPolarized_single hn).1 (Variety.mem_Pi_iff.1 hX.1)
        match g.type, polar with
        | .Positive, _ =>
          rw [Gene.signature_of_positive rfl]
          split_ifs with heven
          · obtain ⟨m, hm : g.rank = m + m⟩ := heven
            use n * m; norm_num [hm]
          · obtain ⟨m, hm : g.rank = 2 * m + 1⟩ := Nat.not_even_iff_odd.1 heven
            use (n * (m + 1), n * m); norm_num [hn, hm]; ring
        | .Negative, _ =>
          rw [Gene.signature_of_negative rfl]
          split_ifs with heven
          · obtain ⟨m, hm : g.rank = m + m⟩ := heven
            use n * m; norm_num [hm]
          · obtain ⟨m, hm : g.rank = 2 * m + 1⟩ := Nat.not_even_iff_odd.1 heven
            use (n * m, n * (m + 1)); norm_num [hn, hm]; ring
    rw [map_add, hm, hk]
    exact ⟨m + k, by simp only [Prod.mk_add_mk, Prod.fst_add, Nat.cast_add, Prod.snd_add]⟩

end aux
