import YoungDiagram.Variety.Basic

open Finsupp Chromosome Pointwise

namespace Chromosome

section polarized

def IsPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type ≠ .NonPolarized)

lemma IsPolarized_def {X : Chromosome} :
  X.IsPolarized ↔ X.filter (·.type ≠ .NonPolarized) = X := IsFiltered_def

lemma IsPolarized_def' {X : Chromosome} :
  X.IsPolarized ↔ ∀ g ∈ X.support, g.type ≠ .NonPolarized := IsFiltered_def'

lemma IsPolarized_zero : IsPolarized 0 := IsFiltered_zero

lemma IsPolarized_single {g : Gene} {n : ℕ} (hn : n ≠ 0) :
  IsPolarized (single g n) ↔ g.type ≠ .NonPolarized := IsFiltered_single hn

lemma IsPolarized_filter {X : Chromosome} {q : Gene → Prop} [DecidablePred q]
  (h : X.IsPolarized) : IsPolarized (X.filter q) := IsFiltered_filter h

lemma IsPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank_def, dif_neg (by omega)]
  exact IsPolarized_single Nat.one_ne_zero

lemma IsPolarized_ofRank' {k : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).IsPolarized :=
  match k with
  | 0 => IsPolarized_zero
  | n + 1 => (IsPolarized_ofRank (Nat.le_add_left 1 n)).2 hε

lemma IsPolarized_ofRankAlt {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRankAlt k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRankAlt_def, IsPolarized_ofRank hk,
    GeneType.negOnePow_smul]
  split_ifs
  · rfl
  · exact GeneType.neg_ne_nonPolarized_iff.symm

lemma IsPolarized_ofRankAlt' {k : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRankAlt k ε).IsPolarized :=
  match k with
  | 0 => IsPolarized_zero
  | n + 1 => (IsPolarized_ofRankAlt (Nat.le_add_left 1 n)).2 hε

lemma IsPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsPolarized ↔ X.IsPolarized ∧ Y.IsPolarized := IsFiltered_iff_add

lemma IsPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsPolarized ↔ X.IsPolarized := IsFiltered_iff_nsmul hn

lemma IsPolarized_iff_lift {X : Chromosome} :
  X.lift.IsPolarized ↔ X.IsPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

lemma IsPolarized_iff_iterate_lift {X : Chromosome} {k : ℕ} :
  (lift^[k] X).IsPolarized ↔ X.IsPolarized :=
    IsFiltered_iff_iterate_lift (fun _ ↦ .rfl)

lemma IsPolarized_support_of_below_one {X : Chromosome} (hX : X.IsPolarized) :
    (X.below 1).support ⊆ {⟨1, .Positive, le_rfl⟩, ⟨1, .Negative, le_rfl⟩} := by
  intro g hg
  cases htype : g.type <;> simp only [Finset.mem_insert, Finset.mem_singleton]
  · exact False.elim <| (IsPolarized_def'.1 (IsPolarized_filter hX) g hg) htype
  · refine Or.inl ?_; simp_rw [← htype, ← support_of_below_one hg]
  · refine Or.inr ?_; simp_rw [← htype, ← support_of_below_one hg]

lemma IsPolarized_signature {X : Chromosome} (hX : X.IsPolarized) :
    (X.below 1).signature =
    ((X ⟨1, .Positive, le_rfl⟩, X ⟨1, .Negative, le_rfl⟩) : ℚ × ℚ) := by
  simp only [signature, sum, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_subset (IsPolarized_support_of_below_one hX), Finset.sum_pair (by decide),
    below_def, filter_apply_pos _ X NeZero.one_le, filter_apply_pos _ X NeZero.one_le,
    Gene.signature_of_positive rfl, Gene.signature_of_negative rfl]
  · simp
  · rintro x (h1 | h1) h2 <;> rw [Finsupp.notMem_support_iff.1 h2, Nat.cast_zero, zero_smul]

end polarized

end Chromosome

namespace Variety

section Pi

def Pi : Variety := varietyOfFilter (·.type ≠ .NonPolarized)

lemma mem_Pi_iff {X : Chromosome} :
  X ∈ Pi ↔ IsPolarized X := mem_varietyOfFilter_iff

lemma mem_Pi_iff_add {X Y : Chromosome} :
  (X + Y) ∈ Pi ↔ X ∈ Pi ∧ Y ∈ Pi := IsPolarized_iff_add

lemma prime_Pi : Pi.prime = Pi := prime_varietyOfFilter (fun _ ↦ .rfl)

lemma parityDecomp_mem_smul_Pi {X : Chromosome} {n : ℕ} (h : X ∈ n • Pi) :
  oddPart X ∈ n • Pi ∧ evenPart X ∈ n • Pi :=
  ⟨filter_mem_smul_varietyOfFilter (Odd ·.rank) h,
    filter_mem_smul_varietyOfFilter (Even ·.rank) h⟩

lemma parityDecomp_mem_Pi {X : Chromosome} (h : X ∈ Pi) :
    oddPart X ∈ Pi ∧ evenPart X ∈ Pi :=
  ⟨IsFiltered_filter h, IsFiltered_filter h⟩

lemma prime_mem_Pi {X : Chromosome} (hX : X ∈ Pi) : X.prime ∈ Pi :=
  prime_mem_varietyOfFilter (fun _ ↦ .rfl) hX

noncomputable def prime_on_Pi (X : Pi) : Pi := ⟨X.1.prime, prime_mem_Pi X.2⟩

lemma prime_on_Pi_iterate (X : Pi) (k : ℕ) :
    (prime_on_Pi^[k] X).1 = Chromosome.prime^[k] X :=
  prime_on_varietyOfFilter_iterate (fun _ ↦ .rfl) X k

lemma prime_mem_Pi_iterate {X : Chromosome} (hX : X ∈ Pi) {k : ℕ} :
    Chromosome.prime^[k] X ∈ Pi :=
  prime_mem_varietyOfFilter_iterate (fun _ ↦ .rfl) hX

end Pi

end Variety

section signature

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

end signature

section order

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

instance : PartialOrder Variety.Pi :=
  { inferInstanceAs (Preorder Variety.Pi) with
    le_antisymm := fun A B hAB hBA ↦
      Subtype.val_injective (pi_chromosome_antisymm A.2 B.2 hAB hBA) }

end order

section rank_one

lemma rank_eq_one_pi_single {X : Chromosome} (hX : X ∈ Variety.Pi) (hr : X.rank = 1) :
    ∃ ε : GeneType, ε ≠ .NonPolarized ∧ X = Gene.ofRank 1 ε := by
  obtain ⟨ε, hε⟩ := rank_one hr
  exact ⟨ε, (IsPolarized_ofRank le_rfl).1 (hε ▸ Variety.mem_Pi_iff.1 hX), hε⟩

lemma rank_one_pi_sig {X : Chromosome} (hX : X ∈ Variety.Pi) (hr : X.rank = 1) :
    X.signature = (1, 0) ∨ X.signature = (0, 1) := by
  obtain ⟨ε, ⟨h1, h2⟩⟩ := rank_eq_one_pi_single hX hr
  match ε, h1 with
  | .Positive, _ => exact h2 ▸ Or.inl signature_ofRank_one_positive
  | .Negative, _ => exact h2 ▸ Or.inr signature_ofRank_one_negative

lemma Pi_rank_one_eq_of_sig_eq {X Y : Chromosome}
    (hX : X ∈ Variety.Pi) (hY : Y ∈ Variety.Pi)
    (hrX : X.rank = 1) (hrY : Y.rank = 1)
    (hsig : X.signature = Y.signature) : X = Y := by
  obtain ⟨εX, hεX, hXε⟩ := rank_eq_one_pi_single hX hrX
  obtain ⟨εY, hεY, hYε⟩ := rank_eq_one_pi_single hY hrY
  refine eq_of_prime_eq_sig_eq hX hY ?_ hsig
  simp only [hXε, hYε, prime_ofRank, tsub_self, Gene.ofRank_zero]

end rank_one
