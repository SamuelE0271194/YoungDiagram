import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise
import YoungDiagram.Chromosome

abbrev Variety := AddSubmonoid Chromosome

noncomputable def Variety.prime (v : Variety) : Variety :=
  v.map Chromosome.prime

lemma Variety.prime_def (v : Variety) :
  v.prime = v.map Chromosome.prime := rfl

open Finsupp Pointwise

namespace Chromosome

lemma signature_filter_le (X : Chromosome) (p : Gene → Prop) [DecidablePred p] :
    signature (X.filter p) ≤ X.signature := by
  induction X using Finsupp.induction
  · rw [filter_zero]
  · expose_names
    rw [filter_add, map_add, map_add]
    refine add_le_add ?_ h_2
    by_cases ha : p a
    · rwa [filter_single_of_pos]
    · rw [filter_single_of_neg, map_zero]
      · exact signature_nonneg _
      exact ha

section IsFiltered

variable {p : Gene → Prop} [DecidablePred p] {X : Chromosome}

variable (p X) in
def IsFiltered : Prop := X.filter p = X

lemma IsFiltered_def : X.IsFiltered p ↔ X.filter p = X := .rfl

lemma IsFiltered_def' : X.IsFiltered p ↔ ∀ g ∈ X.support, p g := by
  simp [IsFiltered_def, filter_eq_self_iff]

lemma IsFiltered_zero : IsFiltered p 0 := by
  simp only [IsFiltered, filter_zero]

lemma IsFiltered_single {g : Gene} {n : ℕ} (hn : n ≠ 0) :
    IsFiltered p (single g n) ↔ p g := by
  rw [IsFiltered_def', support_single_ne_zero _ hn]
  exact List.forall_mem_singleton

lemma IsFiltered_filter {q : Gene → Prop} [DecidablePred q]
    (h : X.IsFiltered p) : IsFiltered p (X.filter q) := by
  rw [IsFiltered_def'] at h ⊢
  exact fun _ hg ↦ h _ ((Finset.filter_subset ..) hg)

lemma IsFiltered_add_single {g : Gene} {n : ℕ} (hn : 1 ≤ n) :
    IsFiltered p (X + single g n) ↔ X.IsFiltered p ∧ p g := by
  constructor <;> intro h
  · by_cases hg : p g
    · simp only [IsFiltered, filter_add, hg, filter_single_of_pos, add_left_inj] at h
      exact ⟨h, hg⟩
    · simp only [IsFiltered, filter_add, hg, not_false_eq_true, filter_single_of_neg,
      add_zero] at h
      apply_fun signature at h
      have := h ▸ (signature_filter_le X p)
      rw [map_add, signature_single g.rank_pos,
        add_le_iff_nonpos_right, Prod.le_def] at this
      change n * g.signature.1 ≤ 0 ∧ n * g.signature.2 ≤ 0 at this
      exact absurd ⟨nonpos_of_mul_nonpos_right this.1 (Rat.natCast_pos.2 hn),
        nonpos_of_mul_nonpos_right this.2 (Rat.natCast_pos.2 hn)⟩
        (not_le_of_gt g.signature_pos)
  · simp [IsFiltered, h, IsFiltered_def.1 h.1]

lemma IsFiltered_iff_add {X Y : Chromosome} :
    (X + Y).IsFiltered p ↔ X.IsFiltered p ∧ Y.IsFiltered p := by
  induction Y using Finsupp.induction with
  | zero =>
    rw [add_zero]
    exact (and_iff_left_of_imp fun _ ↦ IsFiltered_zero).symm
  | single_add g' n f hg' hn hf =>
    rw [add_comm _ f, ← add_assoc, IsFiltered_add_single
      (Nat.one_le_iff_ne_zero.2 hn), hf, IsFiltered_add_single
      (Nat.one_le_iff_ne_zero.2 hn)]
    tauto

lemma IsFiltered_iff_nsmul {n : ℕ} (hn : n ≠ 0) :
    (n • X).IsFiltered p ↔ X.IsFiltered p := by
  induction n using Nat.twoStepInduction with
  | zero => tauto
  | one => rw [one_nsmul]
  | more m _ hm =>
    specialize hm (by omega)
    change ((m + 1 + 1) • X).IsFiltered p ↔ _
    rw [add_nsmul, one_nsmul, IsFiltered_iff_add, hm]
    tauto

variable (p) in
def LiftStable : Prop :=
  ∀ g : Gene, p g ↔ p ⟨g.rank + 1, g.type, Nat.le_add_left 1 g.rank⟩

lemma IsFiltered_iff_lift (hp : LiftStable p) :
    X.lift.IsFiltered p ↔ X.IsFiltered p := by
  constructor <;> intro h
  · induction X using Finsupp.induction
    · exact IsFiltered_zero
    · expose_names
      rw [map_add, IsFiltered_iff_add] at h
      specialize h_3 h.2
      refine IsFiltered_iff_add.2 ⟨?_, h_3⟩
      replace h := h.1
      simp only [lift, liftGene, smul_dite, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceDIte, smul_single, smul_eq_mul, mul_one, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        single_zero, sum_single_index] at h
      rw [IsFiltered_single h_2] at h ⊢
      exact (hp _).2 h
  · induction X using Finsupp.induction
    · exact IsFiltered_zero
    · expose_names
      rw [map_add, IsFiltered_iff_add]
      rw [IsFiltered_iff_add] at h
      refine ⟨?_, h_3 h.2⟩
      replace h := h.1
      simp only [lift, liftGene, smul_dite, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceDIte, smul_single, smul_eq_mul, mul_one, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        single_zero, sum_single_index]
      rw [IsFiltered_single h_2] at h ⊢
      exact (hp _).1 h

lemma IsFiltered_iff_iterate_lift {k : ℕ} (hp : LiftStable p) :
    (lift^[k] X).IsFiltered p ↔ X.IsFiltered p := by
  induction k with
  | zero => rfl
  | succ n hn => rwa [Function.iterate_succ_apply', IsFiltered_iff_lift hp]

variable (p) in
def varietyOfFilter : Variety where
  carrier := {X : Chromosome | X.IsFiltered p}
  add_mem' ha hb := IsFiltered_iff_add.2 ⟨ha, hb⟩
  zero_mem' := IsFiltered_zero

lemma mem_varietyOfFilter_iff :
  X ∈ varietyOfFilter p ↔ X.IsFiltered p := .rfl

lemma prime_varietyOfFilter (hp : LiftStable p) :
    (varietyOfFilter p).prime = varietyOfFilter p := by
  refine le_antisymm ?_ ?_ <;> intro x hx
  · rw [Variety.prime_def, AddSubmonoid.mem_map] at hx
    rcases hx with ⟨y, ⟨h1, h2⟩⟩
    rw [mem_varietyOfFilter_iff, ← h2]
    induction y using Finsupp.induction generalizing x
    · exact IsFiltered_zero
    · expose_names
      rw [mem_varietyOfFilter_iff, IsFiltered_iff_add] at h1
      rw [map_add, IsFiltered_iff_add]
      refine ⟨?_, h_2 h1.2 rfl⟩
      simp only [prime, primeGene, smul_dite, nsmul_zero, smul_single, smul_eq_mul, mul_one,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, single_zero, dite_eq_ite, ite_self, sum_single_index]
      split_ifs with h
      · exact IsFiltered_zero
      · rw [IsFiltered_single h_1] at h1 ⊢
        rw [hp]
        convert h1.1
        refine Nat.sub_add_cancel a.rank_pos
  · rw [Variety.prime_def, AddSubmonoid.mem_map]
    use x.lift
    refine ⟨?_, prime_lift_leftInverse x⟩
    exact (IsFiltered_iff_lift hp).2 hx

lemma prime_mem_varietyOfFilter {X : Chromosome} (hp : LiftStable p)
    (hX : X ∈ varietyOfFilter p) : X.prime ∈ varietyOfFilter p :=
  ((congrArg (prime X ∈ ·) (prime_varietyOfFilter hp).symm)).mpr ⟨X, ⟨hX, rfl⟩⟩

noncomputable def prime_on_varietyOfFilter (hp : LiftStable p) (X : varietyOfFilter p) :
    varietyOfFilter p := ⟨X.1.prime, prime_mem_varietyOfFilter hp X.2⟩

lemma prime_on_varietyOfFilter_iterate (hp : LiftStable p) (X : varietyOfFilter p) (k : ℕ) :
    ((prime_on_varietyOfFilter hp)^[k] X).1 = Chromosome.prime^[k] X := by
  unfold prime_on_varietyOfFilter
  induction k with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ n hn => simp_rw [Function.iterate_succ_apply', hn]

lemma prime_mem_varietyOfFilter_iterate {X : Chromosome} (hp : LiftStable p) {k : ℕ}
    (hX : X ∈ varietyOfFilter p) : Chromosome.prime^[k] X ∈ varietyOfFilter p := by
  convert ((prime_on_varietyOfFilter hp)^[k] ⟨X, hX⟩).2
  exact (prime_on_varietyOfFilter_iterate hp ⟨X, hX⟩ k).symm

lemma filter_mem_smul_varietyOfFilter (q : Gene → Prop) [DecidablePred q]
  {n : ℕ} (h : X ∈ n • (varietyOfFilter p)) :
    X.filter q ∈ n • (varietyOfFilter p) := by
  obtain ⟨Y, ⟨h1, h2 : n • Y = X⟩⟩ := h
  refine ⟨Y.filter q, IsFiltered_filter h1, (?_ : n • (Y.filter q) = X.filter q)⟩
  rw [← h2, filter_smul]

end IsFiltered

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

section nonpolarized

def IsNonPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type = .NonPolarized)

lemma IsNonPolarized_def {X : Chromosome} :
  X.IsNonPolarized ↔ X.filter (·.type = .NonPolarized) = X := IsFiltered_def

lemma IsNonPolarized_def' {X : Chromosome} :
  X.IsNonPolarized ↔ ∀ g ∈ X.support, g.type = .NonPolarized := IsFiltered_def'

lemma IsNonPolarized_zero : IsNonPolarized 0 := IsFiltered_zero

lemma IsNonPolarized_single {g : Gene} {n : ℕ} (hn : n ≠ 0) :
  IsNonPolarized (single g n) ↔ g.type = .NonPolarized := IsFiltered_single hn

lemma IsNonPolarized_filter {X : Chromosome} {q : Gene → Prop} [DecidablePred q]
  (h : X.IsNonPolarized) : IsNonPolarized (X.filter q) := IsFiltered_filter h

lemma IsNonPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsNonPolarized ↔ ε = .NonPolarized := by
  rw [Gene.ofRank_def, dif_neg (by omega)]
  exact IsNonPolarized_single Nat.one_ne_zero

lemma IsNonPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsNonPolarized ↔ X.IsNonPolarized ∧ Y.IsNonPolarized := IsFiltered_iff_add

lemma IsNonPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_nsmul hn

lemma IsNonPolarized_iff_lift {X : Chromosome} :
  X.lift.IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

lemma IsNonPolarized_iff_iterate_lift {X : Chromosome} {k : ℕ} :
  (lift^[k] X).IsNonPolarized ↔ X.IsNonPolarized :=
    IsFiltered_iff_iterate_lift (fun _ ↦ .rfl)

end nonpolarized

end Chromosome

namespace Variety

open Chromosome

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

section Lambda

def Lambda : Variety := varietyOfFilter (·.type = .NonPolarized)

lemma mem_Lambda_iff {X : Chromosome} :
  X ∈ Lambda ↔ IsNonPolarized X := mem_varietyOfFilter_iff

lemma mem_Lambda_iff_add {X Y : Chromosome} :
  (X + Y) ∈ Lambda ↔ X ∈ Lambda ∧ Y ∈ Lambda := IsNonPolarized_iff_add

lemma prime_Lambda : Lambda.prime = Lambda := prime_varietyOfFilter (fun _ ↦ .rfl)

lemma parityDecomp_mem_smul_Lambda {X : Chromosome} {n : ℕ} (h : X ∈ n • Lambda) :
  oddPart X ∈ n • Lambda ∧ evenPart X ∈ n • Lambda :=
  ⟨filter_mem_smul_varietyOfFilter (Odd ·.rank) h,
    filter_mem_smul_varietyOfFilter (Even ·.rank) h⟩

lemma parityDecomp_mem_Lambda {X : Chromosome} (h : X ∈ Lambda) :
    oddPart X ∈ Lambda ∧ evenPart X ∈ Lambda :=
  ⟨IsFiltered_filter h, IsFiltered_filter h⟩

lemma prime_mem_Lambda {X : Chromosome} (hX : X ∈ Lambda) : X.prime ∈ Lambda :=
  prime_mem_varietyOfFilter (fun _ ↦ .rfl) hX

noncomputable def prime_on_Lambda (X : Lambda) : Lambda := ⟨X.1.prime, prime_mem_Lambda X.2⟩

lemma prime_on_Lambda_iterate (X : Lambda) (k : ℕ) :
    (prime_on_Lambda^[k] X).1 = Chromosome.prime^[k] X :=
  prime_on_varietyOfFilter_iterate (fun _ ↦ .rfl) X k

lemma prime_mem_Lambda_iterate {X : Chromosome} (hX : X ∈ Lambda) {k : ℕ} :
    Chromosome.prime^[k] X ∈ Lambda :=
  prime_mem_varietyOfFilter_iterate (fun _ ↦ .rfl) hX

end Lambda

section Mix

def Mix (v : Variety × Variety) : Variety where
  carrier := {X : Chromosome | X.evenPart ∈ v.1 ∧ X.oddPart ∈ v.2}
  add_mem' ha hb := by
    simp only [Set.mem_setOf_eq, map_add]
    exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, zero_mem, and_self]

lemma mem_Mix_iff {X : Chromosome} {v : Variety × Variety} :
  X ∈ Mix v ↔ X.evenPart ∈ v.1 ∧ X.oddPart ∈ v.2 := .rfl

lemma prime_Mix_le {v : Variety × Variety} :
    (Mix v).prime ≤ Mix ⟨v.2.prime, v.1.prime⟩ := by
  intro x hx
  change x.evenPart ∈ v.2.prime ∧ x.oddPart ∈ v.1.prime
  obtain ⟨y, ⟨h1 : y.evenPart ∈ v.1 ∧ y.oddPart ∈ v.2, h2⟩⟩ := hx
  rw [← h2, evenPart_prime, oddPart_prime]
  exact ⟨⟨y.oddPart, ⟨h1.2, rfl⟩⟩, ⟨y.evenPart, ⟨h1.1, rfl⟩⟩⟩

lemma prime_Mix_eq {v : Variety × Variety}
    (hv1 : ∀ {x}, x ∈ v.1 → x.oddPart ∈ v.1 ∧ x.evenPart ∈ v.1)
    (hv2 : ∀ {x}, x ∈ v.2 → x.oddPart ∈ v.2 ∧ x.evenPart ∈ v.2) :
    (Mix v).prime = Mix ⟨v.2.prime, v.1.prime⟩ := by
  refine le_antisymm prime_Mix_le (fun x hx ↦ ?_)
  obtain ⟨⟨y₁, ⟨h11, h12⟩⟩, ⟨y₂, ⟨h21, h22⟩⟩⟩ := hx
  have eq1 : (oddPart y₁).prime = evenPart x := by
    apply_fun evenPart at h12
    rwa [y₁.parity_decomposition, map_add, map_add, ← oddPart_prime,
      ← evenPart_prime, evenPart_idempotent, evenPart_idempotent,
      evenPart_oddPart, add_zero, evenPart_prime] at h12
  have eq2 : (evenPart y₂).prime = oddPart x := by
    apply_fun oddPart at h22
    rwa [y₂.parity_decomposition, map_add, map_add, ← oddPart_prime,
      ← evenPart_prime, oddPart_idempotent, oddPart_idempotent, oddPart_evenPart,
      zero_add, oddPart_prime] at h22
  refine ⟨y₁.oddPart + y₂.evenPart, ⟨add_mem ⟨?_, ?_⟩ ⟨?_, ?_⟩, ?_⟩⟩
  · rw [evenPart_oddPart]; exact zero_mem _
  · rw [oddPart_idempotent]; exact (hv2 h11).1
  · rw [evenPart_idempotent]; exact (hv1 h21).2
  · rw [oddPart_evenPart]; exact zero_mem _
  · rw [map_add, eq1, eq2, add_comm]; exact x.parity_decomposition.symm

end Mix

lemma variety_prime_smul {v : Variety} {n : ℕ} :
    (n • v).prime = n • v.prime := by
  ext x; constructor <;> intro hx
  · obtain ⟨y, ⟨⟨z, ⟨hz, hyz : n • z = y⟩⟩, heq⟩⟩ := hx
    refine ⟨z.prime, ⟨?_, (?_ : n • z.prime = x)⟩⟩
    · use z
    · rw [← map_nsmul, hyz, heq]
  · obtain ⟨y, ⟨⟨z, ⟨hz, hyz⟩⟩, heq : n • y = x⟩⟩ := hx
    refine ⟨n • z, ⟨?_, ?_⟩⟩
    · use z, hz; rfl
    · rw [map_nsmul, hyz, heq]

noncomputable def Label : Fin 5 → Variety
  | 0 => Pi
  | 1 => Mix (Lambda, Pi)
  | 2 => Mix (Pi, Lambda)
  | 3 => Mix (2 • Lambda, Pi)
  | 4 => Mix (Pi, 2 • Lambda)

def Label.prime : Fin 5 → Fin 5
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3

lemma Label.prime_eq {i : Fin 5} :
    Variety.prime (Label i) = Label (Label.prime i) := by
  match i with
  | 0 => exact prime_Pi
  | 1 =>
    change (Mix (Lambda, Pi)).prime = Mix (Pi, Lambda)
    rw [prime_Mix_eq parityDecomp_mem_Lambda
      parityDecomp_mem_Pi, prime_Pi, prime_Lambda]
  | 2 =>
    change (Mix (Pi, Lambda)).prime = Mix (Lambda, Pi)
    rw [prime_Mix_eq parityDecomp_mem_Pi
      parityDecomp_mem_Lambda, prime_Pi, prime_Lambda]
  | 3 =>
    change (Mix (2 • Lambda, Pi)).prime = Mix (Pi, 2 • Lambda)
    rw [prime_Mix_eq parityDecomp_mem_smul_Lambda
      parityDecomp_mem_Pi, prime_Pi, variety_prime_smul, prime_Lambda]
  | 4 =>
    change (Mix (Pi, 2 • Lambda)).prime = Mix (2 • Lambda, Pi)
    rw [prime_Mix_eq parityDecomp_mem_Pi
      parityDecomp_mem_smul_Lambda, prime_Pi, variety_prime_smul, prime_Lambda]

lemma Label.prime_eq_iterate {i : Fin 5} {k : ℕ} :
    Label (prime^[k] i) = Variety.prime^[k] (Label i) := by
  induction k
  · rw [Function.iterate_zero, Function.iterate_zero]; rfl
  · expose_names
    nth_rw 1 [add_comm, Function.iterate_add_apply, Function.iterate_one,
      ← Label.prime_eq, h, Function.iterate_add_apply, Function.iterate_one]
    exact (Function.iterate_succ_apply' ..).symm

lemma prime_iterate_mem {k : ℕ} {X : Chromosome} {V : Variety} (hX : X ∈ V) :
    Chromosome.prime^[k] X ∈ Variety.prime^[k] V := by
  induction k generalizing V X
  · rwa [Function.iterate_zero, Function.iterate_zero]
  · expose_names
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact @h X.prime V.prime ⟨X, hX, rfl⟩

noncomputable def Label.of_mem_prime_iterate {i : Fin 5} {k : ℕ} {X : Chromosome}
    (hX : X ∈ Label i) : Label (Label.prime^[k] i) := by
  use Chromosome.prime^[k] X
  rw [Label.prime_eq_iterate]
  exact prime_iterate_mem hX

lemma Label.prime_iterate_zero {k : ℕ} : Label.prime^[k] 0 = 0 :=
  Function.iterate_fixed rfl k

end Variety
