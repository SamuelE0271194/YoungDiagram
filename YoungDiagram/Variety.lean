import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise
import YoungDiagram.Chromosome

noncomputable def liftGene (g : Gene) : Chromosome :=
  Gene.ofRank (g.rank + 1) g.type

abbrev variety := AddSubmonoid Chromosome

noncomputable def variety.prime (v : variety) : variety :=
  v.map Chromosome.prime

lemma variety.prime_def (v : variety) :
  v.prime = v.map Chromosome.prime := rfl

open Finsupp Pointwise

namespace Chromosome

/- Comment: tons of Mathlib lemmas rely on partial order for no reason.
For example `Finsupp.sum_le_sum`, which is obviously still true under pre-order.
These lemmas could make proving a lot less painful. A pull request in mathlib
is already opened to address the issue. For the time being we'll just use induction here.-/
lemma filtered_sig_leq (X : Chromosome) (p : Gene → Prop) [DecidablePred p] :
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

section lift

noncomputable def lift : Chromosome →+ Chromosome where
  toFun c := c.sum (fun g count ↦ count • liftGene g)
  map_zero' := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ zero_nsmul _)
    fun _ _ _ ↦ add_nsmul ..

abbrev below (X : Chromosome) (k : ℕ) : Chromosome := X.filter (·.rank ≤ k)

abbrev above (X : Chromosome) (k : ℕ) : Chromosome := X.filter (k < ·.rank)

lemma rankDecomposition (X : Chromosome) (k : ℕ) :
    X = X.below k + X.above k := by
  simp [below, above]
  conv =>
    enter [2, 2, 1, a]
    rw [lt_iff_not_ge]
  rw [filter_pos_add_filter_neg]

lemma prime_elim (X : Chromosome) (k : ℕ) :
    prime^[k] X = prime^[k] (X.above k) := by
  nth_rw 1 [rankDecomposition X k]
  simp only [iterate_map_add, add_eq_right]
  induction X using Finsupp.induction with
  | zero => simp [below, filter_zero]
  | single_add g n f hg hn hf =>
    simp [below]
    by_cases hg_rank : g.rank ≤ k
    · rw [filter_single_of_pos, ← Gene.ofRank_eq_gene', iterate_map_nsmul]
      · refine ⟨?_, hf⟩
        rw [IsAddTorsionFree.nsmul_eq_zero_iff, prime_ofRank_it,
          Nat.sub_eq_zero_of_le hg_rank, Gene.ofRank_zero]
        exact Or.inl rfl
      exact hg_rank
    · rw [filter_single_of_neg, iterate_map_zero]
      · exact ⟨rfl, hf⟩
      exact hg_rank

lemma prime_lift_LeftInverse : Function.LeftInverse prime lift := by
  intro x
  induction x using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add a m f ha hm hf =>
    rw [map_add, map_add, hf, add_left_inj]
    simp [prime, lift, liftGene, primeGene]
    split_ifs with h
    · rw [← Gene.ofRank_eq_gene', h, Gene.ofRank_zero, smul_zero]
    · rfl

lemma prime_lift_LeftInverse_it (k : ℕ) :
    Function.LeftInverse prime^[k] lift^[k] :=
  Function.LeftInverse.iterate prime_lift_LeftInverse k

end lift

section IsFiltered

variable {p : Gene → Prop} [DecidablePred p] {X : Chromosome}

variable (p X) in
def IsFiltered : Prop := X.filter p = X

lemma IsFiltered_def : X.IsFiltered p ↔ X.filter p = X := .rfl

lemma IsFiltered_def' : X.IsFiltered p ↔ ∀ g ∈ X.support, p g := by
  simp [IsFiltered_def, filter_eq_self_iff]

lemma IsFiltered_zero : IsFiltered p 0 := by
  simp only [IsFiltered, filter_zero]

lemma IsFiltered_single {g : Gene} : IsFiltered p (single g 1) ↔ p g := by
  rw [IsFiltered_def', support_single_ne_zero _ Nat.one_ne_zero]
  exact List.forall_mem_singleton

lemma IsFiltered_add_single {g : Gene} {n : ℕ} (hn : 1 ≤ n) :
    IsFiltered p (X + single g n) ↔ X.IsFiltered p ∧ p g := by
  constructor <;> intro h
  · by_cases hg : p g
    · simp [IsFiltered, hg] at h
      exact ⟨h, hg⟩
    · simp [IsFiltered, hg] at h
      apply_fun signature at h
      have := h ▸ (filtered_sig_leq X p)
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
      simp [lift, liftGene] at h
      rw [← smul_single_one, IsFiltered_iff_nsmul h_2, IsFiltered_single] at h ⊢
      exact (hp _).2 h
  · induction X using Finsupp.induction
    · exact IsFiltered_zero
    · expose_names
      rw [map_add, IsFiltered_iff_add]
      rw [IsFiltered_iff_add] at h
      refine ⟨?_, h_3 h.2⟩
      replace h := h.1
      simp [lift, liftGene]
      rw [← smul_single_one, IsFiltered_iff_nsmul h_2, IsFiltered_single] at h ⊢
      exact (hp _).1 h

variable (p) in
def varietyOfFilter : variety where
  carrier := {X : Chromosome | X.IsFiltered p}
  add_mem' ha hb := IsFiltered_iff_add.2 ⟨ha, hb⟩
  zero_mem' := IsFiltered_zero

lemma mem_varietyOfFilter_iff {X : Chromosome} :
  X ∈ varietyOfFilter p ↔ X.IsFiltered p := .rfl

lemma prime_varietyOfFilter (hp : LiftStable p) :
    (varietyOfFilter p).prime = varietyOfFilter p := by
  refine le_antisymm ?_ ?_ <;> intro x hx
  · rw [variety.prime_def, AddSubmonoid.mem_map] at hx
    rcases hx with ⟨y, ⟨h1, h2⟩⟩
    rw [mem_varietyOfFilter_iff, ← h2]
    induction y using Finsupp.induction generalizing x
    · exact IsFiltered_zero
    · expose_names
      rw [mem_varietyOfFilter_iff, IsFiltered_iff_add] at h1
      rw [map_add, IsFiltered_iff_add]
      refine ⟨?_, h_2 h1.2 rfl⟩
      simp [prime, primeGene]
      split_ifs with h
      · exact IsFiltered_zero
      · rw [← smul_single_one, IsFiltered_iff_nsmul h_1, IsFiltered_single] at h1 ⊢
        rw [hp]
        convert h1.1
        refine Nat.sub_add_cancel a.rank_pos
  · rw [variety.prime_def, AddSubmonoid.mem_map]
    use x.lift
    refine ⟨?_, prime_lift_LeftInverse x⟩
    exact (IsFiltered_iff_lift hp).2 hx

end IsFiltered

section parity

def o : Chromosome →+ Chromosome where
  toFun c := c.filter (Odd ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

def e : Chromosome →+ Chromosome where
  toFun c := c.filter (Even ·.rank)
  map_zero' := filter_zero _
  map_add' _ _ := filter_add

lemma e_it {X : Chromosome} : e (e X) = e X := by
  refine (filter_eq_self_iff (Even ·.rank) (filter (Even ·.rank) X)).2 ?_
  intro _ hx
  by_contra!
  exact hx (filter_apply_neg _ X this)

lemma o_it {X : Chromosome} : o (o X) = o X := by
  refine (filter_eq_self_iff (Odd ·.rank) (filter (Odd ·.rank) X)).2 ?_
  intro _ hx
  by_contra!
  exact hx (filter_apply_neg _ X this)

lemma parityDecomposition (X : Chromosome) : X = X.o + X.e := by
  simp [o, e]
  conv =>
    enter [2, 2, 1, a]
    rw [← Nat.not_odd_iff_even]
  rw [filter_pos_add_filter_neg]

lemma e_single {g : Gene} : e (single g 1) =
    if Even g.rank then single g 1 else 0 := by
  split_ifs with h
  · exact filter_single_of_pos _ h
  · exact filter_single_of_neg _ h

lemma o_single {g : Gene} : o (single g 1) =
    if Even g.rank then 0 else single g 1 := by
  split_ifs with h
  · exact filter_single_of_neg _ <| Nat.not_odd_iff_even.2 h
  · exact filter_single_of_pos _ <| Nat.not_even_iff_odd.1 h

lemma e_prime {X : Chromosome} : X.prime.e = X.o.prime := by
  induction X using Finsupp.induction
  · repeat rw [map_zero]
  · expose_names
    repeat rw [map_add]
    rw [h_2, add_left_inj, ← smul_single_one, map_nsmul, map_nsmul,
      map_nsmul, map_nsmul, nsmul_right_inj h_1, o_single]
    split_ifs with ha
    · simp [prime, primeGene]
      split_ifs
      · exact map_zero _
      · simp [e_single, Nat.even_add_one.1 ((Nat.sub_add_cancel a.rank_pos) ▸ ha)]
    · simp [prime, primeGene]
      split_ifs
      · exact map_zero _
      · simp [e_single, (Nat.even_sub a.rank_pos).2 <|
          (iff_false_right Nat.not_even_one).2 ha]

lemma o_prime {X : Chromosome} : X.prime.o = X.e.prime := by
  have := X.prime.parityDecomposition
  nth_rw 1 [X.parityDecomposition, map_add, e_prime, add_comm,
    add_left_inj] at this
  exact this.symm

lemma o_e_eq_zero {X : Chromosome} : o (e X) = 0 := by
  simp [o, e, filter_eq_zero_iff, filter_apply]
  intro _ ho he
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff, ho] at he
  tauto

lemma e_o_eq_zero {X : Chromosome} : e (o X) = 0 := by
  simp [o, e, filter_eq_zero_iff, filter_apply]
  intro _ he ho
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff, ho] at he
  tauto

end parity

section polarized

def IsPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type ≠ .NonPolarized)

lemma IsPolarized_def {X : Chromosome} :
  X.IsPolarized ↔ X.filter (·.type ≠ .NonPolarized) = X := IsFiltered_def

lemma IsPolarized_def' {X : Chromosome} :
  X.IsPolarized ↔ ∀ g ∈ X.support, g.type ≠ .NonPolarized := IsFiltered_def'

lemma IsPolarized_zero : IsPolarized 0 := IsFiltered_zero

lemma IsPolarized_single {g : Gene} :
  IsPolarized (single g 1) ↔ g.type ≠ .NonPolarized := IsFiltered_single

lemma IsPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank_def]
  split_ifs
  · omega
  · exact IsPolarized_single

lemma IsPolarized_ofRank' {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank' k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank'_def, IsPolarized_ofRank hk,
    GeneType.neg_one_pow_smul]
  split_ifs
  · rfl
  · exact GeneType.nonpolarized_iff_neg_non.symm

lemma IsPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsPolarized ↔ X.IsPolarized ∧ Y.IsPolarized := IsFiltered_iff_add

lemma IsPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsPolarized ↔ X.IsPolarized := IsFiltered_iff_nsmul hn

lemma IsPolarized_iff_lift {X : Chromosome} :
  X.lift.IsPolarized ↔ X.IsPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

end polarized

section nonpolarized

def IsNonPolarized (X : Chromosome) : Prop := X.IsFiltered (·.type = .NonPolarized)

lemma IsNonPolarized_def {X : Chromosome} :
  X.IsNonPolarized ↔ X.filter (·.type = .NonPolarized) = X := IsFiltered_def

lemma IsNonPolarized_def' {X : Chromosome} :
  X.IsNonPolarized ↔ ∀ g ∈ X.support, g.type = .NonPolarized := IsFiltered_def'

lemma IsNonPolarized_zero : IsNonPolarized 0 := IsFiltered_zero

lemma IsNonPolarized_single {g : Gene} :
  IsNonPolarized (single g 1) ↔ g.type = .NonPolarized := IsFiltered_single

lemma IsNonPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsNonPolarized ↔ ε = .NonPolarized := by
  rw [Gene.ofRank_def]
  split_ifs
  · omega
  · exact IsNonPolarized_single

lemma IsNonPolarized_iff_add {X Y : Chromosome} :
  (X + Y).IsNonPolarized ↔ X.IsNonPolarized ∧ Y.IsNonPolarized := IsFiltered_iff_add

lemma IsNonPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
  (n • X).IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_nsmul hn

lemma IsNonPolarized_iff_lift {X : Chromosome} :
  X.lift.IsNonPolarized ↔ X.IsNonPolarized := IsFiltered_iff_lift (fun _ ↦ .rfl)

end nonpolarized

section Pi

def Pi : variety := varietyOfFilter (·.type ≠ .NonPolarized)

lemma mem_Pi_iff {X : Chromosome} :
  X ∈ Pi ↔ X.IsPolarized := mem_varietyOfFilter_iff

lemma prime_Pi : Pi.prime = Pi := prime_varietyOfFilter (fun _ ↦ .rfl)

lemma Pi_closed_under_parityDecomp' {X : Chromosome} {n : ℕ} (h : X ∈ n • Pi) :
    o X ∈ n • Pi ∧ e X ∈ n • Pi := by
  rw [AddSubmonoid.mem_smul_pointwise_iff_exists,
    AddSubmonoid.mem_smul_pointwise_iff_exists]
  obtain ⟨Y, ⟨h1, h2 : n • Y = X⟩⟩ := h
  constructor
  · refine ⟨Y.o, ?_, ?_⟩
    · have : Y.o.support ⊆ Y.support := by simp [o]
      rw [mem_Pi_iff, IsPolarized_def']
      rw [SetLike.mem_coe, mem_Pi_iff, IsPolarized_def'] at h1
      intro g hg
      exact h1 _ (this hg)
    · apply_fun o at h2
      rwa [map_nsmul] at h2
  · refine ⟨Y.e, ?_, ?_⟩
    · have : Y.e.support ⊆ Y.support := by simp [e]
      rw [mem_Pi_iff, IsPolarized_def']
      rw [SetLike.mem_coe, mem_Pi_iff, IsPolarized_def'] at h1
      intro g hg
      exact h1 _ (this hg)
    · apply_fun e at h2
      rwa [map_nsmul] at h2

lemma Pi_closed_under_parityDecomp {X : Chromosome} (h : X ∈ Pi) :
    o X ∈ Pi ∧ e X ∈ Pi := by
  convert @Pi_closed_under_parityDecomp' X 1 (by rwa [one_smul])
  <;> exact (MulAction.one_smul _).symm

end Pi

section Lambda

def Lambda : variety := varietyOfFilter (·.type = .NonPolarized)

lemma mem_Lambda_iff {X : Chromosome} :
  X ∈ Lambda ↔ X.IsNonPolarized := mem_varietyOfFilter_iff

lemma prime_Lambda : Lambda.prime = Lambda := prime_varietyOfFilter (fun _ ↦ .rfl)

lemma Lambda_closed_under_parityDecomp' {X : Chromosome} {n : ℕ} (h : X ∈ n • Lambda) :
    o X ∈ n • Lambda ∧ e X ∈ n • Lambda := by
  rw [AddSubmonoid.mem_smul_pointwise_iff_exists,
    AddSubmonoid.mem_smul_pointwise_iff_exists]
  obtain ⟨Y, ⟨h1, h2 : n • Y = X⟩⟩ := h
  constructor
  · refine ⟨Y.o, ?_, ?_⟩
    · have : Y.o.support ⊆ Y.support := by simp [o]
      rw [mem_Lambda_iff, IsNonPolarized_def']
      rw [SetLike.mem_coe, mem_Lambda_iff, IsNonPolarized_def'] at h1
      intro g hg
      exact h1 _ (this hg)
    · apply_fun o at h2
      rwa [map_nsmul] at h2
  · refine ⟨Y.e, ?_, ?_⟩
    · have : Y.e.support ⊆ Y.support := by simp [e]
      rw [mem_Lambda_iff, IsNonPolarized_def']
      rw [SetLike.mem_coe, mem_Lambda_iff, IsNonPolarized_def'] at h1
      intro g hg
      exact h1 _ (this hg)
    · apply_fun e at h2
      rwa [map_nsmul] at h2

lemma Lambda_closed_under_parityDecomp {X : Chromosome} (h : X ∈ Lambda) :
    o X ∈ Lambda ∧ e X ∈ Lambda := by
  convert @Lambda_closed_under_parityDecomp' X 1 (by rwa [one_smul])
  <;> exact (MulAction.one_smul _).symm

end Lambda

section Mix

def Mix (v : variety × variety) : variety where
  carrier := {X : Chromosome | X.e ∈ v.1 ∧ X.o ∈ v.2}
  add_mem' ha hb := by
    simp only [Set.mem_setOf_eq, map_add]
    exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, zero_mem, and_self]

lemma mem_Mix_iff {X : Chromosome} {v : variety × variety} :
  X ∈ Mix v ↔ X.e ∈ v.1 ∧ X.o ∈ v.2 := .rfl

lemma prime_Mix_1 {v : variety × variety} :
    (Mix v).prime ≤ Mix ⟨v.2.prime, v.1.prime⟩ := by
  intro x hx
  change x.e ∈ v.2.prime ∧ x.o ∈ v.1.prime
  obtain ⟨y, ⟨h1 : y.e ∈ v.1 ∧ y.o ∈ v.2, h2⟩⟩ := hx
  rw [← h2, e_prime, o_prime]
  exact ⟨⟨y.o, ⟨h1.2, rfl⟩⟩, ⟨y.e, ⟨h1.1, rfl⟩⟩⟩

lemma prime_Mix_2 {v : variety × variety}
    (hv1 : ∀ {x}, x ∈ v.1 → x.o ∈ v.1 ∧ x.e ∈ v.1)
    (hv2 : ∀ {x}, x ∈ v.2 → x.o ∈ v.2 ∧ x.e ∈ v.2) :
    (Mix v).prime = Mix ⟨v.2.prime, v.1.prime⟩ := by
  refine le_antisymm prime_Mix_1 (fun x hx ↦ ?_)
  obtain ⟨⟨y₁, ⟨h11, h12⟩⟩, ⟨y₂, ⟨h21, h22⟩⟩⟩ := hx
  have eq1 : (o y₁).prime = e x := by
    apply_fun e at h12
    rwa [y₁.parityDecomposition, map_add, map_add, ← o_prime,
      ← e_prime, e_it, e_it, e_o_eq_zero, add_zero, e_prime] at h12
  have eq2 : (e y₂).prime = o x := by
    apply_fun o at h22
    rwa [y₂.parityDecomposition, map_add, map_add, ← o_prime,
      ← e_prime, o_it, o_it, o_e_eq_zero, zero_add, o_prime] at h22
  refine ⟨y₁.o + y₂.e, ⟨add_mem ⟨?_, ?_⟩ ⟨?_, ?_⟩, ?_⟩⟩
  · rw [e_o_eq_zero]; exact zero_mem _
  · rw [o_it]; exact (hv2 h11).1
  · rw [e_it]; exact (hv1 h21).2
  · rw [o_e_eq_zero]; exact zero_mem _
  · rw [map_add, eq1, eq2, add_comm]; exact x.parityDecomposition.symm

end Mix

lemma variety_prime_smul {v : variety} {n : ℕ} :
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

end Chromosome

open Chromosome

noncomputable def VarietyLabel : Fin 5 → variety
  | 0 => Pi
  | 1 => Mix (Lambda, Pi)
  | 2 => Mix (Pi, Lambda)
  | 3 => Mix (2 • Lambda, Pi)
  | 4 => Mix (Pi, 2 • Lambda)

def VarietyLabel.prime : Fin 5 → Fin 5
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3

lemma VarietyLabel.prime_eq_prime {i : Fin 5} :
    variety.prime (VarietyLabel i) = VarietyLabel (VarietyLabel.prime i) := by
  match i with
  | 0 => exact prime_Pi
  | 1 =>
    change (Mix (Lambda, Pi)).prime = Mix (Pi, Lambda)
    rw [prime_Mix_2 Lambda_closed_under_parityDecomp Pi_closed_under_parityDecomp,
      prime_Pi, prime_Lambda]
  | 2 =>
    change (Mix (Pi, Lambda)).prime = Mix (Lambda, Pi)
    rw [prime_Mix_2 Pi_closed_under_parityDecomp Lambda_closed_under_parityDecomp,
      prime_Pi, prime_Lambda]
  | 3 =>
    change (Mix (2 • Lambda, Pi)).prime = Mix (Pi, 2 • Lambda)
    rw [prime_Mix_2 Lambda_closed_under_parityDecomp' Pi_closed_under_parityDecomp,
      prime_Pi, variety_prime_smul, prime_Lambda]
  | 4 =>
    change (Mix (Pi, 2 • Lambda)).prime = Mix (2 • Lambda, Pi)
    rw [prime_Mix_2 Pi_closed_under_parityDecomp Lambda_closed_under_parityDecomp',
      prime_Pi, variety_prime_smul, prime_Lambda]

noncomputable def VarietyLabel.of_mem_prime_iter {i : Fin 5} {k : ℕ} {X : Chromosome}
  (hX : X ∈ VarietyLabel i) :
    VarietyLabel (VarietyLabel.prime^[k] i) := by
  use Chromosome.prime^[k] X
  induction k generalizing i X
  · rwa [Function.iterate_zero, Function.iterate_zero]
  · expose_names
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine @h (prime i) X.prime ?_
    rw [← VarietyLabel.prime_eq_prime]
    refine ⟨X, hX, rfl⟩
