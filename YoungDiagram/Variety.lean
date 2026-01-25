import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise
import YoungDiagram.Chromosome

noncomputable def liftGene (g : Gene) : Chromosome :=
  Gene.ofRank (g.rank + 1) g.type

abbrev variety := AddSubmonoid Chromosome

noncomputable def variety.prime (v : variety) : variety :=
  v.map Chromosome.prime

lemma variety.prime_def (v : variety) :
  v.prime = v.map Chromosome.prime := rfl

open Finsupp

namespace Chromosome

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

abbrev o (X : Chromosome) : Chromosome := X.filter (Odd  ·.rank)
abbrev e (X : Chromosome) : Chromosome := X.filter (Even ·.rank)

def IsOdd (X : Chromosome) : Prop  := X.o = X

lemma IsOdd_def {X : Chromosome} :
  X.IsOdd ↔ X.filter (Odd  ·.rank) = X := .rfl

def IsEven (X : Chromosome) : Prop := X.e = X

lemma IsEven_def {X : Chromosome} :
  X.IsEven ↔ X.filter (Even ·.rank) = X := .rfl

lemma parityDecomposition (X : Chromosome) : X = X.o + X.e := by
  simp [o, e]
  conv =>
    enter [2, 2, 1, a]
    rw [← Nat.not_odd_iff_even]
  rw [filter_pos_add_filter_neg]

/- Comment: tons of Mathlib lemmas rely on partial order for no reason.
For example `Finsupp.sum_le_sum`, which is obviously still true under pre-order.
These lemmas could make proving a lot less painful. A pull request in mathlib
is already opened to address the issue. For the time being we'll just leave a
sorry here.-/
lemma filtered_sig_leq (X : Chromosome) (p : Gene → Prop) [DecidablePred p] :
    signature (X.filter p) ≤ X.signature := by
  sorry

section polarized

def IsPolarized (X : Chromosome) : Prop :=
  X.filter (·.type ≠ .NonPolarized) = X

lemma IsPolarized_def {X : Chromosome} :
  X.IsPolarized ↔ X.filter (·.type ≠ .NonPolarized) = X := .rfl

lemma IsPolarized_zero : IsPolarized 0 := by
  simp only [IsPolarized_def, ne_eq, filter_zero]

lemma IsPolarized_single {g : Gene} :
    IsPolarized (single g 1) ↔ g.type ≠ .NonPolarized := by
  simp [IsPolarized_def]
  by_cases hg : g.type = .NonPolarized
  · constructor <;> intro h
    · symm at h
      rw [filter_single_of_neg _ (fun a ↦ a hg), single_eq_zero] at h
      tauto
    · tauto
  · exact ⟨fun _ ↦ hg, fun _ ↦ filter_single_of_pos _ hg⟩

lemma IsPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank_def]
  split_ifs
  · omega
  · rw [IsPolarized_single]

lemma IsPolarized_ofRank' {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank' k ε).IsPolarized ↔ ε ≠ .NonPolarized := by
  rw [Gene.ofRank'_def, IsPolarized_ofRank hk,
    GeneType.neg_one_pow_smul]
  split_ifs
  · rfl
  · exact GeneType.nonpolarized_iff_neg_non.symm

lemma IsPolarized_add_single {g : Gene} {n : ℕ} (hn : 1 ≤ n) {X : Chromosome} :
    IsPolarized (X + single g n) ↔ X.IsPolarized ∧ g.type ≠ .NonPolarized := by
  constructor <;> intro h
  · by_cases hg : g.type = .NonPolarized
    · simp [IsPolarized_def, hg] at h
      apply_fun signature at h
      have := h ▸ (filtered_sig_leq X (·.type ≠ GeneType.NonPolarized))
      rw [map_add, signature_single g.rank_pos,
        add_le_iff_nonpos_right, Prod.le_def] at this
      change n * g.signature.1 ≤ 0 ∧ n * g.signature.2 ≤ 0 at this
      exact absurd ⟨nonpos_of_mul_nonpos_right this.1 (Rat.natCast_pos.2 hn),
        nonpos_of_mul_nonpos_right this.2 (Rat.natCast_pos.2 hn)⟩
        (not_le_of_gt g.signature_pos)
    · simp [IsPolarized_def, hg] at h
      exact ⟨h, hg⟩
  · simp [IsPolarized_def, h, IsPolarized_def.1 h.1]

lemma IsPolarized_iff_add {X Y : Chromosome} :
    (X + Y).IsPolarized ↔ X.IsPolarized ∧ Y.IsPolarized := by
  induction Y using Finsupp.induction with
  | zero =>
    rw [add_zero]
    exact (and_iff_left_of_imp fun _ ↦ IsPolarized_zero).symm
  | single_add g' n f hg' hn hf =>
    rw [add_comm _ f, ← add_assoc, IsPolarized_add_single
      (Nat.one_le_iff_ne_zero.2 hn), hf, IsPolarized_add_single
      (Nat.one_le_iff_ne_zero.2 hn)]
    tauto

lemma IsPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
    (n • X).IsPolarized ↔ X.IsPolarized := by
  induction n using Nat.twoStepInduction with
  | zero => tauto
  | one => rw [one_nsmul]
  | more m _ hm =>
    specialize hm (by omega)
    change ((m + 1 + 1) • X).IsPolarized ↔ _
    rw [add_nsmul, one_nsmul, IsPolarized_iff_add, hm]
    tauto

lemma IsPolarized_iff_lift {X : Chromosome} :
    X.lift.IsPolarized ↔ X.IsPolarized := by
  constructor <;> intro h
  · induction X using Finsupp.induction
    · exact IsPolarized_zero
    · expose_names
      rw [map_add, IsPolarized_iff_add] at h
      specialize h_3 h.2
      refine IsPolarized_iff_add.2 ⟨?_, h_3⟩
      replace h := h.1
      simp [lift, liftGene] at h
      rwa [← smul_single_one, IsPolarized_iff_nsmul h_2, IsPolarized_single] at h ⊢
  · induction X using Finsupp.induction
    · exact IsPolarized_zero
    · expose_names
      rw [map_add, IsPolarized_iff_add]
      rw [IsPolarized_iff_add] at h
      refine ⟨?_, h_3 h.2⟩
      replace h := h.1
      simp [lift, liftGene]
      rwa [← smul_single_one, IsPolarized_iff_nsmul h_2, IsPolarized_single] at h ⊢

end polarized

section nonpolarized

def IsNonPolarized (X : Chromosome) : Prop :=
  X.filter (·.type = .NonPolarized) = X

lemma IsNonPolarized_def {X : Chromosome} :
  X.IsNonPolarized ↔ X.filter (·.type = .NonPolarized) = X := .rfl

lemma IsNonPolarized_zero : IsNonPolarized 0 := by
  simp only [IsNonPolarized_def, filter_zero]

lemma IsNonPolarized_single {g : Gene} :
    IsNonPolarized (single g 1) ↔ g.type = .NonPolarized := by
  simp [IsNonPolarized_def]
  by_cases hg : g.type = .NonPolarized
  · exact ⟨fun _ ↦ hg, fun _ ↦ filter_single_of_pos _ hg⟩
  · constructor <;> intro h
    · symm at h
      rw [filter_single_of_neg, single_eq_zero] at h <;> tauto
    · tauto

lemma IsNonPolarized_ofRank {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) :
    (Gene.ofRank k ε).IsNonPolarized ↔ ε = .NonPolarized := by
  rw [Gene.ofRank_def]
  split_ifs
  · omega
  · rw [IsNonPolarized_single]

lemma IsNonPolarized_add_single {g : Gene} {n : ℕ} (hn : 1 ≤ n) {X : Chromosome} :
    IsNonPolarized (X + single g n) ↔ X.IsNonPolarized ∧ g.type = .NonPolarized := by
  constructor <;> intro h
  · by_cases hg : g.type = .NonPolarized
    · simp [IsNonPolarized_def, hg] at h
      exact ⟨h, hg⟩
    · simp [IsNonPolarized_def, hg] at h
      apply_fun signature at h
      have := h ▸ (filtered_sig_leq X (·.type = GeneType.NonPolarized))
      rw [map_add, signature_single g.rank_pos,
        add_le_iff_nonpos_right, Prod.le_def] at this
      change n * g.signature.1 ≤ 0 ∧ n * g.signature.2 ≤ 0 at this
      exact absurd ⟨nonpos_of_mul_nonpos_right this.1 (Rat.natCast_pos.2 hn),
        nonpos_of_mul_nonpos_right this.2 (Rat.natCast_pos.2 hn)⟩
        (not_le_of_gt g.signature_pos)
  · simp [IsNonPolarized_def, h, IsNonPolarized_def.1 h.1]

lemma IsNonPolarized_iff_add {X Y : Chromosome} :
    (X + Y).IsNonPolarized ↔ X.IsNonPolarized ∧ Y.IsNonPolarized := by
  induction Y using Finsupp.induction with
  | zero =>
    rw [add_zero]
    exact (and_iff_left_of_imp fun _ ↦ IsNonPolarized_zero).symm
  | single_add g' n f hg' hn hf =>
    rw [add_comm _ f, ← add_assoc, IsNonPolarized_add_single
      (Nat.one_le_iff_ne_zero.2 hn), hf, IsNonPolarized_add_single
      (Nat.one_le_iff_ne_zero.2 hn)]
    tauto

lemma IsNonPolarized_iff_nsmul {X : Chromosome} {n : ℕ} (hn : n ≠ 0) :
    (n • X).IsNonPolarized ↔ X.IsNonPolarized := by
  induction n using Nat.twoStepInduction with
  | zero => tauto
  | one => rw [one_nsmul]
  | more m _ hm =>
    specialize hm (by omega)
    change ((m + 1 + 1) • X).IsNonPolarized ↔ _
    rw [add_nsmul, one_nsmul, IsNonPolarized_iff_add, hm]
    tauto

lemma IsNonPolarized_iff_lift {X : Chromosome} :
    X.lift.IsNonPolarized ↔ X.IsNonPolarized := by
  constructor <;> intro h
  · induction X using Finsupp.induction
    · exact IsNonPolarized_zero
    · expose_names
      rw [map_add, IsNonPolarized_iff_add] at h
      specialize h_3 h.2
      refine IsNonPolarized_iff_add.2 ⟨?_, h_3⟩
      replace h := h.1
      simp [lift, liftGene] at h
      rwa [← smul_single_one, IsNonPolarized_iff_nsmul h_2, IsNonPolarized_single] at h ⊢
  · induction X using Finsupp.induction
    · exact IsNonPolarized_zero
    · expose_names
      rw [map_add, IsNonPolarized_iff_add]
      rw [IsNonPolarized_iff_add] at h
      refine ⟨?_, h_3 h.2⟩
      replace h := h.1
      simp [lift, liftGene]
      rwa [← smul_single_one, IsNonPolarized_iff_nsmul h_2, IsNonPolarized_single] at h ⊢

end nonpolarized

def Pi : variety where
  carrier := {X : Chromosome | IsPolarized X}
  add_mem' ha hb := IsPolarized_iff_add.2 ⟨ha, hb⟩
  zero_mem' := IsPolarized_zero

lemma mem_Pi_iff {X : Chromosome} : X ∈ Pi ↔ X.IsPolarized := .rfl

lemma prime_Pi : Pi.prime = Pi := by
  refine le_antisymm ?_ ?_ <;> intro x hx
  · rw [variety.prime_def, AddSubmonoid.mem_map] at hx
    rcases hx with ⟨y, ⟨h1, h2⟩⟩
    rw [mem_Pi_iff, ← h2]
    induction y using Finsupp.induction generalizing x
    · exact IsPolarized_zero
    · expose_names
      rw [mem_Pi_iff, IsPolarized_iff_add, ← @mem_Pi_iff f] at h1
      rw [map_add, IsPolarized_iff_add]
      refine ⟨?_, @h_2 (prime f) h1.2 rfl⟩
      simp [prime, primeGene]
      split_ifs
      · exact IsPolarized_zero
      · rw [← smul_single_one, IsPolarized_iff_nsmul h_1,
          IsPolarized_single] at h1 ⊢
        exact h1.1
  · rw [variety.prime_def, AddSubmonoid.mem_map]
    use x.lift
    refine ⟨mem_Pi_iff.2 <| IsPolarized_iff_lift.2 <|
      mem_Pi_iff.1 hx, prime_lift_LeftInverse x⟩

def Lambda : variety where
  carrier := {X : Chromosome | IsNonPolarized X}
  add_mem' ha hb := IsNonPolarized_iff_add.2 ⟨ha, hb⟩
  zero_mem' := IsNonPolarized_zero

lemma mem_Lambda_iff {X : Chromosome} : X ∈ Lambda ↔ X.IsNonPolarized := .rfl

lemma prime_Lambda : Lambda.prime = Lambda := by
  refine le_antisymm ?_ ?_ <;> intro x hx
  · rw [variety.prime_def, AddSubmonoid.mem_map] at hx
    rcases hx with ⟨y, ⟨h1, h2⟩⟩
    rw [mem_Lambda_iff, ← h2]
    induction y using Finsupp.induction generalizing x
    · exact IsNonPolarized_zero
    · expose_names
      rw [mem_Lambda_iff, IsNonPolarized_iff_add, ← @mem_Lambda_iff f] at h1
      rw [map_add, IsNonPolarized_iff_add]
      refine ⟨?_, @h_2 (prime f) h1.2 rfl⟩
      simp [prime, primeGene]
      split_ifs
      · exact IsNonPolarized_zero
      · rw [← smul_single_one, IsNonPolarized_iff_nsmul h_1,
          IsNonPolarized_single] at h1 ⊢
        exact h1.1
  · rw [variety.prime_def, AddSubmonoid.mem_map]
    use x.lift
    refine ⟨mem_Lambda_iff.2 <| IsNonPolarized_iff_lift.2 <|
      mem_Lambda_iff.1 hx, prime_lift_LeftInverse x⟩

def Mix (v : variety × variety) : variety where
  carrier := {X : Chromosome | X.e ∈ v.1 ∧ X.o ∈ v.2}
  add_mem' ha hb := by
    simp at *
    exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := by simp [filter_zero]

lemma mem_Mix_iff {X : Chromosome} {v : variety × variety} :
  X ∈ Mix v ↔ X.e ∈ v.1 ∧ X.o ∈ v.2 := .rfl

end Chromosome

open Chromosome Pointwise

noncomputable def VarietyLabel : Fin 5 → variety
  | 0 => Pi
  | 1 => Mix (Lambda, Pi)
  | 2 => Mix (Pi, Lambda)
  | 3 => Mix (2 • Lambda, Pi)
  | 4 => Mix (Pi, 2 • Lambda)
