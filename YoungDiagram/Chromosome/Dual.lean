import YoungDiagram.Chromosome.Order
import YoungDiagram.Chromosome.Rank

open Finsupp

namespace Gene

/-- The sign-dual gene: same rank, opposite polarity. -/
def dual (g : Gene) : Gene :=
  ⟨g.rank, -g.type, g.rank_pos⟩

@[simp] lemma dual_rank (g : Gene) : g.dual.rank = g.rank := rfl

@[simp] lemma dual_type (g : Gene) : g.dual.type = -g.type := rfl

@[simp] lemma dual_dual (g : Gene) : g.dual.dual = g := by
  ext <;> simp [dual]

/-- The sign-dual operation as an equivalence on genes. -/
def dualEquiv : Gene ≃ Gene where
  toFun := dual
  invFun := dual
  left_inv := dual_dual
  right_inv := dual_dual

@[simp] lemma dualEquiv_apply (g : Gene) : dualEquiv g = g.dual := rfl

lemma signature_dual (g : Gene) : g.dual.signature = g.signature.swap := by
  cases g with
  | mk rank type rank_pos =>
      cases type <;> simp [dual, Gene.signature] <;> split_ifs <;> rfl

end Gene

namespace Chromosome

/-- The sign-dual additive equivalence on chromosomes. -/
noncomputable def dualEquiv : Chromosome ≃+ Chromosome :=
  Finsupp.domCongr Gene.dualEquiv

/-- The chromosome obtained by replacing every gene type by its opposite. -/
noncomputable def dual (X : Chromosome) : Chromosome :=
  dualEquiv X

@[simp] lemma dual_apply (X : Chromosome) (g : Gene) :
    dual X g = X g.dual := by
  simp [dual, dualEquiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    Gene.dualEquiv]

@[simp] lemma dual_zero : dual 0 = 0 :=
  dualEquiv.map_zero

@[simp] lemma dual_add (X Y : Chromosome) : dual (X + Y) = dual X + dual Y :=
  dualEquiv.map_add X Y

@[simp] lemma dual_single (g : Gene) (n : ℕ) :
    dual (single g n : Chromosome) = single g.dual n := by
  simp [dual, dualEquiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]

@[simp] lemma dual_dual (X : Chromosome) : dual (dual X) = X := by
  ext g
  simp

@[simp] lemma dual_ofRank (n : ℕ) (ε : GeneType) :
    dual (Gene.ofRank n ε) = Gene.ofRank n (-ε) := by
  rw [Gene.ofRank_def, Gene.ofRank_def]
  split_ifs with h <;> simp [Gene.dual]

@[simp] lemma dual_ofRankAlt (n : ℕ) (ε : GeneType) :
    dual (Gene.ofRankAlt n ε) = Gene.ofRankAlt n (-ε) := by
  simp [Gene.ofRankAlt_def]

@[simp] lemma rank_dual (X : Chromosome) : (dual X).rank = X.rank := by
  induction X using Finsupp.induction with
  | zero => simp
  | single_add a n f ha hn ih =>
      rw [dual_add, dual_single, map_add, map_add, ih]
      simp [rank_single]

lemma signature_dual_single (g : Gene) (n : ℕ) :
    signature (single g.dual n : Chromosome) =
      (signature (single g n : Chromosome)).swap := by
  rw [signature_single g.dual.rank_pos, signature_single g.rank_pos, Gene.signature_dual]
  exact (Prod.smul_swap (n : ℚ) g.signature).symm

@[simp] lemma signature_dual (X : Chromosome) :
    signature (dual X) = (signature X).swap := by
  induction X using Finsupp.induction with
  | zero => simp
  | single_add a n f ha hn ih =>
      rw [dual_add, dual_single, map_add, map_add, ih, Prod.swap_add,
        signature_dual_single]

@[simp] lemma dual_prime (X : Chromosome) : dual X.prime = (dual X).prime := by
  ext g
  rw [dual_apply, prime_coeff, prime_coeff, dual_apply]
  rfl

lemma dual_prime_iterate (X : Chromosome) :
    ∀ k : ℕ, dual (prime^[k] X) = prime^[k] (dual X)
  | 0 => rfl
  | k + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        dual_prime, dual_prime_iterate X k]

lemma dual_le_dual_iff {X Y : Chromosome} : dual X ≤ dual Y ↔ X ≤ Y := by
  constructor
  · intro h k
    have hk := (le_iff_dominates.mp h) k
    rw [← dual_prime_iterate X k, ← dual_prime_iterate Y k, signature_dual,
      signature_dual] at hk
    exact Prod.swap_le_swap.mp hk
  · intro h k
    have hk := (le_iff_dominates.mp h) k
    rw [← dual_prime_iterate X k, ← dual_prime_iterate Y k, signature_dual,
      signature_dual]
    exact Prod.swap_le_swap.mpr hk

lemma dual_lt_dual_iff {X Y : Chromosome} : dual X < dual Y ↔ X < Y := by
  constructor
  · intro h
    exact ⟨dual_le_dual_iff.mp h.1, fun hYX => h.2 (dual_le_dual_iff.mpr hYX)⟩
  · intro h
    exact ⟨dual_le_dual_iff.mpr h.1, fun hYX => h.2 (dual_le_dual_iff.mp hYX)⟩

end Chromosome
