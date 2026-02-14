import YoungDiagram.ListAux
import Mathlib.Algebra.Ring.NegOnePow

inductive GeneType
  | NonPolarized
  | Positive
  | Negative
deriving DecidableEq, Repr

instance : Neg GeneType where
  neg
    | .NonPolarized => .NonPolarized
    | .Positive => .Negative | .Negative => .Positive

instance : InvolutiveNeg GeneType where
  neg_neg
    | .NonPolarized => rfl
    | .Positive => rfl | .Negative => rfl

instance : SMul ℤˣ GeneType where
  smul n ε := if n = - 1 then - ε else ε

instance : MulAction ℤˣ GeneType where
  one_smul n := rfl
  mul_smul m n ε := by
    obtain ⟨h1 | h1, h2 | h2⟩ := And.intro (Int.units_eq_one_or m) (Int.units_eq_one_or n)
    <;> (subst h1 h2; try rfl)
    exact (neg_neg _).symm

@[simp] lemma GeneType.neg_positive : - GeneType.Positive = .Negative := rfl

@[simp] lemma GeneType.neg_negative : - GeneType.Negative = .Positive := rfl

@[simp] lemma GeneType.neg_one_smul {ε : GeneType} : (- 1 : ℤˣ) • ε = - ε := rfl

lemma GeneType.negOnePow_smul {n : ℤ} {ε : GeneType} :
    n.negOnePow • ε = if Even n then ε else - ε := by
  split_ifs with h
  · simp [(Int.negOnePow_eq_one_iff n).2 h]
  · simp [(Int.negOnePow_eq_neg_one_iff n).2 (Int.not_even_iff_odd.1 h)]

lemma GeneType.negOnePow_smul' {n : ℕ} {ε : GeneType} :
    (n : ℤ).negOnePow • ε = if Even n then ε else - ε := by
  rw [negOnePow_smul]
  exact ite_cond_congr <| propext <| Int.even_coe_nat n

@[simp] lemma GeneType.negOnePow_smul_smul {m n : ℤ} {ε : GeneType} :
    m.negOnePow • n.negOnePow • ε = (m + n).negOnePow • ε := by
  rw [Int.negOnePow_add, mul_smul]

@[simp] lemma GeneType.neg_negOnePow_smul {n : ℤ} {ε : GeneType} :
    - (n.negOnePow • ε) = (n + 1).negOnePow • ε := by
  rw [add_comm, ← negOnePow_smul_smul]; rfl

@[simp] lemma GeneType.negOnePow_smul_neg {n : ℤ} {ε : GeneType} :
    n.negOnePow • (- ε) = (n + 1).negOnePow • ε := by
  rw [← negOnePow_smul_smul]; rfl

-- make this `@[simp]` causes error in MutationsAux.lean
lemma GeneType.neg_smul {n : ℤ} {ε : GeneType} :
    - n.negOnePow • ε = - (n.negOnePow • ε) := by
  rw [← Int.negOnePow_succ, neg_negOnePow_smul]

lemma GeneType.smul_neg {n : ℤ} {ε : GeneType} :
    n.negOnePow • (- ε) = - (n.negOnePow • ε) := by
  rw [neg_negOnePow_smul, negOnePow_smul_neg]

lemma GeneType.neg_ne_nonPolarized_iff {ε : GeneType} :
    ε ≠ .NonPolarized ↔ - ε ≠ .NonPolarized := by cases ε <;> decide

lemma GeneType.smul_ne_nonPolarized_iff {n : ℤ} {ε : GeneType} :
    ε ≠ .NonPolarized ↔ n.negOnePow • ε ≠ .NonPolarized := by
  rw [negOnePow_smul]
  split_ifs
  · rfl
  · exact neg_ne_nonPolarized_iff

lemma Nat.even_sub_one {n : ℕ} (hn : 1 ≤ n) :
    Even n ↔ ¬ Even (n - 1) := by
  nth_rw 1 [← Nat.sub_add_cancel hn, Nat.even_add_one]

/--
A gene is an isomorphism class of strings, defined by its rank (size) and type.
-/
structure Gene where
  /-- The number of vertices in the string representation of the gene. -/
  rank : ℕ
  /-- The polarity of the gene. -/
  type : GeneType
  /-- The rank of a gene is strictly positive. -/
  rank_pos : 1 ≤ rank := by decide
deriving DecidableEq, Repr

def List.toGene {l : List Bool} (hl : l ≠ [] := by decide)
    (_ : l.IsAlt hl := by decide) : Gene :=
  ⟨l.length, if l.getLast hl = true then .Positive else .Negative, List.length_pos_iff.2 hl⟩

def Gene.toList {g : Gene} (_ : g.type ≠ .NonPolarized := by decide) : List Bool :=
  List.iterate not
    (match g.type with | .Positive => true | .Negative => false | .NonPolarized => by tauto)
    g.rank |>.reverse

def Gene.signature (g : Gene) : ℚ × ℚ :=
  match hg : g.type with
  | .NonPolarized => (g.rank / 2, g.rank / 2)
  | .Positive =>
    let l := g.toList <|
      (congrArg (· ≠ .NonPolarized) hg).mpr
      (not_eq_of_beq_eq_false rfl)
    (l.count true, l.count false)
  | .Negative =>
    let l := g.toList <|
      (congrArg (· ≠ .NonPolarized) hg).mpr
      (not_eq_of_beq_eq_false rfl)
    (l.count true, l.count false)

lemma Gene.signature_of_nonPolarized {g : Gene} (hg : g.type = .NonPolarized) :
    g.signature = ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2) := by
  unfold Gene.signature
  split <;> first | rfl | rw [hg] at *; contradiction

lemma Gene.signature_of_positive {g : Gene} (hg : g.type = .Positive) :
  g.signature =
    if Even g.rank then ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2)
    else (((g.rank : ℚ) + 1) / 2, ((g.rank : ℚ) - 1) / 2) := by
  unfold Gene.signature
  split
  · rw [hg] at *; contradiction
  · next hg =>
    simp only [toList, hg, List.count_reverse]
    exact count_iterate_not_true
  · rw [hg] at *; contradiction

lemma Gene.signature_of_negative {g : Gene} (hg : g.type = .Negative) :
  g.signature =
    if Even g.rank then ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2)
    else (((g.rank : ℚ) - 1) / 2, ((g.rank : ℚ) + 1) / 2) := by
  unfold Gene.signature
  split
  · rw [hg] at *; contradiction
  · rw [hg] at *; contradiction
  next hg =>
    simp only [toList, hg, List.count_reverse]
    exact count_iterate_not_false

lemma Gene.signature_pos (g : Gene) : 0 < g.signature := by
  match hg : g.type with
  | .NonPolarized =>
    rw [signature_of_nonPolarized hg]
    exact Prod.lt_of_le_of_lt (by positivity) (by positivity [g.rank_pos])
  | .Positive =>
    rw [signature_of_positive hg]
    split_ifs
    · exact Prod.lt_of_lt_of_le (by positivity [g.rank_pos]) (by positivity)
    · exact Prod.lt_of_lt_of_le (by positivity [g.rank_pos]) <|
        Rat.div_nonneg ((Rat.le_iff_sub_nonneg 1 _).1 <|
          Nat.one_le_cast.2 g.rank_pos) rfl
  | .Negative =>
    rw [signature_of_negative hg]
    split_ifs
    · exact Prod.lt_of_le_of_lt (by positivity) (by positivity [g.rank_pos])
    · refine Prod.lt_of_le_of_lt ?_ (by positivity [g.rank_pos])
      exact Rat.div_nonneg ((Rat.le_iff_sub_nonneg 1 _).1 <|
          Nat.one_le_cast.2 g.rank_pos) rfl
