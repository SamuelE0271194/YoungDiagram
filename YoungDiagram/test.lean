import Mathlib

open Finsupp

inductive GeneType
| NonPolarized
| Positive
| Negative
deriving DecidableEq, Repr

structure Gene where
  rank : ℕ
  type : GeneType
  rank_pos : 1 ≤ rank
deriving DecidableEq, Repr

section polarized

abbrev List.isAlt {l : List Bool} (hl : l ≠ [] := by decide) : Prop :=
  l = List.iterate not (l.head hl) l.length

#eval [true].isAlt
#eval [true, true].isAlt
#eval [true, false].isAlt
#eval [true, false, true].isAlt
#eval [false, true, false].isAlt

def List.toGen {l : List Bool} (hl : l ≠ [] := by decide)
    (_ : l.isAlt hl := by decide) : Gene :=
  ⟨l.length, if l.head hl = true then .Positive else .Negative, List.length_pos_iff.2 hl⟩

#eval [true].toGen
#eval [true, false].toGen
#eval [true, false, true].toGen
#eval [false, true, false].toGen

def Gene.toList {g : Gene} (_ : g.type ≠ .NonPolarized := by decide) : List Bool :=
  List.iterate not
    (match g.type with | .Positive => true | .Negative => false | .NonPolarized => by tauto)
    g.rank

#eval [true].toGen.toList
#eval [true, false].toGen.toList
#eval [true, false, true].toGen.toList
#eval [false, true, false].toGen.toList

def Gene.Signature (g : Gene) : ℚ × ℚ :=
  match hg : g.type with
  | .NonPolarized => (g.rank / 2, g.rank / 2)
  | .Positive =>
    let l := g.toList <|
      (congrArg (fun _a ↦ _a ≠ .NonPolarized) hg).mpr
      (not_eq_of_beq_eq_false rfl)
    (l.count true, l.count false)
  | .Negative =>
    let l := g.toList <|
      (congrArg (fun _a ↦ _a ≠ .NonPolarized) hg).mpr
      (not_eq_of_beq_eq_false rfl)
    (l.count true, l.count false)

#eval [true].toGen.Signature
#eval [true, false].toGen.Signature
#eval [true, false, true].toGen.Signature
#eval [false, true, false].toGen.Signature

def geneSignature (g : Gene) : ℚ × ℚ :=
  let n : ℚ := g.rank
  match g.type with
  | .NonPolarized => (n / 2, n / 2)
  | .Positive =>
      if g.rank % 2 == 0 then (n / 2, n / 2)
      else ((n + 1) / 2, (n - 1) / 2)
  | .Negative =>
      if g.rank % 2 == 0 then (n / 2, n / 2)
      else ((n - 1) / 2, (n + 1) / 2)

#eval geneSignature [true].toGen
#eval geneSignature [true, false].toGen
#eval geneSignature [true, false, true].toGen
#eval geneSignature [false, true, false].toGen

end polarized

abbrev Chromosome := Gene →₀ ℕ

namespace Chromosome

def signature (c : Chromosome) : ℚ × ℚ :=
  c.sum (fun g count ↦ (count : ℚ) • g.Signature)

noncomputable def primeGene (g : Gene) : Chromosome :=
  if h : 1 < g.rank then
    single ⟨g.rank - 1, g.type, Nat.le_sub_one_of_lt h⟩ 1
  else 0

noncomputable def prime (c : Chromosome) : Chromosome :=
  c.sum (fun g m ↦ m • primeGene g)

def dominates (X Y : Chromosome) : Prop :=
  ∀ k : ℕ, signature (prime^[k] Y) ≤ signature (prime^[k] X)

instance : Preorder Chromosome where
  le a b := b.dominates a
  le_refl a _ := le_refl _
  lt a b := b.dominates a ∧ ¬a.dominates b
  le_trans _ _ _ hab hbc k := le_trans (hab k) (hbc k)

abbrev o (c : Chromosome) : Chromosome := c.filter (Odd  ·.rank)
abbrev e (c : Chromosome) : Chromosome := c.filter (Even ·.rank)

def IsOdd (c : Chromosome) : Prop  := o c = c
def IsEven (c : Chromosome) : Prop := e c = c

lemma parityDecomposition (c : Chromosome) : c = o c + e c := by
  simp [o, e]
  conv =>
    enter [2, 2, 1, a]
    rw [← Nat.not_odd_iff_even]
  rw [filter_pos_add_filter_neg]

def IsPolarized (c : Chromosome) : Prop :=
  c.filter (·.type ≠ .NonPolarized) = c

def IsNonPolarized (c : Chromosome) : Prop :=
  c.filter (·.type = .NonPolarized) = c

abbrev variety := AddSubmonoid Chromosome

def Lambda : variety where
  carrier := {c : Chromosome | IsPolarized c}
  add_mem' {a b} ha hb := by
    simp [IsPolarized] at *
    rw [ha, hb]
  zero_mem' := by
    simp [IsPolarized, filter_zero]

def Pi : variety where
  carrier := {c : Chromosome | IsNonPolarized c}
  add_mem' {a b} ha hb := by
    simp [IsNonPolarized] at *
    rw [ha, hb]
  zero_mem' := by
    simp [IsNonPolarized, filter_zero]

def Mix (v : variety × variety) : variety where
  carrier := {c : Chromosome | e c ∈ v.1 ∧ o c ∈ v.2}
  add_mem' {a b} ha hb := by
    simp [o, e] at *
    exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := by
    simp [o, e, filter_zero]

open Pointwise

#check Pi
#check Mix (Lambda, Pi)
#check Mix (Pi, Lambda)
#check Mix (2 • Lambda, Pi)
#check Mix (Pi, 2 • Lambda)

#synth SMul ℕ variety

end Chromosome

section Legacy

local notation "PolarizedList" => List Bool

def List.isAlternating (l : PolarizedList) : Prop :=
  ∀ i : ℕ, (_ : i < l.length - 1) → l[i] = !l[i + 1]

lemma nil_isAlternating : [].isAlternating := by
  simp [List.isAlternating]

lemma sing_isAlternating {x : Bool} : [x].isAlternating := by
  simp [List.isAlternating]

lemma cons_isAlternating {x : Bool} {xs : PolarizedList} (hxs : xs ≠ []) :
    (x :: xs).isAlternating ↔ x = !xs.head hxs ∧ xs.isAlternating := by
  constructor
  · intro h
    constructor
    · specialize h 0
      simp [List.ne_nil_iff_length_pos.1 hxs] at h
      rw [List.head_eq_getElem, h]
    intro i hi
    specialize h (i + 1) ?_
    · rw [List.length_cons]; omega
    simpa using h
  · intro h i hi
    by_cases hi' : i = 0
    · simpa [hi', List.head_eq_getElem] using h.1
    rw [List.length_cons, add_tsub_cancel_right] at hi
    conv => enter [1, 2]; rw [(Nat.succ_pred_eq_of_ne_zero hi').symm]
    conv => enter [2, 1, 2]; rw [(Nat.succ_pred_eq_of_ne_zero hi').symm]
    simp [h.2 (i - 1) (by omega)]

instance {l : PolarizedList} : Decidable l.isAlternating := by
  induction l with
  | nil => exact Decidable.isTrue nil_isAlternating
  | cons x xs h =>
    match xs with
    | [] => exact Decidable.isTrue sing_isAlternating
    | x' :: xs =>
      exact decidable_of_decidable_of_iff (cons_isAlternating (xs.cons_ne_nil x')).symm

#eval [true].isAlternating
#eval [true, true].isAlternating
#eval [true, false].isAlternating
#eval [true, false, true].isAlternating

def PolarizedList.toGene (l : PolarizedList)
    (_ : l.isAlternating := by decide) (hlen : 1 ≤ l.length := by decide) : Gene :=
  ⟨l.length, if l[0] = true then .Positive else .Negative, hlen⟩

#eval PolarizedList.toGene [true, false, true]
#eval PolarizedList.toGene [true, false]
#eval PolarizedList.toGene [true]

#eval List.iterate not false 3

def PolarizedGene.toList (g : Gene) (_ : g.type ≠ .NonPolarized := by decide) :
    PolarizedList :=
  match g.type with
  | .Positive => List.iterate not true g.rank
  | .Negative => List.iterate not false g.rank
  | .NonPolarized => by tauto

end Legacy
