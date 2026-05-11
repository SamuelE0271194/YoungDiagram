import YoungDiagram.Chromosome.Basic

open Finsupp

namespace Chromosome

section signature

/--
The signature of a chromosome is the weighted sum of the signatures of its constituent genes.
-/
noncomputable def signature : Chromosome →+ ℚ × ℚ := weight Gene.signature

lemma signature_def {X : Chromosome} : X.signature =
  X.sum (fun g count ↦ (count : ℚ) • g.signature) := rfl

lemma signature_nonneg (X : Chromosome) : 0 ≤ X.signature := by
  dsimp [signature_def]
  exact sum_nonneg' fun g ↦
    smul_nonneg Rat.natCast_nonneg g.signature_pos.le

@[simp] lemma signature_ofRank_zero {ε : GeneType} :
    (Gene.ofRank 0 ε).signature = 0 := rfl

lemma signature_ofRank {n : ℕ} {ε : GeneType} :
  (Gene.ofRank n ε).signature =
    if h : n = 0 then 0
    else (⟨n, ε, Nat.pos_of_ne_zero h⟩ : Gene).signature := by
  dsimp [signature_def]
  split_ifs
  · rfl
  · rw [sum_single_index, Nat.cast_one, one_smul]
    · exact smul_eq_zero_of_left rfl _

@[simp] lemma signature_ofRank_one_positive :
    (Gene.ofRank 1 .Positive).signature = (1, 0) := by
  simp only [signature_ofRank, one_ne_zero, ↓reduceDIte, Gene.signature_of_positive,
    Nat.not_even_one, ↓reduceIte, Nat.cast_one, add_self_div_two, sub_self, zero_div]

@[simp] lemma signature_ofRank_one_negative :
    (Gene.ofRank 1 .Negative).signature = (0, 1) := by
  simp only [signature_ofRank, one_ne_zero, ↓reduceDIte, Gene.signature_of_negative,
    Nat.not_even_one, ↓reduceIte, Nat.cast_one, sub_self, zero_div, add_self_div_two]

@[simp] lemma signature_single {k : ℕ} {n : ℕ} (hk : 1 ≤ k) {ε : GeneType} :
    signature (single (⟨k, ε, hk⟩ : Gene) n) =
    n * (⟨k, ε, hk⟩ : Gene).signature :=
  sum_single_index <| smul_eq_zero_of_left rfl _

lemma signature_ofRank_nonPolarized {n : ℕ} :
    (Gene.ofRank n .NonPolarized).signature =
    (Gene.ofRank n .NonPolarized).signature.swap := by
  simp only [signature_ofRank]
  split_ifs
  · rfl
  · rw [Gene.signature_of_nonPolarized rfl]; rfl

lemma signature_ofRank_swap {n : ℕ} {ε : GeneType} :
    (Gene.ofRank n (- ε)).signature = (Gene.ofRank n ε).signature.swap := by
  cases ε
  · exact signature_ofRank_nonPolarized
  all_goals
    simp only [GeneType.neg_positive, signature_ofRank]; split_ifs
    · rfl
    · first | rw [Gene.signature_of_negative rfl, Gene.signature_of_positive rfl] |
        rw [Gene.signature_of_positive rfl, Gene.signature_of_negative rfl]
      simp only; split_ifs <;> rfl

lemma signature_ofRank_positive {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 1) .Negative).signature + (1, 0) := by
  have hk' : k ≠ 0 := by omega
  simp only [signature_ofRank, hk', ↓reduceDIte]
  split_ifs with h
  · replace hk : k = 1 := by omega
    simp [Gene.signature_of_positive, hk]
  · simp [Gene.signature_of_positive]
    split_ifs with h1
    · have : ¬ Even (k - 1) := (Nat.even_sub_one hk).1 h1
      simp [Gene.signature_of_negative, this, Nat.cast_pred hk]; ring
    · have : Even (k - 1) := (iff_not_comm.1 (Nat.even_sub_one hk)).2 h1
      simp [Gene.signature_of_negative, this, Nat.cast_pred hk]; ring

lemma signature_ofRank_negative {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Negative).signature =
    (Gene.ofRank (k - 1) .Positive).signature + (0, 1) := by
  rw [← GeneType.neg_positive, signature_ofRank_swap,
    signature_ofRank_positive hk, Prod.swap_add, ← signature_ofRank_swap]; simp

lemma signature_ofRank_general {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 1) (-ε)).signature + (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp only [signature_ofRank_positive hk, GeneType.neg_positive,
    signature_ofRank_one_positive]
  | .Negative, _ => simp only [signature_ofRank_negative hk, GeneType.neg_negative,
    signature_ofRank_one_negative]

lemma signature_ofRank_even_half {k : ℕ} {ε : GeneType} (hk : Even k) :
    (Gene.ofRank k ε).signature = ((k : ℚ) / 2, (k : ℚ) / 2) := by
  by_cases hk_zero : k = 0
  · simp [hk_zero]; rfl
  · simp only [signature_ofRank, hk_zero, ↓reduceDIte, Gene.signature, hk, ↓reduceIte]
    split <;> rfl

lemma signature_ofRank_even {k : ℕ} {ε : GeneType} (hk : Even k) :
    (Gene.ofRank k ε).signature = (Gene.ofRank k (- ε)).signature := by
  by_cases hk_zero : k = 0
  · rw [hk_zero, Gene.ofRank_zero, Gene.ofRank_zero]
  · simp only [signature_ofRank, hk_zero, ↓reduceDIte, Gene.signature, hk, ↓reduceIte]
    split <;> rfl

lemma signature_ofRankAlt_general {k : ℕ} {ε : GeneType} (hk : 1 ≤ k)
    (hε : ε ≠ .NonPolarized) :
    (Gene.ofRankAlt k ε).signature =
    (Gene.ofRankAlt (k - 1) (-ε)).signature + (Gene.ofRank 1 ε).signature := by
  rw [Gene.ofRankAlt_def, Gene.ofRankAlt_def, Nat.cast_sub hk,
    Nat.cast_one, ← sub_add_eq_sub_sub]
  obtain (h1 | h1) := Int.even_or_odd k
  · rw [Int.negOnePow_odd, Int.negOnePow_even, GeneType.neg_one_smul, one_smul,
      ← signature_ofRank_general hk hε, ← signature_ofRank_even]
    · exact (Int.even_coe_nat k).1 h1
    · exact Even.sub h1 <| Int.even_iff.2 rfl
    · exact odd_sub_one.2 h1
  · rw [Int.negOnePow_even, Int.negOnePow_odd, one_smul, GeneType.neg_one_smul,
      signature_ofRank_general hk hε, add_left_inj, signature_ofRank_even]
    · exact Odd.tsub_odd ((Int.odd_coe_nat k).1 h1) <| Nat.odd_iff.2 rfl
    · exact Odd.sub_even h1 <| Int.even_iff.2 rfl
    · exact even_sub_one.2 h1

lemma signature_ofRankAlt_general' {k : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    (Gene.ofRankAlt (k + 1) ε).signature =
    (Gene.ofRankAlt k (-ε)).signature + (Gene.ofRank 1 ε).signature := by
  rw [signature_ofRankAlt_general (by omega) hε, Nat.add_sub_cancel]

lemma signature_ofRank_eq {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 1) (- ε)).signature + (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp [signature_ofRank_positive hk]
  | .Negative, _ =>
    rw [← GeneType.neg_positive, signature_ofRank_swap,
      signature_ofRank_positive hk, Prod.swap_add, ← signature_ofRank_swap]; simp

lemma signature_ofRank_positive' {k : ℕ} (hk : 1 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 1) .Positive).signature + if Even k then (0, 1) else (1, 0) := by
  have hk' : k ≠ 0 := by omega
  by_cases hk'' : k = 1
  · subst hk''
    simp only [signature_ofRank_one_positive, tsub_self, Gene.ofRank_zero, map_zero,
      Nat.not_even_one, ↓reduceIte, zero_add]
  · simp only [signature_ofRank, hk', ↓reduceDIte]
    replace hk'' : k - 1 ≠ 0 := Nat.sub_ne_zero_of_lt <|
      Nat.lt_of_le_of_ne hk fun a ↦ hk'' a.symm
    simp only [Gene.signature_of_positive, Nat.even_sub_one hk, ite_not, hk'', ↓reduceDIte]
    split_ifs <;> (simp [hk]; ring)

lemma signature_ofRank_eq' {k : ℕ} {ε : GeneType} (hk : 1 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature = (Gene.ofRank (k - 1) ε).signature +
    if Even k then (Gene.ofRank 1 (- ε)).signature else (Gene.ofRank 1 ε).signature := by
  match ε, hε with
  | .Positive, _ => simp [signature_ofRank_positive' hk]
  | .Negative, _ =>
    rw [← GeneType.neg_positive, neg_neg, signature_ofRank_swap, signature_ofRank_swap,
      signature_ofRank_positive' hk, Prod.swap_add, add_right_inj]
    split_ifs <;> simp

lemma signature_ofRank_positive₂ {k : ℕ} (hk : 2 ≤ k) :
    (Gene.ofRank k .Positive).signature =
    (Gene.ofRank (k - 2) .Positive).signature + (1, 1) := by
  change _ = (Gene.ofRank (k - 1 - 1) .Positive).signature + _
  rw [signature_ofRank_positive (Nat.one_le_of_lt hk),
    signature_ofRank_eq (Nat.le_sub_one_of_lt hk) (by decide), add_assoc]; simp

lemma signature_ofRank_eq₂ {k : ℕ} {ε : GeneType} (hk : 2 ≤ k) (hε : ε ≠ .NonPolarized) :
    (Gene.ofRank k ε).signature =
    (Gene.ofRank (k - 2) ε).signature + (1, 1) := by
  match ε, hε with
  | .Positive, _ => exact signature_ofRank_positive₂ hk
  | .Negative, _ =>
    rw [← GeneType.neg_positive, signature_ofRank_swap,
      signature_ofRank_positive₂ hk, Prod.swap_add, ← signature_ofRank_swap]
    rfl

lemma signature_fst {X : Chromosome} :
    (Chromosome.signature X).1 = X.sum (fun g n ↦ (n : ℚ) • g.signature.1) :=
  map_sum (AddMonoidHom.fst ..) ..

lemma signature_snd {X : Chromosome} :
    (Chromosome.signature X).2 = X.sum (fun g n ↦ (n : ℚ) • g.signature.2) :=
  map_sum (AddMonoidHom.snd ..) ..

end signature

end Chromosome
