import Mathlib

lemma alt_list_aux_1 {n : ℕ} (hn : ¬ Even n) :
    List.iterate not true (n + 1) = List.iterate not true n ++ [false] := by
  have h := List.iterate_add not true n 1
  have hiter : not^[n] = not :=
    Function.Involutive.iterate_odd (f := not) Bool.involutive_not <|
      (Nat.not_even_iff_odd).1 hn
  rw [h, hiter]; rfl

lemma alt_list_aux_2 {n : ℕ} :
    List.count true (List.iterate not true n) =
    n - List.count false (List.iterate not true n) := by
  rw [List.count_eq_length_filter, List.count_eq_length_filter]
  refine (Nat.sub_eq_of_eq_add ?_).symm
  nth_rw 1 [← List.length_iterate not true n, List.length_eq_length_filter_add id]
  simp; rfl

lemma alt_list_aux_3 {n : ℕ} (hn : Even n) :
    List.iterate not true (n + 1) = List.iterate not true n ++ [true] := by
  have h := List.iterate_add not true n 1
  have hiter : not^[n] = id :=
    Function.Involutive.iterate_even Bool.involutive_not hn
  rw [h, hiter]; rfl

lemma alt_list_aux_4 {n : ℕ} :
    List.count false (List.iterate not true n) =
    n - List.count true (List.iterate not true n) := by
  rw [@alt_list_aux_2 n, Nat.sub_sub_self]
  nth_rw 2 [← List.length_iterate not true n]
  exact List.count_le_length

lemma signature_eq_pos_aux {n : ℕ} :
  (↑(List.count true (List.iterate not true n)),
   ↑(List.count false (List.iterate not true n))) =
    if Even n then ((n : ℚ) / 2, (n : ℚ) / 2)
    else (((n : ℚ) + 1) / 2, ((n : ℚ) - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n hn =>
    split_ifs with h
    · replace h : ¬ Even n := Nat.even_add_one.mp h
      simp only [h, ↓reduceIte, Prod.mk.injEq] at hn ⊢
      split_ands
      · rw [Nat.cast_add, Nat.cast_one, ← hn.1, alt_list_aux_1 h]; simp
      · rw [Nat.cast_add, Nat.cast_one, ← hn.1, alt_list_aux_2,
          alt_list_aux_1 h, Nat.cast_sub]
        · simp [hn]; linarith
        nth_rw 2 [← List.length_iterate not true n]; exact List.count_le_length
    · replace h : Even n := Nat.not_odd_iff_even.mp <| Nat.odd_add_one.mp <|
        Nat.not_even_iff_odd.1 h
      simp only [h, ↓reduceIte, Prod.mk.injEq] at hn ⊢
      split_ands
      · rw [Nat.cast_add, Nat.cast_one, add_assoc, add_div,
          add_self_div_two, ← hn.1, alt_list_aux_3 h]; simp
      · rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
          ← hn.2, alt_list_aux_4, alt_list_aux_3 h, Nat.cast_sub]
        · simp [hn]; linarith
        simp; nth_rw 2 [← List.length_iterate not true n]
        exact List.count_le_length
