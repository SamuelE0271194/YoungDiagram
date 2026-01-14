import Mathlib

lemma odd_succ_alter_eq_odd_alter_cat_false {n : ℕ} (hn : ¬ Even n) :
    List.iterate not true (n + 1) = List.iterate not true n ++ [false] := by
  have h := (List.iterate_add (f := not) (a := true) (m := n) (n := 1))
  have hiter : (not^[n]) = not :=
    Function.Involutive.iterate_odd (f := not) Bool.involutive_not <|
      (Nat.not_even_iff_odd).1 hn
  have hval : (not^[n]) true = false := by
    rw [hiter]; rfl
  rw [h, hval]; rfl
