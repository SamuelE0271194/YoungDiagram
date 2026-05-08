import YoungDiagram.Chromosome.Prime

open Finsupp

namespace Chromosome

section order

/--
The dominance relation defined in [Djoković 1980, p. 73].
$X$ dominates $Y$ ($X \ge Y$) if the signature of $X^{(k)}$ is
component-wise greater than or equal to
the signature of $Y^{(k)}$ for all $k \ge 0$.
-/
def Dominates (X Y : Chromosome) : Prop :=
  ∀ k : ℕ, signature (prime^[k] Y) ≤ signature (prime^[k] X)

instance : LE Chromosome where
  le a b := b.Dominates a

/--
The dominance relation forms a preorder on the set of all chromosomes.
-/
instance : Preorder Chromosome where
  le_refl a _ := le_refl _
  lt a b := b.Dominates a ∧ ¬a.Dominates b
  le_trans _ _ _ hab hbc k := le_trans (hab k) (hbc k)

@[simp] lemma le_iff_dominates {X Y : Chromosome} : X ≤ Y ↔
  ∀ k : ℕ, signature (prime^[k] X) ≤ signature (prime^[k] Y) := .rfl

instance : IsOrderedCancelAddMonoid Chromosome where
  add_le_add_left _ _ _ _ := by
    simpa only [le_iff_dominates, iterate_map_add, map_add, add_le_add_iff_right]
  le_of_add_le_add_left _ _ _ h := by
    simpa only [le_iff_dominates, iterate_map_add, map_add, add_le_add_iff_left] using h

lemma sub_single_lt_sub_single {X Y : Chromosome} {g : Gene}
    (hgX : 0 < X g) (hgY : 0 < Y g) (hXY : X < Y) :
    (X - Finsupp.single g 1) < Y - Finsupp.single g 1 := by
  have hX_eq := sub_single_add_single_eq hgX
  have hY_eq := sub_single_add_single_eq hgY
  refine ⟨fun k ↦ ?_, fun hge ↦ lt_irrefl X (lt_of_lt_of_le hXY (fun k ↦ ?_))⟩
  · have h : (prime^[k] X).signature ≤ (prime^[k] Y).signature :=
      (le_iff_dominates.mp hXY.le) k
    nth_rw 1 [← hX_eq, ← hY_eq] at h
    simpa only [iterate_map_add, map_add, add_le_add_iff_right] using h
  · nth_rw 1 [← hY_eq, ← hX_eq]
    simpa only [iterate_map_add, map_add, add_le_add_iff_right] using hge k

end order

end Chromosome
