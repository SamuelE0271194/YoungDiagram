import YoungDiagram.Theorem6.MixPiLambda.CaseA2Prop
import YoungDiagram.Theorem6.MixPiLambda.CaseProp5

/-!
# §16 Case A Branch B for `Mix (Pi, Lambda)` (label 2): `g₁` polarized.

For `Mix (Pi, Lambda)` the minimal polarized gene `g₁` sits at EVEN rank `2m'+2`, so the
§16 sub-cases are: **Case 4** (`m=2`, `m'=0`) and **Case 3** (`m≥4`, `m'≥1`); Case 5 (`m=1`)
is vacuous.  Since our Case A hypothesis already supplies `ha : a_X(1) < a_Y(1)` directly,
Case 4's §16 `b₁<d₁`/`b₁=d₁` split is unnecessary for the `g⁺` charge: the `a`-propagation
`branchB_case4_aprop_gen` applies, and the mutation reuses the `g₃`-style type6/type7
assemblies (`branchA_g3_assembly_type{6,7}`) with the lower positive gene `g₁ = g⁺(2)`
(`n' = 0`).
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- Parity of `X`'s polarized genes (`Mix (Pi, Lambda)`: positive/negative ⇒ even rank). -/
lemma branchB_hpar {N : ℕ} (X : nMixPiLambda N) :
    ∀ g ∈ X.1.1.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank) := by
  intro g hg
  have hgpos : 0 < X.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
  exact ⟨fun hp => rank_even_of_polarized X.1.2 (by rw [hp]; decide) hgpos,
         fun hn => rank_even_of_polarized X.1.2 (by rw [hn]; decide) hgpos⟩

/-- §16 Case 4 existence: if `X` (minimal gene `g⁺(2)`, so all genes rank `≥ 2`, with
`a_1 < c_1`) had no negative/nonpolarized gene, `branchB_case4_aprop_gen` (vacuous) would
force `a_X(2N+3) + 1 ≤ a_Y(2N+3) = 0`. -/
lemma branchB_case4_exists {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (hmin2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank) :
    ∃ g ∈ X.1.1.support, g.type ≠ .Positive := by
  by_contra hcon
  push Not at hcon
  have hk : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → 2 * N + 3 ≤ g.rank :=
    fun g hg hgnp => absurd (hcon g hg) hgnp
  have hprop := branchB_case4_aprop_gen X Y hXY ha hmin2 (branchB_hpar X) (2 * N + 3) hk
    (2 * N + 3) (by omega) (le_refl _) ⟨N + 1, by ring⟩
  have hzero : ∀ Z : nMixPiLambda N, Chromosome.prime^[2 * N + 3] Z.1.1 = 0 := by
    intro Z
    apply prime_iterate_zero_of_maxRank_le
    have h2 := maxRank_le_rank Z.1.1
    rw [Z.2] at h2
    exact le_trans h2 (by omega)
  rw [show Sigma.sigma X.1.1 (2 * N + 3) =
        signature (Chromosome.prime^[2 * N + 3] X.1.1) from rfl,
    show Sigma.sigma Y.1.1 (2 * N + 3) =
        signature (Chromosome.prime^[2 * N + 3] Y.1.1) from rfl,
    hzero X, hzero Y, map_zero] at hprop
  simp only [Prod.fst_zero, zero_add] at hprop
  exact absurd hprop (by norm_num)

/-- **§16 Case 4** (`m=2`, `g₁ = g⁺(2)`).  Extract the minimal negative/nonpolarized gene
`g₂` and route to the `g₃`-style type6 (`g₂` NP) / type7 (`g₂` negative) assembly with
`n' = 0`.  The `a`-propagation comes from `ha` directly. -/
lemma branchB_case4 (m : ℕ)
    (X Y : nMixPiLambda (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pos : g₁.type = .Positive)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 2) (hm0 : m' = 0) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  subst hm0
  have hm2 : g₁.rank = 2 := by omega
  have hmin2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank := fun g hg => hm2 ▸ hg₁min g hg
  obtain ⟨g0, hg0, hg0np⟩ := branchB_case4_exists X Y hXY ha hmin2
  obtain ⟨g₂, hg₂mem, hg₂minS⟩ := Finset.exists_min_image
    (X.1.1.support.filter (fun g => g.type ≠ .Positive)) Gene.rank
    ⟨g0, Finset.mem_filter.mpr ⟨hg0, hg0np⟩⟩
  rw [Finset.mem_filter] at hg₂mem
  obtain ⟨hg₂supp, hg₂np⟩ := hg₂mem
  have hXg₂' : 0 < X.1.1 g₂ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂supp)
  have hk : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → g₂.rank ≤ g.rank :=
    fun g hg hgnp => hg₂minS g (Finset.mem_filter.mpr ⟨hg, hgnp⟩)
  have hne : g₁ ≠ g₂ := fun h => hg₂np (h ▸ hg₁pos)
  have hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]; exact hXg₂'
  have hprop := branchB_case4_aprop_gen X Y hXY ha hmin2 (branchB_hpar X) g₂.rank hk
  have hg₂ge2 : 2 ≤ g₂.rank := hmin2 g₂ hg₂supp
  cases hch : g₂.type with
  | Positive => exact absurd hch hg₂np
  | NonPolarized =>
    have hodd : Odd g₂.rank := rank_odd_of_nonpolarized_mem X.1.2 hch hXg₂'
    obtain ⟨nn, hnn⟩ : ∃ nn, g₂.rank = 2 * nn + 3 := by
      rcases hodd with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
    have hYwin : ∀ j, 2 * 0 + 1 ≤ j → j < 2 * nn + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0 :=
      fun j _ hj => Ywin_below_pl X Y hXY g₂ hXg₂' (by rw [hnn]; omega)
    exact branchA_g3_assembly_type6 X Y hXY hsigeq 0 nn (Nat.zero_le _) g₁ g₂
      (by rw [hm2]) hg₁pos hnn hch hXg₁ hXg₂ hne
      (fun j _ hj hoj => hprop j (by omega) (by rw [hnn]; exact hj) hoj) hYwin
  | Negative =>
    have hev : Even g₂.rank := rank_even_of_polarized X.1.2 (by rw [hch]; decide) hXg₂'
    have hg₂gt2 : 3 ≤ g₂.rank := by
      rcases Nat.lt_or_ge g₂.rank 3 with hlt | hge
      · exfalso
        have heq2 : g₂.rank = 2 := by omega
        exact hXpn ⟨g₁, g₂, by rw [hm2, heq2], hg₁pos, hch, hXg₁, hXg₂'⟩
      · exact hge
    obtain ⟨nn, hnn⟩ : ∃ nn, g₂.rank = 2 * nn + 2 := by
      rcases hev with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
    have hYwin : ∀ j, 2 * 0 + 1 ≤ j → j ≤ 2 * nn + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0 := by
      intro j _ hj
      rcases lt_or_eq_of_le hj with hlt | heq
      · exact Ywin_below_pl X Y hXY g₂ hXg₂' (by rw [hnn]; omega)
      · subst heq
        exact branchA_g3_Ynonzero_top X Y hXY hcommon nn g₂ hnn hch hXg₂'
    exact branchA_g3_assembly_type7 X Y hXY hsigeq 0 nn (Nat.zero_le _) g₁ g₂
      (by rw [hm2]) hg₁pos hnn hch hXg₁ hXg₂ hne
      (fun j _ hj hoj => hprop j (by omega) (by rw [hnn]; omega) hoj) hYwin

end MixPiLambda
