import YoungDiagram.Chromosome
import YoungDiagram.Variety
import YoungDiagram.Mutations
import YoungDiagram.SigmaAux_Claude
import YoungDiagram.Sigma_Claude

open Chromosome Variety

/--
`Pi_n n` is the set of elements of `Π` (the polarized variety) with rank equal to `n`.
This corresponds to `Π(n)` in the paper.
-/
def Pi_n (n : ℕ) : Set Variety.Pi := { X | X.val.rank = n }

lemma rank_0 (X : Chromosome) (h : X.rank = 0) : X = 0 := by
  simp [Chromosome.rank, Finsupp.sum] at h
  have h' : ∀ a ∈ X.support, 1 ≤ a.rank := by
    intro a h''
    exact a.rank_pos
  apply Finsupp.ext
  intro a
  simp
  simp_all


/-- A rank-1 polarized chromosome is `Gene.ofRank 1 ε` for some polarized type ε. -/
lemma rank_eq_one_pi_single (C : Chromosome) (hC : C ∈ Variety.Pi) (hr : C.rank = 1) :
    ∃ ε : GeneType, ε ≠ .NonPolarized ∧ C = Gene.ofRank 1 ε := by
  induction C using Finsupp.induction with
  | zero => simp [Chromosome.rank] at hr
  | single_add g n f hg hn ih =>
    -- C = single g n + f; rank C = n * g.rank + rank f
    have hr' : rank f + n * g.rank = 1 := by
      have h2 : rank (Finsupp.single g n) = n * g.rank := by
        have eq1 : rank (Finsupp.single g n) =
            (Finsupp.single g n).sum (fun g' count => count • g'.rank) := rfl
        rw [eq1, Finsupp.sum_single_index (show (0 : ℕ) • g.rank = 0 from by simp),
            nsmul_eq_mul]
        norm_cast
      linarith [map_add Chromosome.rank (Finsupp.single g n) f]
    have hng : 1 ≤ n * g.rank :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hn (Nat.one_le_iff_ne_zero.mp g.rank_pos))
    have hf0 : rank f = 0 := by omega
    have hmul : n * g.rank = 1 := by omega
    have hn1 : n = 1 := Nat.dvd_one.mp ⟨g.rank, hmul.symm⟩
    have hgr1 : g.rank = 1 := by rw [hn1, one_mul] at hmul; exact hmul
    have hfeq : f = 0 := rank_0 f hf0
    have hmem : g ∈ (Finsupp.single g n + f).support := by
      apply Finsupp.mem_support_iff.mpr
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      have hfg : f g = 0 := by
        by_contra h; exact hg (Finsupp.mem_support_iff.mpr h)
      omega
    have hgtype : g.type ≠ .NonPolarized :=
      IsPolarized_def'.mp (mem_Pi_iff.mp hC) g hmem
    exact ⟨g.type, hgtype, by rw [hfeq, add_zero, hn1, ← Gene.ofRank_eq_gene, hgr1]⟩

/-- A rank-1 polarized chromosome has signature (1, 0) or (0, 1). -/
lemma rank_one_pi_sig (C : Chromosome) (hC : C ∈ Variety.Pi) (hr : C.rank = 1) :
    C.signature = (1, 0) ∨ C.signature = (0, 1) := by
  obtain ⟨ε, hε, hCε⟩ := rank_eq_one_pi_single C hC hr
  rw [hCε]
  rcases ε with _ | _ | _
  · exact absurd rfl hε
  · left; exact signature_ofRank_one_positive
  · right; exact signature_ofRank_one_negative

/-- Two rank-1 polarized chromosomes with equal signatures are equal. -/
lemma Pi_rank_one_eq_of_sig_eq (C D : Chromosome)
    (hC : C ∈ Variety.Pi) (hD : D ∈ Variety.Pi)
    (hrC : C.rank = 1) (hrD : D.rank = 1)
    (hsig : C.signature = D.signature) : C = D := by
  obtain ⟨εC, hεC, hCε⟩ := rank_eq_one_pi_single C hC hrC
  obtain ⟨εD, hεD, hDε⟩ := rank_eq_one_pi_single D hD hrD
  rw [hCε, hDε] at hsig ⊢
  rcases εC <;> rcases εD <;>
    simp_all [signature_ofRank_one_positive, signature_ofRank_one_negative]

/--
Proposition after (15.7) [Djoković 1982, p. 29]:
Let X, Y ∈ Π(n) with X < Y.  Then there exists a Π-mutation X → Z such that Z ≤ Y.

Here:
- `Π(n)` is the set of polarized chromosomes of rank `n`
- `X < Y` is the pointwise (Finsupp) strict order on chromosomes
- `IsMutation X.val Z.val` witnesses a single Π-mutation from X to Z
- `Z ≤ Y` is the pointwise order on `Variety.Pi`
-/
theorem exists_mutation_le (n : ℕ) (X Y : Variety.Pi)
    (hX : X ∈ Pi_n n) (hY : Y ∈ Pi_n n)
    (hXY : X < Y) :
    ∃ Z : Variety.Pi, IsMutation X.val Z.val ∧ Z ≤ Y := by
  -- Use strong induction so that subtracting a gene of any rank stays in range.
  revert X Y hX hY hXY
  refine Nat.strongRecOn n ?_
  intro n ih X Y hX hY hXY
  cases n with
  | zero =>
    -- rank 0 forces X = Y = 0, contradicting X < Y.
    exfalso
    have hX0 : X.val = 0 := rank_0 X.val hX
    have hY0 : Y.val = 0 := rank_0 Y.val hY
    exact absurd (Subtype.ext (hX0.trans hY0.symm)) (ne_of_lt hXY)
  | succ n =>
    cases n with
    | zero =>
      -- X, Y ∈ Π(1): rank-1 in Π forces X = Y, contradicting X < Y.
      exfalso
      have hsig_le : signature X.val ≤ signature Y.val :=
        (le_iff_dominates.mp hXY.le) 0
      have hXsum : (signature X.val).1 + (signature X.val).2 = 1 := by
        rcases rank_one_pi_sig X.val X.2 hX with h | h <;> simp [h]
      have hYsum : (signature Y.val).1 + (signature Y.val).2 = 1 := by
        rcases rank_one_pi_sig Y.val Y.2 hY with h | h <;> simp [h]
      have hsig_eq : signature X.val = signature Y.val := by
        obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
        exact Prod.ext (le_antisymm h1_le (by linarith [h2_le]))
                       (le_antisymm h2_le (by linarith [h1_le]))
      exact absurd (Subtype.ext (Pi_rank_one_eq_of_sig_eq X.val Y.val X.2 Y.2 hX hY hsig_eq))
                   (ne_of_lt hXY)
    | succ m =>
      -- X, Y ∈ Π(m+2). Decide whether X and Y share a gene.
      by_cases hcommon : ∃ g : Gene, 0 < X.val g ∧ 0 < Y.val g
      · -- Case 1: shared gene g. Remove one copy from both, apply IH, reattach.
        obtain ⟨g, hgX, hgY⟩ := hcommon
        -- g is polarized (it is in the support of X ∈ Π)
        have hg_pol : g.type ≠ .NonPolarized :=
          IsPolarized_def'.mp (mem_Pi_iff.mp X.2) g
            (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgX))
        -- Finsupp.single g 1 ∈ Π
        have hg1_Pi : Finsupp.single g 1 ∈ Variety.Pi :=
          mem_Pi_iff.mpr (IsPolarized_single.mpr hg_pol)
        -- Define X' = X.val − single g 1 and Y' = Y.val − single g 1
        set X'v : Chromosome := X.val - Finsupp.single g 1
        set Y'v : Chromosome := Y.val - Finsupp.single g 1
        -- Adding back single g 1 recovers X.val / Y.val
        have hX_eq : X'v + Finsupp.single g 1 = X.val := by
          apply Finsupp.ext; intro h
          simp only [X'v, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with heq
          · subst heq; omega
          · omega
        have hY_eq : Y'v + Finsupp.single g 1 = Y.val := by
          apply Finsupp.ext; intro h
          simp only [Y'v, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with heq
          · subst heq; omega
          · omega
        -- X'v and Y'v are in Π (their support ⊆ that of X.val / Y.val)
        have hX'Pi : X'v ∈ Variety.Pi := by
          rw [mem_Pi_iff, IsPolarized_def']
          intro h hh
          apply IsPolarized_def'.mp (mem_Pi_iff.mp X.2) h
          rw [Finsupp.mem_support_iff] at hh ⊢
          intro hXh; apply hh
          simp only [X'v, Finsupp.tsub_apply, Finsupp.single_apply, hXh]; omega
        have hY'Pi : Y'v ∈ Variety.Pi := by
          rw [mem_Pi_iff, IsPolarized_def']
          intro h hh
          apply IsPolarized_def'.mp (mem_Pi_iff.mp Y.2) h
          rw [Finsupp.mem_support_iff] at hh ⊢
          intro hYh; apply hh
          simp only [Y'v, Finsupp.tsub_apply, Finsupp.single_apply, hYh]; omega
        -- rank (single g 1) = g.rank
        have hrank_g : Chromosome.rank (Finsupp.single g 1) = g.rank := by
          simp only [Chromosome.rank, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          rw [Finsupp.sum_single_index (by simp : (0 : ℕ) • g.rank = 0)]
          simp
        -- X'v.rank = m + 2 − g.rank
        have hX'rank : X'v.rank = m + 2 - g.rank := by
          have h1 : X'v.rank + g.rank = m + 2 := by
            have heq := congr_arg Chromosome.rank hX_eq
            rw [map_add, hrank_g] at heq
            linarith [show X.val.rank = m + 2 from hX]
          omega
        have hY'rank : Y'v.rank = m + 2 - g.rank := by
          have h1 : Y'v.rank + g.rank = m + 2 := by
            have heq := congr_arg Chromosome.rank hY_eq
            rw [map_add, hrank_g] at heq
            linarith [show Y.val.rank = m + 2 from hY]
          omega
        -- ⟨X'v, _⟩ < ⟨Y'v, _⟩ in Variety.Pi (cancel single g 1 from X < Y)
        -- The goal is definitionally Y'v.Dominates X'v ∧ ¬X'v.Dominates Y'v
        have hlt' : (⟨X'v, hX'Pi⟩ : Variety.Pi) < ⟨Y'v, hY'Pi⟩ := by
          change Y'v.Dominates X'v ∧ ¬X'v.Dominates Y'v
          refine ⟨fun k => ?_, fun hge => ?_⟩
          · -- Y'v.Dominates X'v at step k
            have h := (le_iff_dominates.mp hXY.le) k
            simp only [← hX_eq, ← hY_eq, iterate_map_add, map_add,
                       add_le_add_iff_right] at h
            exact h
          · -- ¬X'v.Dominates Y'v: hge yields Y ≤ X (dominance), so X < X, absurd
            exact lt_irrefl X (lt_of_lt_of_le hXY (fun k => by
              simp only [← hX_eq, ← hY_eq, iterate_map_add, map_add,
                         add_le_add_iff_right]
              exact hge k))
        -- Apply strong IH at rank m + 2 − g.rank (< m + 2 since g.rank ≥ 1)
        obtain ⟨Z', hmut', hle'⟩ :=
          ih (m + 2 - g.rank) (Nat.sub_lt (by omega) g.rank_pos)
            ⟨X'v, hX'Pi⟩ ⟨Y'v, hY'Pi⟩ hX'rank hY'rank hlt'
        -- Return Z = Z' + single g 1
        refine ⟨⟨Z'.val + Finsupp.single g 1,
            mem_Pi_iff.mpr (IsPolarized_iff_add.mpr
              ⟨mem_Pi_iff.mp Z'.2, mem_Pi_iff.mp hg1_Pi⟩)⟩, ?_, ?_⟩
        · -- IsMutation X.val (Z'.val + single g 1)
          rw [show X.val = X'v + Finsupp.single g 1 from hX_eq.symm]
          exact hmut'.add_right _
        · -- Z' + single g 1 ≤ Y.val
          change Z'.val + Finsupp.single g 1 ≤ Y.val
          rw [← hY_eq, le_iff_dominates]
          intro k
          have h := (le_iff_dominates.mp hle') k
          simp only [iterate_map_add, map_add, add_le_add_iff_right]
          exact h
      · -- Case 2: disjoint supports.
        push_neg at hcommon
        sorry
