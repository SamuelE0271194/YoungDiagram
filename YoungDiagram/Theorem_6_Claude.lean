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
- `Variety.Pi.Step X Z` witnesses a single Π-mutation from X to Z
- `Z ≤ Y` is the pointwise order on `Variety.Pi`
-/
theorem exists_mutation_le (n : ℕ) (X Y : Variety.Pi)
    (hX : X ∈ Pi_n n) (hY : Y ∈ Pi_n n)
    (hXY : X < Y) :
    ∃ Z : Variety.Pi, Variety.Pi.Step X Z ∧ Z ≤ Y := by
  induction n generalizing X Y with
  | zero =>
    -- Both X and Y have rank 0.  Since rank is a sum of positive gene ranks,
    -- rank 0 forces the chromosome to be 0, so X = 0 = Y, contradicting X < Y.
    exfalso
    have hX0 : X.val = 0 := rank_0 X.val hX
    have hY0 : Y.val = 0 := rank_0 Y.val hY
    have : X = Y := by
      ext1
      rw [hX0, hY0]
    exact absurd this (ne_of_lt hXY)
  | succ n ih =>
    cases n with
    | zero =>
      -- X, Y ∈ Π(1): every element is a single polarized gene of rank 1.
      -- Since X < Y, sig X = sig Y, thus X and Y contains the same gene
      -- Thus X = Y, contradiction.
      exfalso
      -- Step 1: X ≤ Y (dominance) at k = 0 gives sig(X.val) ≤ sig(Y.val)
      have hsig_le : signature X.val ≤ signature Y.val := by
        have hle : X.val ≤ Y.val := hXY.le
        exact (le_iff_dominates.mp hle) 0
      -- Step 2: For rank-1 polarized chromosomes, sig.fst + sig.snd = rank = 1
      have hXsum : (signature X.val).1 + (signature X.val).2 = 1 := by
        rcases rank_one_pi_sig X.val X.2 hX with h | h <;> simp [h]
      have hYsum : (signature Y.val).1 + (signature Y.val).2 = 1 := by
        rcases rank_one_pi_sig Y.val Y.2 hY with h | h <;> simp [h]
      -- Step 3: sig(X) ≤ sig(Y) with equal component sums forces sig(X) = sig(Y)
      have hsig_eq : signature X.val = signature Y.val := by
        obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
        have h1 : (signature X.val).1 = (signature Y.val).1 :=
          le_antisymm h1_le (by linarith [h2_le])
        have h2 : (signature X.val).2 = (signature Y.val).2 :=
          le_antisymm h2_le (by linarith [h1_le])
        exact Prod.ext h1 h2
      -- Step 4: Same signature + rank-1 in Π forces X.val = Y.val (same gene)
      have hval_eq : X.val = Y.val :=
        Pi_rank_one_eq_of_sig_eq X.val Y.val X.2 Y.2 hX hY hsig_eq
      exact absurd (Subtype.ext hval_eq) (ne_of_lt hXY)
    | succ m =>
      -- X, Y ∈ Π(m+2): the full inductive step with IH available at rank m+1.
      -- Decide whether X and Y share a common gene.
      by_cases hcommon :
          ∃ g : Gene, 0 < X.val g ∧ 0 < Y.val g
      · -- Case 1: shared gene g.
        -- Subtract one copy of g from both, apply ih at rank m+1, reattach g.
        obtain ⟨g, hgX, hgY⟩ := hcommon
        sorry
      · -- Case 2: disjoint supports.
        -- Direct primitive mutation from X to some Z ≤ Y.
        push_neg at hcommon
        sorry
