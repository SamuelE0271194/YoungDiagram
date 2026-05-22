import YoungDiagram.Theorem6.Prelim

open Variety hiding prime prime_def
open Chromosome Sigma

/-- Common type-2 mutation constructor for Case 4b with even rank-gap.

The parity-specific files only have to prove `hXY_sigma`: the sigma increment of
the type-2 mutation is absorbed by the existing gap between `X` and `Y`. -/
lemma exists_mutation_le_case4b_evenGap_of_sigma_window
    {n : ℕ} (X Y : nPi n)
    {g₁ g₂ : Gene}
    (hXg₁ : X.1.val g₁ ≠ 0)
    (hg₁_ge2 : 2 ≤ g₁.rank)
    (hg₁_one : X.1.val g₁ = 1)
    (hg₂pos : 0 < X.1.val g₂)
    (hg₂rank : g₁.rank < g₂.rank)
    (hε₂ : ¬ g₂.type = -g₁.type)
    (hXY_sigma : ∀ (hε : g₁.type ≠ .NonPolarized)
        (hle : g₁.rank ≤ g₂.rank) (hm : 1 < g₁.rank) (j : ℕ),
        sigma (Pi.Y2 hε hle hm).val j + sigma X.1.val j ≤
        sigma (Pi.X2 hε hle hm).val j + sigma Y.1.val j) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let ε := g₁.type
  have hε : ε ≠ .NonPolarized :=
    IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
  have hle : g₁.rank ≤ g₂.rank := le_of_lt hg₂rank
  have hg₂_type : g₂.type = g₁.type := by
    have hpol₁ : g₁.type ≠ .NonPolarized := hε
    have hpol₂ : g₂.type ≠ .NonPolarized :=
      IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₂
        (Finsupp.mem_support_iff.mpr hg₂pos.ne')
    match ht₁ : g₁.type, hpol₁ with
    | .Positive, _ =>
      cases ht₂ : g₂.type
      · tauto
      · rw [ht₂, ht₁] at hε₂
      · rw [ht₂, ht₁, GeneType.neg_positive] at hε₂; tauto
    | .Negative, _ =>
      cases ht₂ : g₂.type
      · tauto
      · rw [ht₂, ht₁, GeneType.neg_negative] at hε₂; tauto
      · rw [ht₂, ht₁] at hε₂
  have hg₁_ofRank : Gene.ofRank g₁.rank ε = Finsupp.single g₁ 1 :=
    Gene.ofRank_eq_gene
  have hg₂_ofRank : Gene.ofRank g₂.rank ε = Finsupp.single g₂ 1 := by
    have h := @Gene.ofRank_eq_gene g₂
    rw [hg₂_type] at h
    exact h
  have hsrc_val : (Pi.X2 hε hle hg₁_ge2 : Chromosome) =
      Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
    simp only [Pi.X2_eq]
    rw [hg₁_ofRank, hg₂_ofRank]
  have hne : g₁ ≠ g₂ := fun h => absurd hg₂rank (h ▸ lt_irrefl _)
  have hsrc_le : ∀ g : Gene,
      (Pi.X2 hε hle hg₁_ge2 : Chromosome) g ≤ X.1.val g := by
    intro gen
    rw [hsrc_val, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    rcases eq_or_ne gen g₁ with rfl | hng₁
    · simp [Ne.symm hne, hg₁_one]
    · rcases eq_or_ne gen g₂ with rfl | hng₂
      · simp only [Ne.symm hng₁]
        exact hg₂pos
      · simp [Ne.symm hng₁, Ne.symm hng₂]
  let rest : Pi :=
    ⟨X.1.val - (Pi.X2 hε hle hg₁_ge2 : Chromosome),
      Variety.sub_mem_Pi _ X.1.2⟩
  have hdecomp : X.1 = Pi.X2 hε hle hg₁_ge2 + rest :=
    Subtype.val_injective
      (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
  let Z : Pi := Pi.Y2 hε hle hg₁_ge2 + rest
  have hstep : Pi.Step X.1 Z :=
    hdecomp.symm ▸ Pi.Step.mk
      (Pi.X2 hε hle hg₁_ge2)
      (Pi.Y2 hε hle hg₁_ge2)
      rest
      (Pi.Primitive.type2 ε hε hle hg₁_ge2)
  refine ⟨Z, hstep, ?_⟩
  change Z.val ≤ Y.1.val
  rw [le_iff_dominates]
  intro i
  change sigma Z.val i ≤ sigma Y.1.val i
  have hZ_split : sigma Z.val i =
      sigma (Pi.Y2 hε hle hg₁_ge2).val i +
      sigma rest.val i := by
    change sigma (Pi.Y2 hε hle hg₁_ge2 + rest : Variety.Pi).val i = _
    simp only [AddSubmonoid.coe_add, sigma, iterate_map_add, map_add]
  have hX_split : sigma X.1.val i =
      sigma (Pi.X2 hε hle hg₁_ge2).val i +
      sigma rest.val i := by
    have hval : X.1.val = (Pi.X2 hε hle hg₁_ge2).val + rest.val := by
      have h := congrArg Subtype.val hdecomp
      simp only [AddSubmonoid.coe_add] at h
      exact h
    simp only [hval, sigma, iterate_map_add, map_add]
  rw [hZ_split]
  have h1 := (hXY_sigma hε hle hg₁_ge2 i).1
  have h2 := (hXY_sigma hε hle hg₁_ge2 i).2
  rw [hX_split] at h1 h2
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add]
    linarith
  · simp only [Prod.snd_add]
    linarith

lemma support_filter_tail_eq {X : Chromosome} {g₁ g₂ : Gene} {j : ℕ} {τ : GeneType}
    (hg₂min : ∀ g', 0 < X g' → g₁.rank < g'.rank → g₂.rank ≤ g'.rank)
    (hj1 : g₁.rank ≤ j) (hj2 : j ≤ g₂.rank - 1) :
    X.support.filter (fun g => g₁.rank < g.rank ∧ g.type = Sigma.altType g.rank τ) =
      X.support.filter (fun g => j < g.rank ∧ g.type = Sigma.altType g.rank τ) := by
  ext g
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨hg_supp, hg_rank, hg_type⟩
    exact ⟨hg_supp, by have := hg₂min g (Nat.pos_of_ne_zero hg_supp) hg_rank; omega,
      hg_type⟩
  · rintro ⟨hg_supp, hg_rank, hg_type⟩
    exact ⟨hg_supp, by omega, hg_type⟩

lemma support_filter_rank_pred_altType_split {X : Chromosome} {g₁ : Gene} {τ : GeneType}
    (hg₁_one : X g₁ = 1) (hg₁_altType : g₁.type = Sigma.altType g₁.rank τ) :
    X.support.filter (fun g => g₁.rank - 1 < g.rank ∧ g.type = Sigma.altType g.rank τ) =
      {g₁} ∪ X.support.filter (fun g => g₁.rank < g.rank ∧
        g.type = Sigma.altType g.rank τ) := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
    Finsupp.mem_support_iff]
  constructor
  · rintro ⟨hsupp, hrank, htype⟩
    by_cases heq : g = g₁
    · exact Or.inl heq
    · right
      refine ⟨hsupp, ?_, htype⟩
      rcases Nat.lt_or_eq_of_le (show g₁.rank ≤ g.rank from by omega) with h | h
      · exact h
      · exfalso
        exact heq (Gene.ext h.symm (by rw [← h, ← hg₁_altType] at htype; exact htype))
  · rintro (rfl | ⟨hsupp, hrank, htype⟩)
    · exact ⟨by rw [hg₁_one]; exact one_ne_zero, by have := g.rank_pos; omega, hg₁_altType⟩
    · exact ⟨hsupp, by have := g₁.rank_pos; omega, htype⟩

lemma fst_zero_gap_le_sub_one_of_fst_one_lt {n : ℕ} (X Y : nPi n)
    (hXY : X.1 ≤ Y.1) (ha : (sigma X.1 1).1 < (sigma Y.1 1).1) :
    (sigma Y.1 0).1 - (sigma Y.1 1).1 ≤
      (sigma X.1 0).1 - (sigma X.1 1).1 - 1 := by
  obtain ⟨nX, hnX⟩ := sigma_isNat X.1.val 1 X.1.2
  obtain ⟨nY, hnY⟩ := sigma_isNat Y.1.val 1 Y.1.2
  have hX1 : (sigma X.1 1).1 = ↑nX.1 := congr_arg Prod.fst hnX
  have hY1 : (sigma Y.1 1).1 = ↑nY.1 := congr_arg Prod.fst hnY
  have hlt : (↑nX.1 : ℚ) < ↑nY.1 := by linarith
  have hle : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 := by
    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hlt)
  linarith [sigma_zero_fst_eq X Y hXY]

lemma fst_lt_of_gap_chain {n i j : ℕ} (X Y : nPi n) (hXY : X.1 ≤ Y.1)
    (hstrict : (sigma Y.1 0).1 - (sigma Y.1 1).1 <
      (sigma X.1 0).1 - (sigma X.1 1).1)
    (hc1_ci : (sigma Y.1 1).1 - (sigma Y.1 i).1 ≤
      (sigma Y.1 0).2 - (sigma Y.1 j).2)
    (hd0_di : (sigma Y.1 0).2 - (sigma Y.1 j).2 ≤
      (sigma X.1 0).2 - (sigma X.1 j).2)
    (hb0_bi : (sigma X.1 0).2 - (sigma X.1 j).2 =
      (sigma X.1 1).1 - (sigma X.1 i).1) :
    (sigma X.1 i).1 < (sigma Y.1 i).1 := by
  have ha0_eq : (sigma X.1 0).1 = (sigma Y.1 0).1 := sigma_zero_fst_eq X Y hXY
  linarith

lemma snd_lt_of_gap_chain {n i j : ℕ} (X Y : nPi n)
    (hd2_gt_b2 : (sigma X.1 2).2 < (sigma Y.1 2).2)
    (hd2_di : (sigma Y.1 2).2 - (sigma Y.1 i).2 ≤
      (sigma Y.1 0).2 - (sigma Y.1 j).2)
    (hd0_di : (sigma Y.1 0).2 - (sigma Y.1 j).2 ≤
      (sigma X.1 0).2 - (sigma X.1 j).2)
    (hb0_b2 : (sigma X.1 0).2 - (sigma X.1 j).2 =
      (sigma X.1 2).2 - (sigma X.1 i).2) :
    (sigma X.1 i).2 < (sigma Y.1 i).2 := by
  linarith
