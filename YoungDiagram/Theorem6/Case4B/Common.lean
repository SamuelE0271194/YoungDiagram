import YoungDiagram.Theorem6.Prelim

open Variety hiding prime prime_def
open Chromosome

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
        Sigma.sigma (Pi.Y2 hε hle hm).val j + Sigma.sigma X.1.val j ≤
        Sigma.sigma (Pi.X2 hε hle hm).val j + Sigma.sigma Y.1.val j) :
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
  change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
  have hZ_split : Sigma.sigma Z.val i =
      Sigma.sigma (Pi.Y2 hε hle hg₁_ge2).val i +
      Sigma.sigma rest.val i := by
    change Sigma.sigma (Pi.Y2 hε hle hg₁_ge2 + rest : Variety.Pi).val i = _
    simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
  have hX_split : Sigma.sigma X.1.val i =
      Sigma.sigma (Pi.X2 hε hle hg₁_ge2).val i +
      Sigma.sigma rest.val i := by
    have hval : X.1.val = (Pi.X2 hε hle hg₁_ge2).val + rest.val := by
      have h := congrArg Subtype.val hdecomp
      simp only [AddSubmonoid.coe_add] at h
      exact h
    simp only [hval, Sigma.sigma, iterate_map_add, map_add]
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
