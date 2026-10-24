import OTSelector.Reconstruction.OriginalFocalResidueLocalEnergy

/-! The same actual endpoint residue energy is controlled on the entire original
legal matching: short focal compliance near the endpoint, true momentum outside. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The public quadratic coefficient bound controls the actual full original
momentum pointwise, in the same kinetic convention used by the matching class. -/
theorem OriginalSeedConditionalMoments.exists_original_momentum_kinetic_domination
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support) →
      (m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support) → m.1.1 < m.1.2 →
      ‖originalSeedPairMomentum S w m‖ ^ 2 ≤ C * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 := by
  obtain ⟨C, hC, hbound⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  refine ⟨4 * C + 1, by positivity, fun m ha hb hab ↦ ?_⟩
  have hpd := (D.pair_compliance_posDef hF hw ha.1 hb.1 hab).2
  have hquad (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
      |matrixQuadratic (originalSeedPairCoefficient S w m.1) v| ≤ C * ∑ i, v i ^ 2 := by
    rw [← D.originalFocalKinetic_eq_of_original_support hbounds ha hb hab v]
    exact hbound m.1.1 m.1.2 v
  have h := norm_mulVec_sq_le_quadratic_of_sum_bound hpd.posSemidef hC hquad m.2
  rw [← D.originalFocalKinetic_eq_of_original_support hbounds ha hb hab m.2] at h
  have hk : 0 ≤ D.originalFocalKinetic gap m.1.1 m.1.2 m.2 :=
    D.originalFocalKinetic_nonneg hF hw hgap m.1.1 m.1.2 m.2
  change ‖originalSeedPairMomentum S w m‖ ^ 2 ≤ _ at h
  nlinarith

/-- The same actual left pole residue energy is bounded by the original kinetic
cost on every legal original mark, including marks outside the focal collar. -/
theorem OriginalSeedConditionalMoments.exists_original_left_residueEnergy_kinetic_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter ε c : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hε : 0 < ε) (hεh : ε < D.hi - D.lo) (hc : 0 < c)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    (hlower : ∀ s ∈ Ioo 0 ε,
      (originalSeedKernel S w (D.lo + s) - c • ((s ^ 2)⁻¹ • G + 1)).PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support) →
      (m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support) → m.1.1 < m.1.2 →
      0 ≤ originalSeedLeftPoleEnergy S w D.lo G m ∧
      originalSeedLeftPoleEnergy S w D.lo G m ≤ C * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 := by
  obtain ⟨Cm, hCm, hm⟩ := D.exists_original_momentum_kinetic_domination hF hw hgap hbounds
  let δ : ℝ := min (ε / 4) (gap / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδgap : δ ≤ gap / 2 := min_le_right _ _
  let J : ℝ := ∑ i, ∑ j, |G i j|
  have hJ : 0 ≤ J := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  refine ⟨4 / c + J * Cm / δ + 1, by positivity, fun m ha hb hab ↦ ?_⟩
  let r : ℝ := m.1.1 - (S.level : ℝ) - D.lo
  have hr : 0 < r := by dsimp [r]; linarith [ha.1.1]
  have hk := D.originalFocalKinetic_nonneg hF hw hgap m.1.1 m.1.2 m.2
  have he0 : 0 ≤ originalSeedLeftPoleEnergy S w D.lo G m := by
    apply div_nonneg
    · simpa only [star_trivial] using hG.dotProduct_mulVec_nonneg (originalSeedPairMomentum S w m)
    · exact hr.le
  refine ⟨he0, ?_⟩
  by_cases hsmall : r < δ
  · have hrε : 2 * r < ε := by linarith
    have hsep : gap ≤ m.1.2 - m.1.1 := by
      have h := hbounds.separated m.1.1 ha.2 m.1.2 hb.2
      simpa only [Real.dist_eq, abs_of_neg (sub_neg.mpr hab), neg_sub] using h
    have h2r : (S.level : ℝ) + D.lo + 2 * r ≤ m.1.2 := by dsimp [r]; linarith
    have hlocal := D.original_left_focal_pair_residue_lower hF hw hεh hc hG hlower hr hrε hb.1 h2r
    have heq : (S.level : ℝ) + D.lo + r = m.1.1 := by dsimp [r]; ring
    rw [heq] at hlocal
    have hnear := residue_energy_le_of_compliance_lower hc hr
      (D.posDef_originalSeedClockCompliance hF hw ha.1 hb.1 hab) hlocal m.2
    change originalSeedLeftPoleEnergy S w D.lo G m ≤
      (4 / c) * matrixQuadratic (originalSeedPairCoefficient S w m.1) m.2 at hnear
    rw [← D.originalFocalKinetic_eq_of_original_support hbounds ha hb hab m.2] at hnear
    exact hnear.trans (mul_le_mul_of_nonneg_right
      (by have hz := div_nonneg (mul_nonneg hJ hCm.le) hδ.le; linarith) hk)
  · have hδr : δ ≤ r := le_of_not_gt hsmall
    have hres := residue_dotProduct_le_absEntrySum_mul_norm_sq G (originalSeedPairMomentum S w m)
    have hmomentum := hm m ha hb hab
    change originalSeedPairMomentum S w m ⬝ᵥ (G *ᵥ originalSeedPairMomentum S w m) ≤
      J * ‖originalSeedPairMomentum S w m‖ ^ 2 at hres
    change (originalSeedPairMomentum S w m ⬝ᵥ (G *ᵥ originalSeedPairMomentum S w m)) / r ≤ _
    calc
      _ ≤ (J * ‖originalSeedPairMomentum S w m‖ ^ 2) / r :=
        div_le_div_of_nonneg_right hres hr.le
      _ ≤ (J * (Cm * D.originalFocalKinetic gap m.1.1 m.1.2 m.2)) / r := by gcongr
      _ ≤ (J * (Cm * D.originalFocalKinetic gap m.1.1 m.1.2 m.2)) / δ :=
        div_le_div_of_nonneg_left (by positivity) hδ hδr
      _ = (J * Cm / δ) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hc.le]) hk

/-- The same actual right pole residue energy is bounded by the original kinetic
cost on every legal original mark, including marks outside the focal collar. -/
theorem OriginalSeedConditionalMoments.exists_original_right_residueEnergy_kinetic_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter ε c : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hε : 0 < ε) (hεh : ε < D.hi - D.lo) (hc : 0 < c)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    (hlower : ∀ s ∈ Ioo 0 ε,
      (originalSeedKernel S w (D.hi - s) - c • ((s ^ 2)⁻¹ • G + 1)).PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support) →
      (m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support) → m.1.1 < m.1.2 →
      0 ≤ originalSeedRightPoleEnergy S w D.hi G m ∧
      originalSeedRightPoleEnergy S w D.hi G m ≤ C * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 := by
  obtain ⟨Cm, hCm, hm⟩ := D.exists_original_momentum_kinetic_domination hF hw hgap hbounds
  let δ : ℝ := min (ε / 4) (gap / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδgap : δ ≤ gap / 2 := min_le_right _ _
  let J : ℝ := ∑ i, ∑ j, |G i j|
  have hJ : 0 ≤ J := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  refine ⟨4 / c + J * Cm / δ + 1, by positivity, fun m ha hb hab ↦ ?_⟩
  let r : ℝ := D.hi - (m.1.2 - (S.level : ℝ))
  have hr : 0 < r := by dsimp [r]; linarith [hb.1.2]
  have hk := D.originalFocalKinetic_nonneg hF hw hgap m.1.1 m.1.2 m.2
  have he0 : 0 ≤ originalSeedRightPoleEnergy S w D.hi G m := by
    apply div_nonneg
    · simpa only [star_trivial] using hG.dotProduct_mulVec_nonneg (originalSeedPairMomentum S w m)
    · exact hr.le
  refine ⟨he0, ?_⟩
  by_cases hsmall : r < δ
  · have hrε : 2 * r < ε := by linarith
    have hsep : gap ≤ m.1.2 - m.1.1 := by
      have h := hbounds.separated m.1.1 ha.2 m.1.2 hb.2
      simpa only [Real.dist_eq, abs_of_neg (sub_neg.mpr hab), neg_sub] using h
    have h2r : m.1.1 ≤ (S.level : ℝ) + D.hi - 2 * r := by dsimp [r]; linarith
    have hlocal := D.original_right_focal_pair_residue_lower hF hw hεh hc hG hlower hr hrε ha.1 h2r
    have heq : (S.level : ℝ) + D.hi - r = m.1.2 := by dsimp [r]; ring
    rw [heq] at hlocal
    have hnear := residue_energy_le_of_compliance_lower hc hr
      (D.posDef_originalSeedClockCompliance hF hw ha.1 hb.1 hab) hlocal m.2
    change originalSeedRightPoleEnergy S w D.hi G m ≤
      (4 / c) * matrixQuadratic (originalSeedPairCoefficient S w m.1) m.2 at hnear
    rw [← D.originalFocalKinetic_eq_of_original_support hbounds ha hb hab m.2] at hnear
    exact hnear.trans (mul_le_mul_of_nonneg_right
      (by have hz := div_nonneg (mul_nonneg hJ hCm.le) hδ.le; linarith) hk)
  · have hδr : δ ≤ r := le_of_not_gt hsmall
    have hres := residue_dotProduct_le_absEntrySum_mul_norm_sq G (originalSeedPairMomentum S w m)
    have hmomentum := hm m ha hb hab
    change originalSeedPairMomentum S w m ⬝ᵥ (G *ᵥ originalSeedPairMomentum S w m) ≤
      J * ‖originalSeedPairMomentum S w m‖ ^ 2 at hres
    change (originalSeedPairMomentum S w m ⬝ᵥ (G *ᵥ originalSeedPairMomentum S w m)) / r ≤ _
    calc
      _ ≤ (J * ‖originalSeedPairMomentum S w m‖ ^ 2) / r :=
        div_le_div_of_nonneg_right hres hr.le
      _ ≤ (J * (Cm * D.originalFocalKinetic gap m.1.1 m.1.2 m.2)) / r := by gcongr
      _ ≤ (J * (Cm * D.originalFocalKinetic gap m.1.1 m.1.2 m.2)) / δ :=
        div_le_div_of_nonneg_left (by positivity) hδ hδr
      _ = (J * Cm / δ) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hc.le]) hk

end OTSelector.Reconstruction
