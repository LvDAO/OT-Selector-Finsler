import OTSelector.Reconstruction.OriginalStageResidualDensityReflectedMass

/-! Genuine spatial L1 of the true omitted-cut densities on the original physical cube. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Local finiteness suffices for spatial L1 of a bounded unit-range smoothing on a cube. -/
theorem integrable_cube_compactKernel_smoothing {q : ℕ}
    (ρ : Measure (Fin q → ℝ)) [IsFiniteMeasureOnCompacts ρ]
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η)
    {M R : ℝ} (hηM : ∀ x, |η x| ≤ M)
    (hsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0) (hR : 0 ≤ R) :
    Integrable (fun z ↦ ∫ x, η (x - z) ∂ρ)
      (volume.restrict (haarRootCube (Fin q) R)) := by
  let K := haarRootCube (Fin q) (R + 1)
  let σ := ρ.restrict K
  let μ := volume.restrict (haarRootCube (Fin q) R)
  have : IsFiniteMeasure σ := ⟨by
    change (ρ.restrict K) univ < (∞ : ℝ≥0∞)
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (haarRootCube (Fin q) R)) univ < (∞ : ℝ≥0∞)
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hprod : Integrable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦ η (p.2 - p.1))
      (μ.prod σ) := by
    have hm : Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦ η (p.2 - p.1)) :=
      hη.comp (measurable_snd.sub measurable_fst)
    apply Integrable.of_bound hm.aestronglyMeasurable M
    exact Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hηM (p.2 - p.1))
  apply hprod.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
  change (∫ x in K, η (x - z) ∂ρ) = _
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  apply hsupport
  by_contra! hn
  apply hx
  apply (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R + 1) x).mpr
  have hzn := (mem_haarRootCube_iff_norm_le hR z).mp hz
  have hxnorm := norm_add_le (x - z) z
  rw [sub_add_cancel] at hxnorm
  linarith

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Actual original omitted-cut densities are spatially integrable on the actual cube,
by their already proved Campbell local finiteness and the genuine kernel support. -/
theorem ae_originalOmittedCutDensity_integrableOn_cube (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels)
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R : ℝ} (hR : 0 ≤ R) (ell c : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {M : ℝ} (hηM : ∀ x, |η x| ≤ M)
    (hsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Integrable (fun z ↦ originalOmittedCutDensity S w R ell c η z scene)
        (volume.restrict (haarRootCube _ R)) := by
  filter_upwards [ae_originalRestrictedSceneSlabCharges_finiteOnCompacts S hF hw Q
    (originalPathLengthRetained S w R ell)ᶜ c c] with scene hscene
  have : IsFiniteMeasureOnCompacts (originalOmittedSceneActiveCutMeasure S w R ell c scene) :=
    hscene.2.2.1
  exact integrable_cube_compactKernel_smoothing _ hη hηM hsupport hR

end OTSelector.Reconstruction
