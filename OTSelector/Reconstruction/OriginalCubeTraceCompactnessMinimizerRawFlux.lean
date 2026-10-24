import OTSelector.Reconstruction.OriginalCubeTraceCompactnessNormalReadout
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessRawFaceFlux

/-! True raw centered-cube surface-order flux variance of the same actual minimizing currents. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm Module Manifold
open scoped ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- One actual common frame gives vanishing surface-order raw cube-flux variance
for all countably many original minimizing clock-set currents, with actual area
change of variables and physical centered cube faces. Its true normal
readouts are selected after the frame. Actual conditional centering, zero face
projections, stationarity and every face second-moment limit are theorems. -/
theorem OriginalSeedConditionalMoments.exists_basis_tendsto_integral_sq_pathClockSetCurrent_normalizedRawCenteredCubeFlux_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (τ : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ R.value τ)
    {K : Type*} [Countable K]
    (η : K → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (hη : ∀ a, Measurable (η a)) (hηI : ∀ a, Integrable (η a) volume)
    (A : K → Set ℝ)
    (hL2 : ∀ a k, MemLp (fun s ↦ originalSeedPathClockSetCurrent S w (η a) (A a) s k) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) :
    ∃ b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
        (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))), ∀ a,
      Tendsto (fun R : ℝ ↦ ∫ s,
        ((R^((finrank ℝ S.covector.ker)-1))⁻¹ * Q.sceneRawCenteredCubeFlux b
          (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _)
            (originalSeedPathClockSetCurrent S w (η a) (A a)) (hL2 a)
            (originalEuclideanNormalReadout (b i))) R s)^2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
        atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := D.exists_basis_projection_all_pathClockSetCurrent_readouts_zero
    hF hw hq hgap hbounds Q τ hmin η hη hηI A hL2
  refine ⟨b, fun a ↦ ?_⟩
  apply Q.tendsto_integral_sq_normalized_sceneRawCenteredCubeFlux_zero b
    (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _)
      (originalSeedPathClockSetCurrent S w (η a) (A a)) (hL2 a)
      (originalEuclideanNormalReadout (b i)))
  intro i
  exact hb i a (originalEuclideanNormalReadout (b i))

end OTSelector.Reconstruction
