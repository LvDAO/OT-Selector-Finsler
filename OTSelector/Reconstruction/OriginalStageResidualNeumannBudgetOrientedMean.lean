import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedCurrentInput
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedInputVaryingSupport

/-! The actual same-frame common Neumann coefficient has subextensive expectation. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- Each term of the true same-frame common stage coefficient is nonnegative. -/
theorem originalOrientedStageCurrentInputNeumannBudget_nonneg
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) {R : ℝ} (hR : 0 ≤ R) (ell s t : ℝ)
    (hj : ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc s t) scene k) 2 (Q.law : Measure _))
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    0 ≤ originalOrientedStageCurrentInputNeumannBudget S w Q b K R ell s t hj scene := by
  have hE : 0 ≤ originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R ell (Ioc s t) scene :=
    integral_nonneg (fun _ ↦ sq_nonneg _)
  have hface := originalScreeningPhysicalFaceBudget_nonneg Q b
    (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _) (Ioc s t)) hj
    (show 0 ≤ 2*R by linarith) scene
  have hS : 0 ≤ originalStageOrientedSourceReflectedInputBound K b R s t scene := sq_nonneg _
  have hT : 0 ≤ originalStageOrientedTargetReflectedInputBound K b R s t scene := sq_nonneg _
  unfold originalOrientedStageCurrentInputNeumannBudget
  linarith

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- Original minimization and the actual chosen normal projections give a measurable,
integrable common stage coefficient with expectation o(the same physical cube volume).
The omitted bulk, full-current trace and full-input response rates are all proved internally. -/
theorem original_minimizer_orientedStageCurrentInputNeumannBudget_mean_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 2<qdim)
    (b : OrthonormalBasis (Fin qdim) ℝ (EuclideanSpace ℝ (Fin qdim)))
    {densityμ densityν : M→ℝ} {v : M→E→ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀x,0≤densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀x,0≤densityν x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensityμ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ↦x-S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ↦x-S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0<gap)
    {g : ℝ→ℝ→ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀x y,|g x y|≤gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    (K : ℝ → Compacts (Fin qdim → ℝ)) (s t : ℝ)
    (hj : ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc s t) scene k) 2 (Q.law : Measure _))
    (hproj : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _) (Ioc s t)) hj
        (originalEuclideanNormalReadout (b i))) = 0)
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    (∀ R, 1 ≤ R →
      Measurable (originalOrientedStageCurrentInputNeumannBudget S w Q b (K R) R (ell R) s t hj) ∧
      Integrable (originalOrientedStageCurrentInputNeumannBudget S w Q b (K R) R (ell R) s t hj)
        (Q.law : Measure (LegalMarkedOptimalInputScene qdim))) ∧
    Tendsto (fun R : ℝ ↦
      (∫ scene, originalOrientedStageCurrentInputNeumannBudget S w Q b (K R) R (ell R) s t hj scene
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim))) /
          volume.real (originalCenteredPhysicalCubeRegion b (2*R))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let j := originalSeedPathClockSetCurrent S w (originalEuclideanMollifier qdim) (Ioc s t)
  have hE := D.original_minimizer_canonical_oriented_omittedCurrentLtwoEnergy_mean_density_zero
    hF hw (by omega) b cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hg hgb τ Q hmin hell hlarge hsmall (fun _ ↦ Ioc s t)
  have hf := (tendsto_originalScreeningPhysicalFaceBudget_mean_div_pow_zero Q b j hj hproj).comp
    ((tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id)
  have hface : Tendsto (fun R : ℝ ↦
      (∫ scene, originalScreeningPhysicalFaceBudget Q b j hj (2*R) scene ∂(Q.law : Measure _)) /
        volume.real (originalCenteredPhysicalCubeRegion b (2*R))) atTop (𝓝 0) := by
    apply hf.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    have hvol : volume.real (originalCenteredPhysicalCubeRegion b (2*R)) = (2*R)^qdim := by
      rw [measureReal_def, volume_originalOrientedTraffic_cube, ← measureReal_def,
        volume_real_haarRootCube (Fin qdim) (show 0 ≤ R by linarith), Fintype.card_fin]
    rw [hvol]
    rfl
  have hin := Q.tendsto_originalStageOriented_reflectedInput_varyingSupport_density_zero K b hq s t
  have hInt (R : ℝ) (hR : 1 ≤ R) :
      Measurable (originalOrientedStageCurrentInputNeumannBudget S w Q b (K R) R (ell R) s t hj) ∧
      Integrable (originalOrientedStageCurrentInputNeumannBudget S w Q b (K R) R (ell R) s t hj) (Q.law : Measure _) := by
    have hi := Q.originalStageOriented_reflectedInput_bounds (K R) b hq hR s t
    exact ⟨(((((hE.1 R).1.add (measurable_originalScreeningPhysicalFaceBudget Q b j hj (2*R))).add hi.1).add hi.2.1).const_mul 4),
      (((((hE.1 R).2.add (integrable_originalScreeningPhysicalFaceBudget Q b j hj (2*R))).add hi.2.2.2.1).add hi.2.2.2.2.1).const_mul 4)⟩
  refine ⟨hInt, ?_⟩
  have hl := ((hE.2.add hface).add hin).const_mul 4
  simp only [add_zero, mul_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hi := Q.originalStageOriented_reflectedInput_bounds (K R) b hq hR s t
  have hEi := (hE.1 R).2
  have hFi := integrable_originalScreeningPhysicalFaceBudget Q b j hj (2*R)
  have hSi := hi.2.2.2.1
  have hTi := hi.2.2.2.2.1
  unfold originalOrientedStageCurrentInputNeumannBudget
  rw [integral_const_mul,
    integral_add (f := fun scene ↦ originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R (ell R) (Ioc s t) scene +
      originalScreeningPhysicalFaceBudget Q b j hj (2*R) scene +
      originalStageOrientedSourceReflectedInputBound (K R) b R s t scene)
      (g := originalStageOrientedTargetReflectedInputBound (K R) b R s t) ((hEi.add hFi).add hSi) hTi,
    integral_add (f := fun scene ↦ originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R (ell R) (Ioc s t) scene +
      originalScreeningPhysicalFaceBudget Q b j hj (2*R) scene)
      (g := originalStageOrientedSourceReflectedInputBound (K R) b R s t) (hEi.add hFi) hSi,
    integral_add (f := originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R (ell R) (Ioc s t))
      (g := originalScreeningPhysicalFaceBudget Q b j hj (2*R)) hEi hFi,
    integral_add hSi hTi]
  ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
