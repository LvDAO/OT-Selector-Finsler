import OTSelector.Reconstruction.FinslerOriginalRetainedRootPressure

/-! Actual varying original retained pressures have AE measurable original
root versions, with no measurable pressure or optimizer selection assumption. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
  (hdim : 6 ≤ finrank ℝ E)
  {gap diameter : ℝ} (hgap : 0 < gap)
  (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diameter)
  (γ : Kernel Z (ℝ × ℝ)) [IsMarkovKernel γ]
  (hγ : ∀ᵐ z ∂lambda, Vlasov.IsCoupling (γ z)
    (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
  (χ : ℕ → Kernel Z (ℝ × ℝ)) [∀ n z, IsFiniteMeasure (χ n z)]
  (hχ : ∀ᵐ z ∂lambda, ∀ n, χ n z ≤ γ z)
  (δ : ℕ → Z → ℝ)
  (hδ : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ δ n z) atTop (𝓝 0) ∧
    ∀ n, 0 ≤ δ n z ∧ δ n z < 1 ∧ 1 - δ n z ≤ (χ n z).real univ)
  {b : Z × ℝ → M} (hb : Measurable b) (f : M × M →ᵇ ℝ)
include hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ χ hχ δ hδ hb

/-- Every measurable actual physical tilt gives a strongly measurable
canonical retained pressure on the unchanged selected original root piece. -/
theorem aestronglyMeasurable_actual_originalRetainedRootPressure
    (j n : ℕ) (tilt : Z → ℝ) (htilt : Measurable tilt) :
    AEStronglyMeasurable (fun z ↦ originalSeedRetainedRootPressure (P j).seed a (χ n) b f z (tilt z))
      (lambda.restrict (populationSeedRootPiece P a κ lambda j)) := by
  apply aestronglyMeasurable_original_legalMarkedPressure_limit
    (source := fun (_z : Z) (x : ℝ) ↦ x) (target := fun (_z : Z) (y : ℝ) ↦ y)
    (kin := originalSeedRootKinetic (P j).seed a) (probe := originalPhysicalRootProbe b f)
    (finrank ℝ (P j).seed.covector.ker)
    ((originalNormalizedRetainedPairKernel (χ n)).map Prod.fst)
    ((originalNormalizedRetainedPairKernel (χ n)).map Prod.snd) measurable_snd measurable_snd
    (measurable_originalSeedRootKinetic (P j).seed hF hcomplete hu ha hinj)
    (measurable_originalPhysicalRootProbe hcomplete hb f) tilt htilt
  filter_upwards [hlaw.ae_originalSeedRetainedRootPressure_limits hF hcomplete hu ha hinj
    hdim hgap hsep γ hγ χ hχ δ hδ hb f j] with z hz
  exact (hz.1 n).1 (tilt z)

end OTSelector.Reconstruction
