import OTSelector.Reconstruction.FinslerOriginalRetainedPhysicalPressure
import OTSelector.MeasureTheory.AEIntegralCutoffUpperLimit

/-! True actual retained physical root pressures admit deterministic cutoffs
whose pressure integrals recover the canonical original pressure upper. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

variable {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure]
  {lambda : Measure Z} {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
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

/-- Actual original laws internally supply all pressure measurability, common
lower and pointwise upper inputs of the deterministic root-cutoff construction.
The only global analytic input is genuine integrability of the same physical
p0 produced by the original global energy/lower argument. -/
theorem eventually_exists_originalRetainedSeedPhysicalPressure_cutoff
    [IsFiniteMeasure lambda]
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0) lambda)
    (η : ℕ → Z → ℝ) (hηM : ∀ n, Measurable (η n))
    (hη : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ η n z) atTop (𝓝 0) ∧
      ∀ n, 0 ≤ η n z ∧ η n z ≤ 1)
    (j : ℕ) (t budget tolerance : ℝ) (hbudget : 0 < budget) (htolerance : 0 < tolerance) :
    ∀ᶠ n in atTop, ∃ K : Set Z, MeasurableSet K ∧
      (lambda.restrict (populationSeedRootPiece P a κ lambda j)).real Kᶜ < budget ∧
      IntegrableOn (originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t) K
        (lambda.restrict (populationSeedRootPiece P a κ lambda j)) ∧
      (∫ z in K, originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t z
        ∂lambda.restrict (populationSeedRootPiece P a κ lambda j)) <
      (∫ z, originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z
        ∂lambda.restrict (populationSeedRootPiece P a κ lambda j)) + tolerance := by
  have hphysical := integrable_originalPhysicalFinslerRootPressure_of_zero f hlaw hF
    hcomplete hu ha hinj hdim hgap hsep γ hγ hb hp0 t
  have hbound := ae_originalRetainedSeedPhysicalPressure_lower_upper hlaw hF hcomplete hu
    ha hinj hdim hgap hsep γ hγ χ hχ δ hδ hb f η hη j t
  exact exists_original_pressure_cutoff_integral_upper_ae
    (lambda.restrict (populationSeedRootPiece P a κ lambda j))
    (fun n ↦ originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t)
    (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t)
    (fun n ↦ aestronglyMeasurable_originalRetainedSeedPhysicalPressure hlaw hF hcomplete
      hu ha hinj hdim hgap hsep γ hγ χ hχ δ hδ hb f η hηM j n t)
    hphysical.1.restrict (mul_nonneg (abs_nonneg t) (norm_nonneg f))
    (fun n ↦ hbound.mono (fun _ hz ↦ hz.1 n)) (hbound.mono (fun _ hz ↦ hz.2))
    budget tolerance hbudget htolerance

end OTSelector.Reconstruction
