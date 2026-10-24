import OTSelector.Reconstruction.FinslerOriginalRootPressureLaw
import OTSelector.Reconstruction.OriginalNormalizedPressureLipschitz

/-! The canonical actual general Finsler root pressure and its exact population
normalization have their measurable versions and physical probe bounds internally. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
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
  {b : Z × ℝ → M} (hb : Measurable b) (f : M × M →ᵇ ℝ)

include hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ hb

/-- Every measurable original root tilt has its actual canonical general
Finsler pressure AE strongly measurable on each unchanged original seed piece. -/
theorem aestronglyMeasurable_actual_originalRootPressure
    (j : ℕ) (tilt : Z → ℝ) (htilt : Measurable tilt) :
    AEStronglyMeasurable (fun z ↦ originalSeedRootPressure (P j).seed a η₀ η₁ b f z (tilt z))
      (lambda.restrict (populationSeedRootPiece P a κ lambda j)) := by
  apply aestronglyMeasurable_original_legalMarkedPressure_limit
    (source := fun (_z : Z) (x : ℝ) ↦ x) (target := fun (_z : Z) (y : ℝ) ↦ y)
    (kin := originalSeedRootKinetic (P j).seed a) (probe := originalPhysicalRootProbe b f)
    (finrank ℝ (P j).seed.covector.ker) (condDistrib u a η₀) (condDistrib u a η₁)
    measurable_snd measurable_snd
    (measurable_originalSeedRootKinetic (P j).seed hF hcomplete hu ha hinj)
    (measurable_originalPhysicalRootProbe hcomplete hb f) tilt htilt
  filter_upwards [hlaw.ae_originalSeedRootPressure_limits hF hcomplete hu ha hinj hdim hgap hsep
    γ hγ hb f j] with z hz
  exact hz.1 (tilt z)

omit hlaw hdim hgap hsep γ hγ hb f in
/-- The actual original intensity, read at the actual inverse seed label,
is measurable without a global positive lower density. -/
theorem measurable_actual_populationAtlasTheta (j : ℕ) :
    Measurable (populationAtlasTheta P a κ lambda j) :=
  ((measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj j).comp
    (measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj)).ennreal_toReal

/-- Exact original population normalization of the actual canonical pressure
has its own measurable version and one common physical lower/probe bound. -/
theorem actual_originalRootPressure_normalized_measurable_lower (j : ℕ) (t : ℝ) :
    let q : ℝ := finrank ℝ (P j).seed.covector.ker
    let I := originalSeedRootPressure (P j).seed a η₀ η₁ b f
    AEStronglyMeasurable (populationAtlasIntegrand P a κ lambda I j q t)
      (lambda.restrict (populationSeedRootPiece P a κ lambda j)) ∧
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      LipschitzWith ‖f‖₊ (fun s ↦ populationAtlasIntegrand P a κ lambda I j q s z) ∧
      -(|t| * ‖f‖) ≤ populationAtlasIntegrand P a κ lambda I j q t z := by
  let q : ℝ := finrank ℝ (P j).seed.covector.ker
  have hq : 0 < q := by
    have h := (P j).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at h
    dsimp only [q]
    exact_mod_cast (show 0 < finrank ℝ (P j).seed.covector.ker by omega)
  have hmθ : Measurable (populationAtlasTheta P a κ lambda j) :=
    measurable_actual_populationAtlasTheta hF hcomplete hu ha hinj j
  have hpow : Measurable (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (2/q)) :=
    (Real.continuous_rpow_const (div_nonneg (by norm_num) hq.le)).measurable.comp hmθ
  have hnegpow : Measurable (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2/q)) := by
    convert hpow.inv using 1
    funext z
    change populationAtlasTheta P a κ lambda j z ^ (-2/q) =
      (populationAtlasTheta P a κ lambda j z ^ (2/q))⁻¹
    rw [show (-2/q : ℝ) = -(2/q) by ring]
    exact Real.rpow_neg (populationAtlasTheta_nonneg P a κ lambda j z) (2/q)
  have hread := aestronglyMeasurable_actual_originalRootPressure hlaw hF hcomplete hu ha hinj
    hdim hgap hsep γ hγ hb f j (fun z ↦ t * populationAtlasTheta P a κ lambda j z ^ (2/q))
      (hpow.const_mul t)
  refine ⟨hnegpow.aestronglyMeasurable.mul hread,?_⟩
  filter_upwards [hlaw.ae_originalSeedRootPressure_limits hF hcomplete hu ha hinj hdim hgap hsep
    γ hγ hb f j] with z hz
  have hzero : 0 ≤ originalSeedRootPressure (P j).seed a η₀ η₁ b f z 0 := by
    simpa only [abs_zero,zero_mul,neg_zero] using hz.2.2 0
  have hθ := populationAtlasTheta_nonneg P a κ lambda j z
  exact ⟨lipschitz_normalized_pressure hθ hq hz.2.1,
    normalized_pressure_lower_bound hθ hq hz.2.1 hzero t⟩

end OTSelector.Reconstruction
