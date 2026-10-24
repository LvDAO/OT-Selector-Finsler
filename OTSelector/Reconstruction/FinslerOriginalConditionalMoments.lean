import OTSelector.Reconstruction.SeedConditionalMoments
import OTSelector.Reconstruction.FinslerPopulationSupportedComparison

/-!
# Both original conditional populations have the actual compliance moments

One complete comparison and one fixed label basis work for both original colors,
every root in their common support span, and every exponent strictly below two.
The comparison retains its actual original phase derivative, so its intrinsic
kernel remains identified with the original physical length Hessian.
-/

open Set Matrix Module Manifold MeasureTheory ProbabilityTheory
open scoped Topology ContDiff Matrix.Norms.Operator MatrixOrder ENNReal

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

/-- Both compliance observables, under the original clock law and with its actual offset. -/
def OriginalClockComplianceMoments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (offset : ℝ) (K : ℝ → Matrix ι ι ℝ) (root : ℝ) : Prop :=
  Integrable (fun x ↦ (1 + CFC.abs (∫ t in root..(x - offset), K t)).det) μ ∧
    ∀ r : ℝ, 0 < r → r < 2 →
      Integrable (fun x ↦ ‖∫ t in root..(x - offset), K t‖ ^ r) μ

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual common geometry and complete moment conclusions for both original colors.
The finite label basis is explicitly fixed, so the conclusion is never a vacuous
quantification over bases of a space with a different dimension. -/
structure OriginalSeedConditionalMoments (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (μ ν : Measure ℝ) where
  comparison : F.SmoothPhaseJetComparison S.c11Data.initialChart 0 w
    (S.c11Data.position w, fderiv ℝ S.c11Data.potential (S.c11Data.position w))
    (fderiv ℝ S.c11Data.position w)
    (fderiv ℝ (fun z ↦ fderiv ℝ S.c11Data.potential (S.c11Data.position z)) w)
  labels_subset : comparison.labels ⊆ S.openLabels
  curve_eq : S.curve w = comparison.curve w
  phase_jet : ∀ old t, S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
    HasFDerivAt (F.chartMomentumFamily old S.curve)
      (fderiv ℝ (F.chartMomentumFamily old comparison.curve) (w, t)) (w, t) ∧
    HasFDerivAt (F.chartMomentumFamily old comparison.curve)
      (fderiv ℝ (F.chartMomentumFamily old comparison.curve) (w, t)) (w, t)
  jacobian_pos : ∀ old t, t ∈ interior (S.calibrationTimes w) →
    S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
    0 < parameterizedJacobian
      (fun q : ℝ × S.covector.ker ↦ extChartAt 𝓘(ℝ, E) old (S.curve q.2 q.1))
      S.normalization (t, w)
  lo : ℝ
  hi : ℝ
  support : CommonSeedSupportSpan S w μ ν lo hi
  source_moments : ∀ root ∈ Ioo lo hi,
    OriginalClockComplianceMoments μ S.level
      (comparison.intrinsicKernel (Module.finBasis ℝ S.covector.ker)) root
  target_moments : ∀ root ∈ Ioo lo hi,
    OriginalClockComplianceMoments ν S.level
      (comparison.intrinsicKernel (Module.finBasis ℝ S.covector.ker)) root

omit [BorelSpace E] in
/-- The original supported comparison and the two original physical density laws
produce the complete common-kernel moment witness, with no endpoint or rank oracle. -/
theorem originalSeedConditionalMoments_of_supported_comparison
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hcomparison : HasActiveSeedComparison S w)
    {μ ν : Measure ℝ} {lo hi : ℝ} (hspan : CommonSeedSupportSpan S w μ ν lo hi)
    {ρ₀ ρ₁ : M → ℝ} {v : M → E → ℝ} {c : ℝ≥0∞}
    (hρ₀ : Continuous ρ₀) (hρ₁ : Continuous ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ x ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old x)
    (hdensity₀ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) ρ₀ v c.toReal)
    (hdensity₁ : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦ x - S.level)) ρ₁ v c.toReal) :
    Nonempty (OriginalSeedConditionalMoments S w μ ν) := by
  obtain ⟨C, hsub, hcurve, hjet, hpos⟩ := hcomparison
  have hμprob := hspan.source.probability
  have hνprob := hspan.target.probability
  refine ⟨{
    comparison := C
    labels_subset := hsub
    curve_eq := hcurve
    phase_jet := hjet
    jacobian_pos := hpos
    lo := lo
    hi := hi
    support := hspan
    source_moments := ?_
    target_moments := ?_ }⟩
  · intro root hroot
    exact seed_comparison_compliance_moments C hF (Module.finBasis ℝ S.covector.ker)
      hw hcurve hjet hpos hspan.lt hspan.calibrated hroot
      (by simpa only [sub_zero] using hspan.source.seedClock.ae_open)
      hρ₀ hρ₀nonneg hv hv0 c
      (fun center hball K hK hKU ↦ hdensity₀ center hball K hK (fun _ ht ↦ hKU _ ht))
  · intro root hroot
    exact seed_comparison_compliance_moments C hF (Module.finBasis ℝ S.covector.ker)
      hw hcurve hjet hpos hspan.lt hspan.calibrated hroot
      (by simpa only [sub_zero] using hspan.target.seedClock.ae_open)
      hρ₁ hρ₁nonneg hv hv0 c
      (fun center hball K hK hKU ↦ hdensity₁ center hball K hK (fun _ ht ↦ hKU _ ht))

variable {Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- Almost every original geometric label has a single actual common-kernel moment
witness for both original conditional populations and all interior roots. -/
def PopulationConditionalMomentLaw (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → Z) (lambda : Measure Z) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] : Prop :=
  ∀ᵐ z ∂lambda, ∃ (j : ℕ) (w : (P j).seed.covector.ker),
    w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
      Nonempty (OriginalSeedConditionalMoments (P j).seed w
        (condDistrib u a η₀ z) (condDistrib u a η₁ z))

omit [BorelSpace E] in
/-- The actual atlas comparison law yields both original conditional moment laws.
The almost-everywhere set is selected before endpoint spaces and frames are chosen. -/
theorem PopulationSupportedComparisonLaw.conditional_moments
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : M → E → ℝ}
    (hlaw : PopulationSupportedComparisonLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v)
    (hF : F.IsSmoothStronglyConvex)
    (hρ₀ : Continuous ρ₀) (hρ₁ : Continuous ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ x ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old x) :
    PopulationConditionalMomentLaw P a lambda η₀ η₁ := by
  filter_upwards [hlaw] with z hz
  obtain ⟨j, w, lo, hi, hw, hwz, _, _, hcomparison, hspan, hdensity₀, hdensity₁⟩ := hz
  exact ⟨j, w, hw, hwz,
    originalSeedConditionalMoments_of_supported_comparison hF hw hcomparison hspan
      hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg hv hv0 hdensity₀ hdensity₁⟩

end OTSelector.Reconstruction
