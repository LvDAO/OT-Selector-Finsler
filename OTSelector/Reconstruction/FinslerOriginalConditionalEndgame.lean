import OTSelector.Reconstruction.FinslerOriginalPaperGeometricHypotheses
import OTSelector.Reconstruction.FinslerSelectorFinalInputsWiringAudit
import OTSelector.Reconstruction.FinslerOriginalValueInputAssembly

/-!
# The conditional endgame of the general Finsler selector

This module packages the endgame of the general Finsler selector as one
conditional theorem.  It combines

1. the paper-side geometric hypotheses, packaged in
   |FinslerPaperGeometricHypotheses| (FinslerOriginalPaperGeometricHypotheses):
   the single geometric hypothesis (the calibrated tube, in the consumer form
   |(interior (chartInterior F u)).Nonempty|), the a.e. Borel ray-cluster data,
   pointwise clock atomlessness, and the Palm sample law;
2. the reduced named fields of the final inputs, in the exact consumer
   interfaces of |FinslerSelectorFinalInputsAudit|
   (FinslerSelectorFinalInputsWiringAudit): |pressureLower|, |pressureUpper|,
   |radius|, |hradius|, |hvalue|, |hprob|, |hupper|.

Their conjunction is the structure |FinslerConditionalEndgameHypotheses|.  From
it we prove that the consumer structure |FinslerSelectorFinalInputs| is
nonempty (|nonempty_finalInputs|, reusing the wiring lemma
|FinslerSelectorFinalInputsAudit.toFinalInputs|), and, using the final assembly
theorem |existsUnique_general_finsler_selector_final|, the endgame theorem
|existsUnique_general_finsler_selector_conditional_endgame|: under the paper's
population and iid sampling data there is one calibrated potential |u| such that
for every conditional endgame structure for |u| (equivalently: whenever the
paper-side geometric hypotheses and the reduced named fields hold at |u|) the
consumer final inputs are nonempty, the Palm readout identification holds, the
readout derivative of the limiting lower pressure at zero exists, and the unique
deterministic population optimal plan with whole-optimal-set convergence in
probability exists.  The paper-side geometric data also produce the open-domain
window data and the calibrated level-seed patches (|windowSide_endgame|).

The remaining paper-data are exactly the fields of
|FinslerConditionalEndgameHypotheses|:

* |geometric| — the paper's local calibrated tube hypothesis and the a.e. Borel /
  Palm data (main.tex:1063-1078, 1173-1185);
* |pressureLower|, |pressureUpper|, |radius|, |hradius| — the two pressure
  localization limits and the common tilt interval; the lower pressure was
  identified with the assembled Palm readout by
  FinslerOriginalPressureLowerAssembly.pressureLower_eq_sceneReadout_of_tileIdentification
  (and, from the Palm sample law fields, by
  FinslerOriginalPressureLowerReadout.pressureLower_eq_sceneReadout_of_palmSampleLaw);
* |hvalue| — the legal-repair/value identification closing the pressure bracket;
  the constructor |ofStationaryScreening| reuses the value-input assembly
  (FinslerOriginalValueInputAssembly.finalValueIdentification_of_stationaryScreening);
* |hprob|, |hupper| — the original iid lower/upper pressure localization for the
  intrinsic length cost at the paper scale.

No |sorry|, |admit| or added axiom occurs.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-! ## 1. The conditional endgame structure -/

/-- **The remaining paper-data of the general Finsler selector**, in one
structure: the paper-side geometric hypotheses (|geometric|: the calibrated tube,
the a.e. Borel ray-cluster data, pointwise clock atomlessness, the Palm sample
law) together with the reduced named fields of the final inputs, stated in the
exact consumer interfaces of |FinslerSelectorFinalInputsAudit|. -/
structure FinslerConditionalEndgameHypotheses
    (F : ContinuousFinslerNorm E M) (u : M → ℝ) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) where
  /-- The paper-side geometric hypotheses: the single geometric hypothesis
  (calibrated tube) plus the a.e. Borel ray-cluster data, pointwise clock
  atomlessness and the Palm sample law. -/
  geometric : FinslerPaperGeometricHypotheses F u μ ν
  /-- The lower pressure localization limit (consumer interface). -/
  pressureLower : FinalPressureField A B
  /-- The upper pressure localization limit (consumer interface). -/
  pressureUpper : FinalPressureField A B
  /-- The common tilt interval (consumer interface). -/
  radius : FinalRadiusField A B
  /-- The tilt interval is positive at every probe (consumer interface). -/
  hradius : FinalPositiveRadius radius
  /-- The legal-repair/value identification closing the pressure bracket
  (consumer interface). -/
  hvalue : FinalValueIdentification pressureLower pressureUpper
  /-- The original iid lower pressure localization for the intrinsic length cost
  (consumer interface). -/
  hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius
  /-- The original iid upper pressure localization for the intrinsic length cost
  (consumer interface). -/
  hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius

namespace FinslerConditionalEndgameHypotheses

variable {u : M → ℝ} {μ ν : ProbabilityMeasure M}
  {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
  {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
  {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}
  {X Y : ∀ n, Fin (n + 1) → Ω n → M}

/-- The conditional endgame structure yields the named audit structure of the
four explicit open analytic inputs. -/
def toAudit (D : FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y) :
    FinslerSelectorFinalInputsAudit F μ ν hA hB hμA hνB P X Y u :=
  { pressureLower := D.pressureLower
    pressureUpper := D.pressureUpper
    radius := D.radius
    hradius := D.hradius
    hvalue := D.hvalue
    hprob := D.hprob
    hupper := D.hupper }

/-- The conditional endgame structure yields the consumer structure
|FinslerSelectorFinalInputs|, through the wiring lemma
|FinslerSelectorFinalInputsAudit.toFinalInputs|. -/
def toFinalInputs (D : FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y) :
    FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u :=
  D.toAudit.toFinalInputs

/-- **The consumer final inputs are nonempty** as soon as the conditional
endgame structure is supplied. -/
theorem nonempty_finalInputs
    (D : FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y) :
    Nonempty (FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :=
  ⟨D.toFinalInputs⟩

/-- The named audit structure of the explicit open inputs is nonempty. -/
theorem nonempty_audit
    (D : FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y) :
    Nonempty (FinslerSelectorFinalInputsAudit F μ ν hA hB hμA hνB P X Y u) :=
  ⟨D.toAudit⟩

/-- The Palm readout identification carried by the paper-side Palm sample law:
the normalized sample mean of the masked frozen cost converges to the population
tile value. -/
theorem palmReadout_tendsto
    (D : FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y) :
    Tendsto (fun n ↦ D.geometric.palm_sample_law.normalization n *
      D.geometric.palm_sample_law.maskedMean n -
      D.geometric.palm_sample_law.populationValue n) atTop (𝓝 0) :=
  D.geometric.palmReadout_tendsto

/-- The geometric field supplies the nonempty exact chart datum. -/
theorem nonempty_chartData
    (D : FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    Nonempty (CoreSectionChartData F u) :=
  D.geometric.nonempty_chartData hF hcomplete hu

/-- **The window side of the endgame from the conditional endgame structure**:
the open-domain window data (with open full-measure sets) and the calibrated
level-seed patches, together with the Palm readout identification. -/
theorem windowSide_endgame
    (D : FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) (μchart : Measure E) :
    (∃ (Seed : ℕ → F.CalibratedSeedWindow u)
      (κs : ∀ j, Measure (Seed j).seed.covector.ker)
      (W : WindowChartDataAe (F := F) (u := u) κs μchart),
      (∀ j, IsOpen ((W.chartData j).good)) ∧
        (∀ j, (W.chartData j).σ 0 ∈ (W.chartData j).good)) ∧
    (∃ (Seed : ℕ → F.CalibratedSeedWindow u) (W : WindowChartData Seed),
      ∀ j, ∃ (A' : F.CalibratedLevelSeedPatch u)
          (e : A'.covector.ker ≃L[ℝ] (W.chartData j).p.ker),
        A'.openLabels = e ⁻¹' (W.chartData j).V ∧
          A'.labels = e ⁻¹' ((W.chartData j).V ∩
            (W.chartData j).σ ⁻¹' (W.parentCore j)) ∧
            (∀ w t, A'.curve w t =
              (W.chartData j).Γ ((W.chartData j).σ (e w)) t) ∧
              A'.level = (W.chartData j).q) ∧
    Tendsto (fun n ↦ D.geometric.palm_sample_law.normalization n *
      D.geometric.palm_sample_law.maskedMean n -
      D.geometric.palm_sample_law.populationValue n) atTop (𝓝 0) :=
  D.geometric.windowSide_endgame hF hcomplete hu μchart

/-- **The conditional endgame structure with the value identification derived
from the legal-pressure value lane.**  The |hvalue| field is not assumed: it is
produced from a stationary pressure datum through the value-input assembly
|finalValueIdentification_of_stationaryScreening| (the Palm reserve-screening /
zero repair-budget data of the paper). -/
def ofStationaryScreening
    {W : Type*} {G Cb : ℝ}
    (geometric : FinslerPaperGeometricHypotheses F u μ ν)
    (pressureLower pressureUpper : FinalPressureField A B) (radius : FinalRadiusField A B)
    (hradius : FinalPositiveRadius radius)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    (hscreen : ∀ (f : FinalProbeSpace A B) (v : ℝ) (Q : W), Q ∈ (datum f).Cw →
      ∀ ε : ℝ, 0 < ε →
        ∃ Q' ∈ (datum f).C2,
          (datum f).K Q' + v * (datum f).P Q' <
            (datum f).K Q + v * (datum f).P Q + ε)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius) :
    FinslerConditionalEndgameHypotheses F u μ ν hA hB hμA hνB P X Y where
  geometric := geometric
  pressureLower := pressureLower
  pressureUpper := pressureUpper
  radius := radius
  hradius := hradius
  hvalue := finalValueIdentification_of_stationaryScreening datum hL hU hscreen
  hprob := hprob
  hupper := hupper

end FinslerConditionalEndgameHypotheses

/-! ## 2. The conditional endgame theorem -/

/-- **The conditional endgame of the general Finsler selector.**

Under the paper's population and iid sampling data, there is one common
calibrated potential |u| such that, for every conditional endgame structure for
|u| (the remaining paper-data: the paper-side geometric hypotheses plus the
reduced named fields of the final inputs), the consumer final inputs are
nonempty, the Palm readout identification holds, the readout derivative of the
limiting lower pressure at zero exists for every probe, and the unique
deterministic population optimal plan exists with whole-optimal-set convergence
in probability, the metric-sup convergence and the population optimality of the
limit plan.

The conclusion is exactly the conclusion of
|existsUnique_general_finsler_selector_final| with the universal quantification
over the consumer input structure instantiated by the conditional endgame
structure; in particular the readout input is discharged by that theorem and no
fifth input is assumed. -/
theorem existsUnique_general_finsler_selector_conditional_endgame
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (physicalSourceProbability ωM ρ₀ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (physicalTargetProbability ωM ρ₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n)) :
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃ u : M → ℝ, (let _instFinalPotentialMetric : MetricSpace M := F.metricSpace
        LipschitzWith 1 u) ∧
      ∀ (D : FinslerConditionalEndgameHypotheses F u
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          hA hB hμA hνB P X Y),
        Nonempty (FinslerSelectorFinalInputs F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          hA hB hμA hνB P X Y u) ∧
        Tendsto (fun n ↦ D.geometric.palm_sample_law.normalization n *
          D.geometric.palm_sample_law.maskedMean n -
          D.geometric.palm_sample_law.populationValue n) atTop (𝓝 0) ∧
        ∃ derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ,
          (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
            HasDerivAt (fun t ↦ D.pressureLower f t) (derivative f) 0) ∧
          ∃! π : ProbabilityMeasure (M × M),
            (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
              ∫ z, f z ∂((π : Measure (M × M)).comap
                (Prod.map ((↑) : ↥(A ∪ B) → M) ((↑) : ↥(A ∪ B) → M))) = derivative f) ∧
            (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
              {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U}) atTop (𝓝 0)) ∧
            (∀ d : ProbabilityMeasure (M × M) → ProbabilityMeasure (M × M) → ℝ,
              d π π = 0 →
              (∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure (M × M) | d γ π < ε}) →
              ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real
                {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                  (fun i ↦ X n i s) (fun i ↦ Y n i s), ε ≤ d γ π}) atTop (𝓝 0)) ∧
            IsOptimalCoupling edist
              (physicalSourceProbability ωM ρ₀ : Measure M)
              (physicalTargetProbability ωM ρ₁ : Measure M) (π : Measure (M × M)) := by
  obtain ⟨u, hu, hmain⟩ := existsUnique_general_finsler_selector_final
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
    hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY
  refine ⟨u, hu, ?_⟩
  intro D
  have hne : Nonempty (FinslerSelectorFinalInputs F
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
      hA hB hμA hνB P X Y u) := D.nonempty_finalInputs
  have hpalm := D.palmReadout_tendsto
  obtain ⟨derivative, hderiv, huniq⟩ := hmain D.toFinalInputs
  have hderiv' : ∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
      HasDerivAt (fun t ↦ D.pressureLower f t) (derivative f) 0 := by
    simpa only [FinslerConditionalEndgameHypotheses.toFinalInputs,
      FinslerConditionalEndgameHypotheses.toAudit,
      FinslerSelectorFinalInputsAudit.toFinalInputs] using hderiv
  exact ⟨hne, hpalm, derivative, hderiv', huniq⟩

end OTSelector.Reconstruction
