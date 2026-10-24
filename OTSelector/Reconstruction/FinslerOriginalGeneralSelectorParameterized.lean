import OTSelector.Reconstruction.FinslerOriginalEndgameFieldsAssembly
import OTSelector.Limit.FinslerPressureSqueeze

/-!
# The general Finsler selector at a given potential

The final assembly theorem
existsUnique_general_finsler_selector_final produces an opaque potential from
the original physical pressure construction and then proves the selector
conclusion for every final-input structure at that potential.  For the
paper-facing theorem the data must instead be assumed at the *calibrated
potential of the paper*, which resolves the vacuity of assuming the endgame
data for every 1-Lipschitz potential (flag F10).

This module removes the existential potential: at a given potential
|u : M → ℝ| with |LipschitzWith 1 u| (with respect to the intrinsic Finsler
metric space |F.metricSpace|), the same selector conclusion holds for every
final-input structure at |u|, and hence for the paper endgame data
|FinslerPaperEndgameData ... u| and for the conditional endgame structure
|FinslerConditionalEndgameHypotheses ... u|.

The whole proof of the convergence, the unique plan, the whole-optimal-face
convergence in outer probability and the optimality of the limit plan is the
assembly proof, reused verbatim; the only difference is that the readout
derivative function is no longer produced by the opaque potential construction
|exists_potential_and_derivative_of_original_physical_pressure| but is an
input.

## The one remaining derivative-existence input

The derivative existence is not derivable from the value identification
|hvalue| alone (nor from the lower/upper pressure localization data): no lemma
of the repository produces |HasDerivAt| of a limiting pressure from a value
identity, and the value functions of stationary problems are in general not
differentiable at zero without an extra tie-breaking input.  It is therefore
isolated as the single named predicate |FinslerReadoutTiltDerivative|:

  FinslerReadoutTiltDerivative (pressureLower : FinalPressureField A B) : Prop
  := ∃ derivative : FinalProbeSpace A B → ℝ,
       ∀ f : FinalProbeSpace A B,
         HasDerivAt (fun t : ℝ ↦ pressureLower f t) (derivative f) 0

i.e. exactly the readout derivative at zero of the limiting lower pressure, for
every probe.  The remaining paper inputs are those of
|FinslerSelectorFinalInputs| (pressureLower, pressureUpper, radius/hradius,
hvalue, hprob, hupper) together with the paper population and iid sampling data;
the paper endgame datum supplies the former, and its |pressureLower| must carry
|FinslerReadoutTiltDerivative|.

No |sorry|, |admit| or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-! ## 1. The single remaining derivative-existence input -/

/-- **The readout derivative at zero of a limiting pressure.**  This is the one
remaining named input at a given potential: the tilt derivative at zero of the
limiting lower pressure, for every probe. -/
def FinslerReadoutTiltDerivative {A B : Set M} (pressureLower : FinalPressureField A B) : Prop :=
  ∃ derivative : FinalProbeSpace A B → ℝ,
    ∀ f : FinalProbeSpace A B,
      HasDerivAt (fun t : ℝ => pressureLower f t) (derivative f) 0

/-! ## 2. The parameterized final theorem -/

/-- **The final general Finsler selector at a given potential.**

At a given potential |u| (1-Lipschitz for the intrinsic Finsler metric) and for
every final-input structure at |u| whose limiting lower pressure carries the
readout derivative at zero, the assembly conclusion holds: there is a readout
derivative function, a unique deterministic population optimal plan with the
readout formula, whole-optimal-face convergence in outer probability, the
metric-sup form of that convergence, and optimality of the limit plan for the
intrinsic Finsler length cost. -/
theorem existsUnique_general_finsler_selector_at_potential_inputs
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
      (fun sample i ↦ Y n i sample) (P n))
    (u : M → ℝ)
    (hu : let _instFinalPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∀ (inputs : FinslerSelectorFinalInputs F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          hA hB hμA hνB P X Y u),
        FinslerReadoutTiltDerivative inputs.pressureLower →
        ∃ derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ,
          (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
            HasDerivAt (fun t ↦ inputs.pressureLower f t) (derivative f) 0) ∧
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
  let μP : ProbabilityMeasure M := physicalSourceProbability ωM ρ₀
  let νP : ProbabilityMeasure M := physicalTargetProbability ωM ρ₁
  let K : Set M := A ∪ B
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  have hdim2 : 2 ≤ Module.finrank ℝ E := by omega
  have hK : IsCompact K := hA.union hB
  have hμK : ∀ᵐ x ∂(μP : Measure M), x ∈ K := hμA.mono fun x hx ↦ Or.inl hx
  have hνK : ∀ᵐ y ∂(νP : Measure M), y ∈ K := hνB.mono fun y hy ↦ Or.inr hy
  have hρ₀L : LipschitzWith K₀ ρ₀ := hρ₀
  have hρ₁L : LipschitzWith K₁ ρ₁ := hρ₁
  have hμchart : ∀ old : M, (((μP : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact OTSelector.Geometry.chartwise_ac_withDensity_of_volume_density ωM m
      hρ₀L.continuous.measurable hρ₀nonneg v hv hvolume old
  have hνchart : ∀ old : M, (((νP : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact OTSelector.Geometry.chartwise_ac_withDensity_of_volume_density ωM m
      hρ₁L.continuous.measurable hρ₁nonneg v hv hvolume old
  refine fun inputs hderivInput => ?_
  have hupper' : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
      |t| < inputs.radius f → 0 < ε → ∀ᶠ n in atTop,
        ∫ s, finslerSupportedPressure F μP νP (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤
            inputs.pressureLower f t + ε := by
    intro f t ε ht hε
    filter_upwards [inputs.hupper f t ε ht hε] with n hn
    rwa [← inputs.hvalue f t] at hn
  have hconv : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      |t| < inputs.radius f →
      Tendsto (fun n ↦ finslerSemidiscreteMean F μP νP K hK hμK hνK u f t n)
        atTop (𝓝 (inputs.pressureLower f t)) := by
    intro f t ht
    exact tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper
      hF hcomplete m hdim2 μP νP hμchart hνchart K hK hμK hνK P X Y hX hY hXi hYi
      hXlaw hYlaw hXY u hu f t (inputs.pressureLower f t)
      (fun ε hε ↦ inputs.hprob f t ε ht hε)
      (fun ε hε ↦ hupper' f t ε ht hε)
  obtain ⟨derivative, hderiv⟩ := hderivInput
  refine ⟨derivative, hderiv, ?_⟩
  obtain ⟨π, hπ, huniq⟩ := existsUnique_selector_of_finsler_semidiscrete_convergence
    hF hcomplete m hdim μP νP hμchart hνchart K hK hμK hνK P X Y hX hY hXi hYi
    hXlaw hYlaw hXY u hu inputs.pressureLower inputs.radius derivative inputs.hradius hconv hderiv
  refine ⟨π, ⟨hπ.1, hπ.2.1, ?_, hπ.2.2⟩, ?_⟩
  · intro d hd0 hdopen ε hε
    exact OTSelector.tendsto_measureReal_exists_metric_le_of_forall_nhds P
      (fun n s ↦ Pressure.empiricalOptimalFace
        (fun i ↦ X n i s) (fun i ↦ Y n i s))
      π d hd0 hdopen hπ.2.1 ε hε
  · intro π' hπ'
    exact huniq π' ⟨hπ'.1, hπ'.2.1, hπ'.2.2.2⟩

/-! ## 3. The paper endgame data at a given potential -/

/-- **The general Finsler selector at a given potential, from the conditional
endgame structure of the paper.**  The data are assumed at the calibrated
potential itself, not for all Lipschitz potentials. -/
theorem existsUnique_general_finsler_selector_at_potential
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
      (fun sample i ↦ Y n i sample) (P n))
    (u : M → ℝ)
    (hu : let _instFinalPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (D : FinslerConditionalEndgameHypotheses F u
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
      hA hB hμA hνB P X Y)
    (hderiv : FinslerReadoutTiltDerivative D.pressureLower) :
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
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
  have hmain := existsUnique_general_finsler_selector_at_potential_inputs
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
    hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
  obtain ⟨derivative, hder, huniq⟩ := hmain D.toFinalInputs hderiv
  exact ⟨D.nonempty_finalInputs, D.palmReadout_tendsto, derivative, hder, huniq⟩

/-- **The general Finsler selector at a given potential, from the paper endgame
data.**  This is the paper-facing interface: the paper endgame data are assumed
at the calibrated potential, so the wrapper is not vacuous. -/
theorem existsUnique_general_finsler_selector_at_potential_paperData
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
      (fun sample i ↦ Y n i sample) (P n))
    (u : M → ℝ)
    (hu : let _instFinalPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (D : FinslerPaperEndgameData F
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
      hA hB hμA hνB P X Y u)
    (hderiv : FinslerReadoutTiltDerivative D.pressureLower) :
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
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
  exact existsUnique_general_finsler_selector_at_potential
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
    hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
    D.toConditionalEndgame hderiv

end OTSelector.Reconstruction
