import OTSelector.Reconstruction.FinslerGeneralSelectorAssembly
import OTSelector.Reconstruction.FinslerOriginalVanishingReadoutGap
import OTSelector.Limit.FinslerSemidiscretePressureData

/-!
# Final general Finsler selector assembly: the readout input is discharged

This module composes the paper-level five-input assembly
(`FinslerGeneralSelectorAssembly`), the vanishing finite readout gap theorem
(`FinslerOriginalVanishingReadoutGap`), and the physical semidiscrete endpoint
(`FinslerSemidiscretePressureData`) into one final endpoint whose only open
analytic inputs are the four hypotheses `hprob`, `hupper`, `hvalue`,
`hradius`.

The former fifth open input `hreadout` (differentiability of the limiting
pressure at zero) is produced internally: the paper's population data supply a
common calibrated potential and, through
`exists_potential_and_derivative_of_original_physical_pressure`, one readout
derivative function for every probe.

For the paper's population data (smooth positive volume, nonnegative Lipschitz
densities, compact disjoint supports, original iid sampling) the main theorem
yields a common optimal potential `u` such that, for every pressure bracket
satisfying the four open inputs, there is one readout derivative function and
a unique deterministic population optimal plan `π` with

* the readout formula `∫ f ∂(π.comap incl) = derivative f` for every probe;
* convergence in outer probability of the *entire* empirical optimal face
  (fractional optima included) to `π`;
* the paper-literal metric-sup form of that convergence;
* `π` is an optimal coupling for the intrinsic Finsler length cost.

The corollary records that the five-input assembly interface (the four inputs
plus explicit readout differentiability) yields the same conclusion as a
consequence of the four-input endpoint, so the paper theorem is conditional on
exactly four open inputs.
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

/-- The four explicit open analytic inputs of the final paper theorem for a
fixed compact carrier `A ∪ B`, potential and iid sampling model. -/
structure FinslerSelectorFinalInputs
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M) {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ) where
  /-- The lower pressure localization limit. -/
  pressureLower : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ
  /-- The upper pressure localization limit. -/
  pressureUpper : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ
  /-- The common tilt interval. -/
  radius : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ
  /-- The tilt interval is positive at every probe. -/
  hradius : ∀ f, 0 < radius f
  /-- The legal-repair/value identification closing the pressure bracket. -/
  hvalue : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
    pressureLower f t = pressureUpper f t
  /-- The original iid lower pressure localization for the intrinsic length cost. -/
  hprob : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
    |t| < radius f → 0 < ε →
    Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν
      (A ∪ B) (hA.union hB).measurableSet
      (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
      (fun i ↦ X n i s) (fun i ↦ Y n i s) u
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
        pressureLower f t - ε}) atTop (𝓝 0)
  /-- The original iid upper pressure localization for the intrinsic length cost. -/
  hupper : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
    |t| < radius f → 0 < ε →
    ∀ᶠ n in atTop,
      ∫ s, finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) u
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤
          pressureUpper f t + ε
/-- **Final general Finsler selector with the readout input discharged.**

The paper's population and iid sampling data plus the four open analytic inputs
`hprob`, `hupper`, `hvalue`, `hradius` produce the common optimal potential,
the readout derivative function, and the unique deterministic population
optimal plan with whole-optimal-set convergence in probability. -/
theorem existsUnique_general_finsler_selector_final
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
      ∀ (inputs : FinslerSelectorFinalInputs F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          hA hB hμA hνB P X Y u),
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
  obtain ⟨u, hu, hdifferentiable⟩ :=
    exists_potential_and_derivative_of_original_physical_pressure
      hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg
      v hv hvnonneg hvolume hA hB hAB hμA hνB
  refine ⟨u, hu, ?_⟩
  intro inputs
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
  obtain ⟨derivative, hderiv⟩ := hdifferentiable K hK hμK hνK
    inputs.pressureLower inputs.radius inputs.hradius hconv
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

/-- **Five-input compatibility corollary.**  The former fifth open input
`hreadout` is redundant: supplying it explicitly together with the four open
inputs still yields the same conclusion, and it now follows from the four-input
endpoint.  This records that the paper theorem is conditional on exactly four
open inputs. -/
theorem existsUnique_general_finsler_selector_five_input_corollary
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
      ∀ (inputs : FinslerSelectorFinalInputs F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          hA hB hμA hνB P X Y u)
        (derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ),
        (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
          HasDerivAt (fun t ↦ inputs.pressureLower f t) (derivative f) 0) →
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
  intro inputs derivative hreadout
  obtain ⟨deriv', hderiv', huniq⟩ := hmain inputs
  have hdeq : ∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ, derivative f = deriv' f :=
    fun f ↦ (hreadout f).unique (hderiv' f)
  obtain ⟨π, hπ, huniqπ⟩ := huniq
  refine ⟨π, ⟨?_, hπ.2⟩, ?_⟩
  · intro f
    rw [hπ.1 f, ← hdeq f]
  · intro π' hπ'
    exact huniqπ π' ⟨fun f ↦ by rw [hπ'.1 f, hdeq f], hπ'.2⟩

end OTSelector.Reconstruction
