import OTSelector.Transport.EmpiricalSelector.Existence
import OTSelector.Transport.EmpiricalSelector.CarrierLift

/-! The original general Finsler empirical selector, before every iid sampling model. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open OTSelector.Geometry OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original general Finsler empirical selector on the literal physical carrier A × B.
One population-optimal plan is fixed before every independent iid realization, and the
entire fractional empirical optimal face converges to it for every weakly open ball. -/
theorem exists_original_general_finsler_empirical_selector_on_carriers
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
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    let μp := physicalSourceProbability ωM ρ₀
    let νp := physicalTargetProbability ωM ρ₁
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃ πAB : ProbabilityMeasure (A × B),
      IsOptimalCoupling (fun (x : A) (y : B) ↦ edist (x : M) (y : M))
        (probabilityOnSubset μp A hA.measurableSet hμ)
        (probabilityOnSubset νp B hB.measurableSet hν) (πAB : Measure (A × B)) ∧
      ∀ {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
        (R : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (R n)]
        (X Y : ∀ n, Fin (n + 1) → Ω n → M),
        (∀ n i, Measurable (X n i)) → (∀ n i, Measurable (Y n i)) →
        (∀ n, iIndepFun (X n) (R n)) → (∀ n, iIndepFun (Y n) (R n)) →
        (∀ n i, (R n).map (X n i) = (μp : Measure M)) →
        (∀ n i, (R n).map (Y n i) = (νp : Measure M)) →
        (∀ n, IndepFun (fun ξ i ↦ X n i ξ) (fun ξ i ↦ Y n i ξ) (R n)) →
        (∀ U ∈ 𝓝 πAB, Tendsto (fun n ↦ (R n).real
          {s | ∃ γ ∈ carrierEmpiricalFace
            (fun i ↦ supportedVersion μp A hA.measurableSet hμ (X n i) s)
            (fun i ↦ supportedVersion νp B hB.measurableSet hν (Y n i) s), γ ∉ U})
          atTop (𝓝 0)) ∧
        (∀ d : ProbabilityMeasure (A × B) → ProbabilityMeasure (A × B) → ℝ,
          d πAB πAB = 0 →
          (∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure (A × B) | d γ πAB < ε}) →
          ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (R n).real
            {s | ∃ γ ∈ carrierEmpiricalFace
              (fun i ↦ supportedVersion μp A hA.measurableSet hμ (X n i) s)
              (fun i ↦ supportedVersion νp B hB.measurableSet hν (Y n i) s), ε ≤ d γ πAB})
            atTop (𝓝 0)) := by
  let μp := physicalSourceProbability ωM ρ₀
  let νp := physicalTargetProbability ωM ρ₁
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  obtain ⟨π, hopt, hgeneral⟩ := exists_original_general_finsler_empirical_selector
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg
    v hv hvnonneg hvolume hA hB hAB hμ hν
  obtain ⟨πAB, hπAB, _hunique⟩ := existsUnique_originalGeneralSelectorCarrierLift
    μp νp hA hB hμ hν π hopt
  refine ⟨πAB, hπAB.1, ?_⟩
  intro Ω _ R _ X Y hX hY hXi hYi hXlaw hYlaw hXY
  have hface := (hgeneral R X Y hX hY hXi hYi hXlaw hYlaw hXY).1
  refine ⟨originalGeneralSelectorCarrierLift_wholeFace μp νp hA hB hμ hν π πAB hπAB.2
    R X Y hX hY hXlaw hYlaw hface, ?_⟩
  intro d hd0 hdopen
  exact originalGeneralSelectorCarrierLift_metric μp νp hA hB hμ hν π πAB hπAB.2
    R X Y hX hY hXlaw hYlaw hface d hd0 hdopen

end OTSelector.Reconstruction
