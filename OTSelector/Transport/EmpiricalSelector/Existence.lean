import OTSelector.Transport.EmpiricalSelector.WithReadout

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

/-- The two original physical populations have one deterministic intrinsic-length optimal
plan to which their entire empirical optimal face, including fractional couplings, converges
in outer probability on every independent iid implementation. No final-input structure,
pressure field, local comparison, derivative, potential or atlas is assumed. -/
theorem exists_original_general_finsler_empirical_selector
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
    ∃ π : ProbabilityMeasure (M × M),
      IsOptimalCoupling edist (μp : Measure M) (νp : Measure M) (π : Measure (M × M)) ∧
      ∀ {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
        (R : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (R n)]
        (X Y : ∀ n, Fin (n + 1) → Ω n → M),
        (∀ n i, Measurable (X n i)) → (∀ n i, Measurable (Y n i)) →
        (∀ n, iIndepFun (X n) (R n)) → (∀ n, iIndepFun (Y n) (R n)) →
        (∀ n i, (R n).map (X n i) = (μp : Measure M)) →
        (∀ n i, (R n).map (Y n i) = (νp : Measure M)) →
        (∀ n, IndepFun (fun ξ i ↦ X n i ξ) (fun ξ i ↦ Y n i ξ) (R n)) →
        (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (R n).real
          {s | ∃ γ ∈ Pressure.empiricalOptimalFace
            (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U}) atTop (𝓝 0)) ∧
        (∀ d : ProbabilityMeasure (M × M) → ProbabilityMeasure (M × M) → ℝ,
          d π π = 0 →
          (∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure (M × M) | d γ π < ε}) →
          ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (R n).real
            {s | ∃ γ ∈ Pressure.empiricalOptimalFace
              (fun i ↦ X n i s) (fun i ↦ Y n i s), ε ≤ d γ π}) atTop (𝓝 0)) := by
  obtain ⟨derivative, π, hπ, _hunique⟩ :=
    existsUnique_original_general_finsler_selector_with_readout
      hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg
      v hv hvnonneg hvolume hA hB hAB hμ hν
  exact ⟨π, hπ.2⟩

end OTSelector.Reconstruction
