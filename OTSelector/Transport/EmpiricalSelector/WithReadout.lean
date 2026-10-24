import OTSelector.Transport.EmpiricalSelector.PopulationPressure
import OTSelector.Transport.EmpiricalSelector.ReadoutUniqueness

/-! One population selector for every independent iid realization of the two physical populations. -/
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

/-- The unique population plan with the constructed population readouts selects the entire
empirical optimal face on every independent iid sampling model. The plan is quantified
before all external sample spaces, sample laws and coordinate arrays. -/
theorem existsUnique_original_general_finsler_selector_with_readout
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
    ∃ derivative : FinalProbeSpace A B → ℝ, ∃! π : ProbabilityMeasure (M × M),
      (∀ f : FinalProbeSpace A B,
        ∫ z, f z ∂((π : Measure (M × M)).comap
          (Prod.map ((↑) : ↥(A ∪ B) → M) ((↑) : ↥(A ∪ B) → M))) = derivative f) ∧
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
  let μp := physicalSourceProbability ωM ρ₀
  let νp := physicalTargetProbability ωM ρ₁
  let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
    hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  have hμK : ∀ᵐ x ∂(μp : Measure M), x ∈ A ∪ B := hμ.mono fun _ hx ↦ Or.inl hx
  have hνK : ∀ᵐ y ∂(νp : Measure M), y ∈ A ∪ B := hν.mono fun _ hy ↦ Or.inr hy
  have hμchart : ∀ old : M, (((μp : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact chartwise_ac_withDensity_of_volume_density ωM m
      hρ₀.continuous.measurable hρ₀nonneg v hv hvolume old
  have hνchart : ∀ old : M, (((νp : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact chartwise_ac_withDensity_of_volume_density ωM m
      hρ₁.continuous.measurable hρ₁nonneg v hv hvolume old
  obtain ⟨hu, pressure, radius, derivative, hradius, hderiv, hconv⟩ :=
    exists_original_population_semidiscrete_pressure hF hcomplete hdim m ωM ρ₀ ρ₁
      hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  obtain ⟨π, hπ, _hunique⟩ := existsUnique_selector_of_finsler_semidiscrete_convergence
    hF hcomplete m hdim μp νp hμchart hνchart (A ∪ B) (hA.union hB) hμK hνK
    (canonicalLaw μp νp) canonicalX canonicalY
    measurable_canonicalX measurable_canonicalY (iIndepFun_canonicalX μp νp)
    (iIndepFun_canonicalY μp νp) (canonicalLaw_map_canonicalX μp νp)
    (canonicalLaw_map_canonicalY μp νp) (indepFun_canonicalArrays μp νp)
    u hu pressure radius derivative hradius hconv hderiv
  refine ⟨derivative, π, ⟨hπ.1, hπ.2.2, ?_⟩, ?_⟩
  · intro Ω _ R _ X Y hX hY hXi hYi hXlaw hYlaw hXY
    obtain ⟨π', hπ', _hunique'⟩ := existsUnique_selector_of_finsler_semidiscrete_convergence
      hF hcomplete m hdim μp νp hμchart hνchart (A ∪ B) (hA.union hB) hμK hνK
      R X Y hX hY hXi hYi hXlaw hYlaw hXY u hu pressure radius derivative hradius hconv hderiv
    have heq : π' = π := populationCoupling_eq_of_compact_readouts μp νp (A ∪ B)
      (hA.union hB) hμK hνK hπ'.2.2.1 hπ.2.2.1
      (fun f ↦ (hπ'.1 f).trans (hπ.1 f).symm)
    have hface := hπ'.2.1
    rw [heq] at hface
    refine ⟨hface, ?_⟩
    intro d hd0 hdopen ε hε
    exact OTSelector.tendsto_measureReal_exists_metric_le_of_forall_nhds R
      (fun n s ↦ Pressure.empiricalOptimalFace (fun i ↦ X n i s) (fun i ↦ Y n i s))
      π d hd0 hdopen hface ε hε
  · intro π' hπ'
    exact populationCoupling_eq_of_compact_readouts μp νp (A ∪ B)
      (hA.union hB) hμK hνK hπ'.2.1.1 hπ.2.2.1
      (fun f ↦ (hπ'.1 f).trans (hπ.1 f).symm)

end OTSelector.Reconstruction
