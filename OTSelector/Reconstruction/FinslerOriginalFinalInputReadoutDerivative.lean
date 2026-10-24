import OTSelector.Reconstruction.FinslerOriginalEndgameActualWired

/-!
# Readout differentiability from the actual final inputs

At `paperCalibratedPotential`, the population theorem already supplies differentiability
of every pressure that is a local pointwise limit of the physical semidiscrete means.
The actual lower probability bound, upper expectation bound and value identification
in `FinslerSelectorFinalInputs` give exactly that convergence. Consequently the readout
derivative is derived from the existing endgame data on arbitrary iid sample spaces;
no auxiliary paper geometric bundle or derivative hypothesis is needed.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- At the same derived population potential, the actual four-field final inputs
supply their own readout derivative on every original iid sampling model. -/
theorem finslerReadoutTiltDerivative_of_finalInputs
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
    (D : FinslerSelectorFinalInputs F
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
      hA hB hμA hνB P X Y
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)) :
    FinslerReadoutTiltDerivative D.pressureLower := by
  classical
  let μP : ProbabilityMeasure M := physicalSourceProbability ωM ρ₀
  let νP : ProbabilityMeasure M := physicalTargetProbability ωM ρ₁
  let u := paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
    hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
  let K : Set M := A ∪ B
  let : MetricSpace M := F.metricSpace
  have hK : IsCompact K := hA.union hB
  have hμK : ∀ᵐ x ∂(μP : Measure M), x ∈ K := hμA.mono fun _ hx ↦ Or.inl hx
  have hνK : ∀ᵐ y ∂(νP : Measure M), y ∈ K := hνB.mono fun _ hy ↦ Or.inr hy
  have hρ₀L : LipschitzWith K₀ ρ₀ := hρ₀
  have hρ₁L : LipschitzWith K₁ ρ₁ := hρ₁
  have hμchart : ∀ old : M, (((μP : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact chartwise_ac_withDensity_of_volume_density ωM m
      hρ₀L.continuous.measurable hρ₀nonneg v hv hvolume old
  have hνchart : ∀ old : M, (((νP : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact chartwise_ac_withDensity_of_volume_density ωM m
      hρ₁L.continuous.measurable hρ₁nonneg v hv hvolume old
  obtain ⟨hu, hdiff⟩ := paperCalibratedPotential_spec hF hcomplete hdim m ωM ρ₀ ρ₁
    hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
  have hconv : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < D.radius f →
      Tendsto (fun n ↦ finslerSemidiscreteMean F μP νP K hK hμK hνK u f t n)
        atTop (𝓝 (D.pressureLower f t)) := by
    intro f t ht
    apply tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper
      hF hcomplete m (by omega) μP νP hμchart hνchart K hK hμK hνK
      P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu f t (D.pressureLower f t)
    · exact fun ε hε ↦ D.hprob f t ε ht hε
    · intro ε hε
      filter_upwards [D.hupper f t ε ht hε] with n hn
      rwa [← D.hvalue f t] at hn
  have hderiv : ∀ f : FinalProbeSpace A B,
      ∃ d : ℝ, HasDerivAt (fun t ↦ D.pressureLower f t) d 0 := by
    intro f
    apply hdiff K hK hμK hνK f (D.pressureLower f) (D.hradius f)
    intro t ht
    exact hconv f t (abs_lt.mpr ht)
  choose derivative hderivative using hderiv
  exact ⟨derivative, hderivative⟩

end OTSelector.Reconstruction
