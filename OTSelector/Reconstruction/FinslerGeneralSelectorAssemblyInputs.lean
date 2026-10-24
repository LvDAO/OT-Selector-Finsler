import OTSelector.Reconstruction.FinslerGeneralSelectorAssemblyFinal

/-!
# Concrete four-input form of the general Finsler selector

The final assembly `FinslerGeneralSelectorAssemblyFinal` takes its open
analytic inputs bundled as the structure `FinslerSelectorFinalInputs`.  This
module provides the integration wrapper with the four open statements as
plain named hypotheses in exactly the shapes the assembly consumes:

* `hradius` — the pressure convergence strip is positive at every probe;
* `hvalue` — the legal-repair/value identification
  `pressureLower = pressureUpper` closing the pressure bracket (the paper's
  focal value equality);
* `hprob` — the original iid probability lower pressure localization for the
  intrinsic length cost at the paper scale `(n+1)^(2/q)`, `q = d - 1`;
* `hupper` — its expectation upper pressure localization.

The common calibrated potential is produced internally from the paper's
population data (it is not a caller input).  The wrapper builds
`FinslerSelectorFinalInputs` from the four hypotheses, applies the final
assembly, and concludes the paper theorem: a readout derivative function, the
readout formula, whole empirical optimal face convergence in outer
probability, the paper-literal metric-sup convergence, and the population
optimality of the limit plan.

Hypothesis-to-team-task mapping (current board): `hprob` is supplied by the
pressure-lower lane (tasks 9/18), `hupper` by the pressure-upper lane (tasks
8/16), `hvalue` by the value-equality lane (tasks 10/19), and `hradius` is
bookkeeping of the same pressure producer (convergence strip, tracked with
tasks 16/18).  Nothing else remains open.
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

/-- **General Finsler selector from the four named open inputs.**

Takes the paper's population and iid sampling data plus, for the internally
produced calibrated potential, the four concrete analytic statements
`hradius`, `hvalue`, `hprob`, `hupper`; builds
`FinslerSelectorFinalInputs` from them and applies the final assembly. -/
theorem existsUnique_general_finsler_selector_of_four_inputs
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
      ∀ (pressureLower pressureUpper : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
        (radius : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ)
        (hradius : ∀ f, 0 < radius f)
        (hvalue : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
          pressureLower f t = pressureUpper f t)
        (hprob : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
          |t| < radius f → 0 < ε →
          Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F
            (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
            (A ∪ B) (hA.union hB).measurableSet
            (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
            (fun i ↦ X n i s) (fun i ↦ Y n i s) u
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
              pressureLower f t - ε}) atTop (𝓝 0))
        (hupper : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
          |t| < radius f → 0 < ε →
          ∀ᶠ n in atTop,
            ∫ s, finslerSupportedPressure F
              (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
              (A ∪ B) (hA.union hB).measurableSet
              (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
              (fun i ↦ X n i s) (fun i ↦ Y n i s) u
              (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤
                pressureUpper f t + ε),
        ∃ derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ,
          (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
            HasDerivAt (fun t ↦ pressureLower f t) (derivative f) 0) ∧
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
  intro pressureLower pressureUpper radius hradius hvalue hprob hupper
  exact hmain
    { pressureLower := pressureLower
      pressureUpper := pressureUpper
      radius := radius
      hradius := hradius
      hvalue := hvalue
      hprob := hprob
      hupper := hupper }

end OTSelector.Reconstruction
