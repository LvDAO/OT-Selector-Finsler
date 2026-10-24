import OTSelector.Reconstruction.FinslerGeneralSelectorAssemblyInputs

/-!
# Paper-literal corollary of the four-input general Finsler selector

This module restates the conclusion of the four-input assembly
(`existsUnique_general_finsler_selector_of_four_inputs`) in the form closest to
the paper theorem "General Finsler empirical distance selection"
(`main.tex`, `thm:general-finsler-selector`).

The paper's conclusion is: there is a deterministic population
distance-optimal plan `π_*` such that for every metric `d_weak` inducing weak
convergence on probabilities, the entire empirical optimal set converges to
`π_*` in `d_weak`-supremum in probability.  The readout derivative and the
readout formula of the assembly are internal here and do not appear in the
statement.

Correspondences with the paper data:

* `F.IsSmoothStronglyConvex` is the smooth strongly convex Finsler data
  (smooth energy on nonzero vectors, positive Hessian); reversibility follows
  from positive homogeneity of the fiber length, so it is not a separate
  hypothesis;
* `F.metricSpace` is the intrinsic length metric: its `edist` is exactly
  `F.lengthEDist`, the original path-length cost (and it preserves the
  manifold topology);
* `physicalSourceProbability ωM ρ₀` is `ωM.withDensity (ofReal ∘ ρ₀)`, the
  density-weighted volume `ρ_A m`;
* `Pressure.empiricalOptimalFace` is the *entire* optimal coupling set of the
  original empirical marginals (fractional optima included);
* `(P n).real` is the outer measure, matching "in probability" for possibly
  nonmeasurable empirical-event sets;
* `d π π = 0` together with weak-open balls is the formal counterpart of a
  metric `d_weak` inducing weak convergence.

The four analytic inputs `hradius`, `hvalue`, `hprob`, `hupper` remain the
still-open hypotheses of the paper's stages (iii)/(iv); the population data and
the calibrated potential are produced internally.
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

/-- **Paper-literal general Finsler empirical distance selection.**

Under the paper's population and iid sampling data, and for the internally
produced calibrated potential, the four open analytic inputs yield a
deterministic population optimal plan `π` such that: every probability
neighborhood of `π` is eventually entered by the entire empirical optimal
face in outer probability (equivalently, for every metric inducing weak
convergence, the supremum distance of the whole empirical optimal set to `π`
tends to zero in probability).  All fractional optima are included. -/
theorem exists_finsler_empirical_distance_selection
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
        ∃ π : ProbabilityMeasure (M × M),
          IsOptimalCoupling edist
            (physicalSourceProbability ωM ρ₀ : Measure M)
            (physicalTargetProbability ωM ρ₁ : Measure M) (π : Measure (M × M)) ∧
          (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
            {s | ∃ γ ∈ Pressure.empiricalOptimalFace
              (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U}) atTop (𝓝 0)) ∧
          (∀ d : ProbabilityMeasure (M × M) → ProbabilityMeasure (M × M) → ℝ,
            d π π = 0 →
            (∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure (M × M) | d γ π < ε}) →
            ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real
              {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                (fun i ↦ X n i s) (fun i ↦ Y n i s), ε ≤ d γ π}) atTop (𝓝 0)) := by
  obtain ⟨u, hu, hmain⟩ := existsUnique_general_finsler_selector_of_four_inputs
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
    hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY
  refine ⟨u, hu, ?_⟩
  intro pressureLower pressureUpper radius hradius hvalue hprob hupper
  obtain ⟨derivative, _hderiv, huniq⟩ := hmain
    pressureLower pressureUpper radius hradius hvalue hprob hupper
  obtain ⟨π, hπ, _hunique⟩ := huniq
  exact ⟨π, hπ.2.2.2, hπ.2.1, hπ.2.2.1⟩

end OTSelector.Reconstruction
