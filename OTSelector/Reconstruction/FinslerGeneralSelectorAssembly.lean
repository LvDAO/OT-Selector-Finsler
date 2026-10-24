import OTSelector.Limit.FinslerPressureSqueeze
import OTSelector.Limit.PhysicalSelectorWrapper

/-!
# General Finsler selector assembly from the remaining analytic inputs

This module is the end-to-end assembly of the paper's main theorem
("General Finsler empirical distance selection").  It retains the paper's
population data on a complete connected smooth reversible strongly convex
Finsler manifold: a smooth positive volume, nonnegative Lipschitz source and
target densities, compact disjoint supports, and the original independent iid
empirical sampling model.  The empirical optimal set is the *entire* optimal
coupling set of the original length cost, so fractional optima are included.

The still-open analytic inputs of the general proof enter as the explicit
hypotheses below:

* `hprob` and `hupper`: the original iid lower and upper pressure
  localization for the intrinsic length cost, stated for the actual
  supported empirical pressure `finslerSupportedPressure` at the paper scale
  `(n+1)^(2/q)`, `q = d - 1`;
* `hvalue`: the legal-repair/value identification, i.e. the local value
  equality equating the lower and upper pressure limits (the paper's focal
  value equality closing the pressure bracket);
* `hreadout`: convergence/differentiability of the limiting pressure
  readout at zero tilt.

Under these inputs the module concludes weak convergence in probability of
the whole empirical optimal face to a deterministic population optimal plan,
first in the form "every weak neighborhood is eventually entered in outer
probability" and then in the paper-literal metric-sup form, for every metric
whose open balls are weak neighborhoods (in particular every metric inducing
weak convergence).

No density lower bound, support-boundary regularity, mass balance,
geometric separator, endpoint nonfocusing or raywise condition is assumed.
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

/-- Paper-literal general Finsler selector assembly.

The hypotheses `hprob`, `hupper`, `hvalue` and `hreadout` are exactly the
remaining analytic inputs: iid lower/upper pressure localization for the
intrinsic length cost, the legal-repair/value identification, and the
readout differentiability of the limiting pressure.  The conclusion is
whole-optimal-set convergence in probability. -/
theorem existsUnique_general_finsler_selector_of_open_inputs
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
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 φ)
    (pressureLower pressureUpper : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hvalue : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      pressureLower f t = pressureUpper f t)
    (hreadout : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ),
      HasDerivAt (fun t ↦ pressureLower f t) (derivative f) 0)
    (hprob : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
      |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F
        (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressureLower f t - ε}) atTop (𝓝 0))
    (hupper : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
      |t| < radius f → 0 < ε →
      ∀ᶠ n in atTop,
        ∫ s, finslerSupportedPressure F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤
            pressureUpper f t + ε) :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
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
  have hK : IsCompact K := hA.union hB
  have hμK : ∀ᵐ x ∂(μP : Measure M), x ∈ K := hμA.mono fun x hx ↦ Or.inl hx
  have hνK : ∀ᵐ y ∂(νP : Measure M), y ∈ K := hνB.mono fun y hy ↦ Or.inr hy
  have hρ₀L : LipschitzWith K₀ ρ₀ := hρ₀
  have hρ₁L : LipschitzWith K₁ ρ₁ := hρ₁
  have hφL : LipschitzWith 1 φ := hφ
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
  have hupper' : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
      |t| < radius f → 0 < ε → ∀ᶠ n in atTop,
        ∫ s, finslerSupportedPressure F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤
            pressureLower f t + ε := by
    intro f t ε ht hε
    filter_upwards [hupper f t ε ht hε] with n hn
    rwa [← hvalue f t] at hn
  obtain ⟨π, hπ, huniq⟩ := existsUnique_selector_of_finsler_squeeze
    hF hcomplete m hdim μP νP hμchart hνchart K hK hμK hνK
    P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφL
    pressureLower radius derivative hradius hreadout hprob hupper'
  refine ⟨π, ⟨hπ.1, hπ.2.1, ?_, hπ.2.2⟩, ?_⟩
  · intro d hd0 hdopen ε hε
    exact OTSelector.tendsto_measureReal_exists_metric_le_of_forall_nhds P
      (fun n s ↦ Pressure.empiricalOptimalFace
        (fun i ↦ X n i s) (fun i ↦ Y n i s))
      π d hd0 hdopen hπ.2.1 ε hε
  · intro π' hπ'
    exact huniq π' ⟨hπ'.1, hπ'.2.1, hπ'.2.2.2⟩

/-- Paper-literal packaging of the general Finsler selector.

The potential and the limiting readout derivative are internal to the proof;
the only hypotheses beyond the paper's population and iid sampling data are
the open analytic inputs, bundled existentially:

* `hprob`, `hupper` — original iid lower/upper pressure localization for the
  intrinsic length cost at the paper scale `(n+1)^(2/q)`;
* `hvalue` — the legal-repair/value identification closing the pressure
  bracket;
* `hreadout` — differentiability of the limiting pressure readout at zero.

The conclusion is the paper's whole-optimal-set convergence in probability,
including all fractional optima. -/
theorem exists_general_finsler_selector_of_open_inputs
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
    (hopen : ∃ (φ : M → ℝ),
      (let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 φ) ∧
      ∃ (pressureLower pressureUpper : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
        (radius derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ),
        (∀ f, 0 < radius f) ∧
        (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
          pressureLower f t = pressureUpper f t) ∧
        (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ),
          HasDerivAt (fun t ↦ pressureLower f t) (derivative f) 0) ∧
        (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
          |t| < radius f → 0 < ε →
          Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F
            (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
            (A ∪ B) (hA.union hB).measurableSet
            (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
            (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
              pressureLower f t - ε}) atTop (𝓝 0)) ∧
        (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
          |t| < radius f → 0 < ε →
          ∀ᶠ n in atTop,
            ∫ s, finslerSupportedPressure F
              (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
              (A ∪ B) (hA.union hB).measurableSet
              (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
              (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
              (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤
                pressureUpper f t + ε)) :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃ π : ProbabilityMeasure (M × M),
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
  obtain ⟨φ, hφ, pressureLower, pressureUpper, radius, derivative,
    hradius, hvalue, hreadout, hprob, hupper⟩ := hopen
  obtain ⟨π, hπ, -⟩ := existsUnique_general_finsler_selector_of_open_inputs
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvolume hA hB hAB
    hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ
    pressureLower pressureUpper radius derivative hradius hvalue hreadout hprob hupper
  exact ⟨π, hπ.2.1, hπ.2.2.1, hπ.2.2.2⟩

end OTSelector.Reconstruction
