import OTSelector.Reconstruction.FinslerGeneralSelectorAssemblyInputs
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Potential invariance of the limiting plan

This module addresses discrepancy (ii) of the paper-fidelity audit.  The paper theorem
(`main.tex`, `thm:general-finsler-selector`) states that the physical limit depends only on
`(F, mu, nu)`, independently of optimal potentials.  The paper proves the underlying
structural statement `thm:intrinsic-active-invariance` (main.tex:958) through the intrinsic
active-block decomposition and its ray quotient (`prop:general-optimal-face`, main.tex:422;
`prop:ray-forward-criterion`, main.tex:524): across two calibrated optimal potentials the
active blocks agree up to a Borel block bijection and the quotient laws agree.

For the *limiting plan* itself the invariance has a shorter formal proof that does not need
the active-block identification: the empirical optimal face
`Pressure.empiricalOptimalFace X Y` is defined from the samples and the intrinsic length cost
alone --- no optimal potential, readout derivative, coordinate choice, label or tie-breaking
rule occurs in its definition.  Hence its outer-probability limit is unique, and every
instantiation of the four-input assembly (with whatever calibrated potential and readout data
it uses) produces exactly that same limit plan.  This is the statement needed at the level of
the paper's conclusion; the finer structural invariance remains recorded by the paper and is
not required here.

Main results:

* `eq_of_tendsto_empiricalOptimalFace` --- any two plans that are outer-probability limits, in
  every weak neighborhood, of the whole empirical optimal face are equal;
* `finsler_assembly_limit_independent_of_potential` --- for the paper data and the four open
  analytic inputs, the assembly's plan is the unique such limit; in particular it does not
  depend on the calibrated potential or the readout derivative used to derive it.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- **Uniqueness of the outer-probability limit of the empirical optimal face.**

If the whole empirical optimal set converges, in outer probability and in every
weak neighborhood, to two probability plans, then the two plans coincide.  The
face depends only on the samples and the intrinsic length cost, not on any
optimal potential or readout data. -/
theorem eq_of_tendsto_empiricalOptimalFace
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ProperSpace M]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    {π₁ π₂ : ProbabilityMeasure (M × M)}
    (h₁ : ∀ U ∈ 𝓝 π₁, Tendsto (fun n ↦ (P n).real
      {s | ∃ γ ∈ Pressure.empiricalOptimalFace (fun i ↦ X n i s) (fun i ↦ Y n i s),
        γ ∉ U}) atTop (𝓝 0))
    (h₂ : ∀ U ∈ 𝓝 π₂, Tendsto (fun n ↦ (P n).real
      {s | ∃ γ ∈ Pressure.empiricalOptimalFace (fun i ↦ X n i s) (fun i ↦ Y n i s),
        γ ∉ U}) atTop (𝓝 0)) :
    π₁ = π₂ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hcont : Continuous (fun γ : ProbabilityMeasure (M × M) ↦
      ∫ z, f z ∂(γ : Measure (M × M))) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  have key : ∀ k : ℕ,
      |(∫ z, f z ∂(π₁ : Measure (M × M))) - (∫ z, f z ∂(π₂ : Measure (M × M)))| ≤
        2 / ((k : ℝ) + 1) := by
    intro k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    let U₁ : Set (ProbabilityMeasure (M × M)) :=
      {γ | |(∫ z, f z ∂(γ : Measure (M × M))) -
        (∫ z, f z ∂(π₁ : Measure (M × M)))| < 1 / ((k : ℝ) + 1)}
    let U₂ : Set (ProbabilityMeasure (M × M)) :=
      {γ | |(∫ z, f z ∂(γ : Measure (M × M))) -
        (∫ z, f z ∂(π₂ : Measure (M × M)))| < 1 / ((k : ℝ) + 1)}
    have hU₁ : U₁ ∈ 𝓝 π₁ := by
      have hbase : Continuous (fun γ : ProbabilityMeasure (M × M) ↦
          |(∫ z, f z ∂(γ : Measure (M × M))) -
            (∫ z, f z ∂(π₁ : Measure (M × M)))|) :=
        (hcont.sub continuous_const).abs
      have hzero : (fun γ : ProbabilityMeasure (M × M) ↦
          |(∫ z, f z ∂(γ : Measure (M × M))) -
            (∫ z, f z ∂(π₁ : Measure (M × M)))|) π₁ = 0 := by simp
      have ht : Tendsto (fun γ : ProbabilityMeasure (M × M) ↦
          |(∫ z, f z ∂(γ : Measure (M × M))) -
            (∫ z, f z ∂(π₁ : Measure (M × M)))|) (𝓝 π₁) (𝓝 0) := by
        simpa only [hzero] using hbase.tendsto π₁
      exact ht.eventually (Iio_mem_nhds hε)
    have hU₂ : U₂ ∈ 𝓝 π₂ := by
      have hbase : Continuous (fun γ : ProbabilityMeasure (M × M) ↦
          |(∫ z, f z ∂(γ : Measure (M × M))) -
            (∫ z, f z ∂(π₂ : Measure (M × M)))|) :=
        (hcont.sub continuous_const).abs
      have hzero : (fun γ : ProbabilityMeasure (M × M) ↦
          |(∫ z, f z ∂(γ : Measure (M × M))) -
            (∫ z, f z ∂(π₂ : Measure (M × M)))|) π₂ = 0 := by simp
      have ht : Tendsto (fun γ : ProbabilityMeasure (M × M) ↦
          |(∫ z, f z ∂(γ : Measure (M × M))) -
            (∫ z, f z ∂(π₂ : Measure (M × M)))|) (𝓝 π₂) (𝓝 0) := by
        simpa only [hzero] using hbase.tendsto π₂
      exact ht.eventually (Iio_mem_nhds hε)
    have hsum : Tendsto (fun n ↦
        (P n).real {s | ∃ γ ∈ Pressure.empiricalOptimalFace
          (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₁} +
        (P n).real {s | ∃ γ ∈ Pressure.empiricalOptimalFace
          (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₂})
        atTop (𝓝 (0 + 0 : ℝ)) := Filter.Tendsto.add (h₁ U₁ hU₁) (h₂ U₂ hU₂)
    have hbound : ∀ᶠ n : ℕ in atTop,
        |(∫ z, f z ∂(π₁ : Measure (M × M))) - (∫ z, f z ∂(π₂ : Measure (M × M)))| <
          2 / ((k : ℝ) + 1) := by
      filter_upwards [hsum.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) + 0 < 1))] with n hn
      have hne : {s | ∃ γ ∈ Pressure.empiricalOptimalFace
            (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₁} ∪
          {s | ∃ γ ∈ Pressure.empiricalOptimalFace
            (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₂} ≠ Set.univ := by
        intro huniv
        have hreal : (P n).real (Set.univ : Set (Ω n)) = 1 := by
          rw [Measure.real_def, measure_univ]
          simp
        have hone : (P n).real ({s | ∃ γ ∈ Pressure.empiricalOptimalFace
              (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₁} ∪
            {s | ∃ γ ∈ Pressure.empiricalOptimalFace
              (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₂}) = 1 := by
          rw [huniv, hreal]
        have hle := measureReal_union_le (μ := P n)
          {s | ∃ γ ∈ Pressure.empiricalOptimalFace
            (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₁}
          {s | ∃ γ ∈ Pressure.empiricalOptimalFace
            (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₂}
        linarith
      obtain ⟨s, hs⟩ := Set.nonempty_compl.mpr hne
      have hs₁ : s ∉ {s | ∃ γ ∈ Pressure.empiricalOptimalFace
          (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₁} :=
        fun hmem ↦ hs (Or.inl hmem)
      have hs₂ : s ∉ {s | ∃ γ ∈ Pressure.empiricalOptimalFace
          (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U₂} :=
        fun hmem ↦ hs (Or.inr hmem)
      haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      obtain ⟨γ, hγ⟩ := Pressure.empiricalOptimalFace_nonempty
        (fun i ↦ X n i s) (fun i ↦ Y n i s)
      have hclose₁ : |(∫ z, f z ∂(γ : Measure (M × M))) -
          (∫ z, f z ∂(π₁ : Measure (M × M)))| < 1 / ((k : ℝ) + 1) := by
        by_contra hcon
        exact hs₁ ⟨γ, hγ, hcon⟩
      have hclose₂ : |(∫ z, f z ∂(γ : Measure (M × M))) -
          (∫ z, f z ∂(π₂ : Measure (M × M)))| < 1 / ((k : ℝ) + 1) := by
        by_contra hcon
        exact hs₂ ⟨γ, hγ, hcon⟩
      have hA : |(∫ z, f z ∂(π₁ : Measure (M × M))) -
          (∫ z, f z ∂(γ : Measure (M × M)))| < 1 / ((k : ℝ) + 1) := by
        rw [abs_sub_comm]
        exact hclose₁
      calc |(∫ z, f z ∂(π₁ : Measure (M × M))) - (∫ z, f z ∂(π₂ : Measure (M × M)))|
          = |((∫ z, f z ∂(π₁ : Measure (M × M))) - (∫ z, f z ∂(γ : Measure (M × M)))) +
              ((∫ z, f z ∂(γ : Measure (M × M))) - (∫ z, f z ∂(π₂ : Measure (M × M))))| :=
            by ring_nf
        _ ≤ |(∫ z, f z ∂(π₁ : Measure (M × M))) - (∫ z, f z ∂(γ : Measure (M × M)))| +
              |(∫ z, f z ∂(γ : Measure (M × M))) - (∫ z, f z ∂(π₂ : Measure (M × M)))| :=
            abs_add_le _ _
        _ < 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by linarith
        _ = 2 / ((k : ℝ) + 1) := by ring
    exact le_of_lt hbound.exists.choose_spec
  have hlim : Tendsto (fun k : ℕ ↦ 2 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [div_eq_mul_inv, mul_comm] using h.const_mul (2 : ℝ)
  have hzero : |(∫ z, f z ∂(π₁ : Measure (M × M))) -
      (∫ z, f z ∂(π₂ : Measure (M × M)))| = 0 := by
    refine le_antisymm ?_ (abs_nonneg _)
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim key
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

theorem finsler_assembly_limit_independent_of_potential
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
          ∀ π' : ProbabilityMeasure (M × M),
            (∀ U ∈ 𝓝 π', Tendsto (fun n ↦ (P n).real
              {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U}) atTop (𝓝 0)) → π' = π := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  obtain ⟨u, hu, hmain⟩ := existsUnique_general_finsler_selector_of_four_inputs
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
    hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY
  refine ⟨u, hu, ?_⟩
  intro pressureLower pressureUpper radius hradius hvalue hprob hupper
  obtain ⟨derivative, _hderiv, huniq⟩ := hmain
    pressureLower pressureUpper radius hradius hvalue hprob hupper
  obtain ⟨π, hπ, _huniqπ⟩ := huniq
  exact ⟨π, hπ.2.2.2, hπ.2.1, fun π' hπ' ↦
    eq_of_tendsto_empiricalOptimalFace (π₁ := π') (π₂ := π) P X Y hπ' hπ.2.1⟩

end OTSelector.Reconstruction
