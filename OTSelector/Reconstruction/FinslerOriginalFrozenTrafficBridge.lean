import OTSelector.Reconstruction.FinslerOriginalCommonScalePressureWiring
import OTSelector.Reconstruction.FinslerOriginalIIDPressureLowerLocalization
import OTSelector.Reconstruction.FiniteDominationCore

/-!
# Frozen-core traffic domination bridges

The pressure-lane wiring theorem
OTSelector.Reconstruction ... hprob_clause_of_commonScale_wholePath consumes two
bridge hypotheses:

* (i) the frozen-core cost is pointwise dominated by the empirical whole-path
  traffic plus a constant, on the whole space;
* (ii) the traffic is integrable on the phase-bad event.

This file closes (ii) and weakens (i).  The key observation is that the only use
of the bad-event traffic integrability in the wiring proof is to integrate the
frozen cost on the bad event.  That integration does not need the traffic: it
only needs the frozen cost to be bounded on the bad event, which is the crude
bound of the finite-domination argument.

Contents:

1. integrable_of_memLp_two: an L2 function is integrable on a finite measure.
2. integrable_of_dominated_on_compl_and_bounded_on: if a statistic is dominated
   by A + C * traffic off the bad event and bounded by a constant on it, then it
   is integrable, using only the L2 bound on the traffic off the bad event.  No
   integrability of the traffic on the bad event is required.
3. empiricalFrozenCore_abs_le_of_pressure_bound: for the finite-domination
   frozen core cost, the crude on-bad boundedness follows from the deterministic
   finite-domination core and boundedness of the normalized empirical pressure.
4. hprob_clause_of_commonScale_wholePath_boundedBad: the hprob localization
   clause of the pressure lane, with the bad-event traffic integrability replaced
   by the crude boundedness of the frozen core cost on the bad event.

The remaining content of the domination bridge is exactly (i) off the bad event:
the frozen core cost is bounded by the traffic plus a constant there.  This is
the path-count / frozen-core identification; it is not derivable from the
integrability or probability data alone.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal Matrix.Norms.Operator Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- An L2 function is integrable on a finite measure. -/
theorem integrable_of_memLp_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) : Integrable f μ := by
  have hsq : Integrable (fun s => f s ^ 2) μ := hf.integrable_sq
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
  have hmaj : Integrable (fun s => 1 + f s ^ 2) μ := hone.add hsq
  have hbound : ∀ s, ‖f s‖ ≤ ‖1 + f s ^ 2‖ := by
    intro s
    rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + f s ^ 2)]
    have h1 : ‖f s‖ ≤ 1 + ‖f s‖ ^ 2 := by
      nlinarith [norm_nonneg (f s), sq_nonneg (‖f s‖ - 1)]
    simpa only [Real.norm_eq_abs, sq_abs] using h1
  exact hmaj.mono hf.aestronglyMeasurable (Eventually.of_forall hbound)

/-- **Bridge (ii), closed.  Integrability from off-bad domination and on-bad
boundedness.**

No integrability of the traffic on the bad event is needed: on the bad event the
statistic is bounded by a constant and the measure is finite, while off the bad
event the L2 bound on the traffic gives integrability of the majorant. -/
theorem integrable_of_dominated_on_compl_and_bounded_on {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {traffic : Ω → ℝ} {Bad : Set Ω} {CB CL B0 : ℝ}
    (hdata : CommonScaleWholePathPressureData μ traffic Bad CB CL B0)
    (hBad : MeasurableSet Bad) (_htraf : Measurable traffic)
    {T : Ω → ℝ} (hT : Measurable T) {A C Ab : ℝ}
    (hgood : ∀ᵐ s ∂μ, s ∉ Bad → |T s| ≤ A + C * traffic s)
    (hbad : ∀ᵐ s ∂μ, s ∈ Bad → |T s| ≤ Ab) :
    Integrable T μ := by
  have hcomplInt : Integrable (Badᶜ.indicator T) μ := by
    have hgoodTraffic : Integrable (Badᶜ.indicator traffic) μ :=
      integrable_of_memLp_two hdata.wholePathL2
    have hmaj : Integrable
        (fun s => Badᶜ.indicator (fun s => A + C * traffic s) s) μ := by
      have h1 : Integrable (Badᶜ.indicator (fun _ : Ω => A)) μ :=
        (integrable_const A).indicator hBad.compl
      have h2 : Integrable (Badᶜ.indicator (fun s => C * traffic s)) μ := by
        have hcm := hgoodTraffic.const_mul C
        refine hcm.congr ?_
        filter_upwards with s
        by_cases hs : s ∈ Bad
        · have hnot : s ∉ Badᶜ := by simpa using hs
          simp [Set.indicator_of_notMem hnot]
        · have hmem : s ∈ Badᶜ := by simpa using hs
          simp [Set.indicator_of_mem hmem]
      have hsum := h1.add h2
      refine hsum.congr ?_
      filter_upwards with s
      by_cases hs : s ∈ Bad
      · have hnot : s ∉ Badᶜ := by simpa using hs
        simp [Set.indicator_of_notMem hnot]
      · have hmem : s ∈ Badᶜ := by simpa using hs
        simp [Set.indicator_of_mem hmem]
    refine hmaj.mono ((hT.indicator hBad.compl).aestronglyMeasurable) ?_
    filter_upwards [hgood] with s hs
    by_cases hsb : s ∈ Bad
    · have hnot : s ∉ Badᶜ := by simpa using hsb
      simp only [Set.indicator_of_notMem hnot, norm_zero]
      exact le_refl 0
    · have hmem : s ∈ Badᶜ := by simpa using hsb
      simp only [Set.indicator_of_mem hmem]
      have hnn : 0 ≤ A + C * traffic s := le_trans (abs_nonneg (T s)) (hs hsb)
      rw [Real.norm_eq_abs, Real.norm_of_nonneg hnn]
      exact hs hsb
  have hbadInt : Integrable (Bad.indicator T) μ := by
    have hconst : Integrable (fun _ : Ω => max Ab 0) μ := integrable_const _
    refine hconst.mono ((hT.indicator hBad).aestronglyMeasurable) ?_
    filter_upwards [hbad] with s hs
    have hnn : 0 ≤ max Ab 0 := le_max_right _ _
    rw [Real.norm_of_nonneg hnn]
    by_cases hsb : s ∈ Bad
    · rw [Set.indicator_of_mem hsb, Real.norm_eq_abs]
      exact (hs hsb).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hsb, norm_zero]
      exact hnn
  have hsplit : T = Badᶜ.indicator T + Bad.indicator T := by
    funext s
    by_cases hs : s ∈ Bad
    · have hnot : s ∉ Badᶜ := by simpa using hs
      simp only [Set.indicator_of_notMem hnot, Set.indicator_of_mem hs, Pi.add_apply,
        zero_add]
    · have hmem : s ∈ Badᶜ := by simpa using hs
      simp only [Set.indicator_of_mem hmem, Set.indicator_of_notMem hs, Pi.add_apply,
        add_zero]
  rw [hsplit]
  exact hcomplInt.add hbadInt

/-- **The on-bad boundedness of the frozen core cost, from finite domination.**

For the finite-domination frozen core cost the crude bound used on the phase-bad
event is automatic: the deterministic finite-domination core bounds the
normalized frozen core cost by the normalized perturbed assignment value (the
empirical pressure) plus the probe overhead, so boundedness of the pressure on
the bad event bounds the frozen core cost there.  This discharges the
on-bad-boundedness hypothesis of
integrable_of_dominated_on_compl_and_bounded_on for the finite-domination frozen
core, leaving only the off-bad traffic domination as the remaining bridge. -/
theorem empiricalFrozenCore_abs_le_of_pressure_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {N : ℕ → ℕ} (hN : ∀ n, 0 < N n)
    {c g E P : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ} {t B : ℝ}
    (hP : ∀ n, ∀ᵐ ω ∂μ, OTSelector.OptimalFractionalAssignment
      (OTSelector.perturbedEdgeCost (c n ω) (g n ω) t) (P n ω))
    (hE : ∀ n, ∀ᵐ ω ∂μ, ∀ i j,
      E n ω i j ≤ OTSelector.perturbedEdgeCost (c n ω) (g n ω) t i j + B)
    (hE_nonneg : ∀ n, ∀ᵐ ω ∂μ,
      0 ≤ OTSelector.fractionalAssignmentCost (E n ω) (P n ω) / (N n : ℝ))
    {Ab : ℕ → ℝ}
    (hV : ∀ n, ∀ᵐ ω ∂μ,
      OTSelector.perturbedAssignmentValue (c n ω) (g n ω) t / (N n : ℝ) + B ≤ Ab n) :
    ∀ n, ∀ᵐ ω ∂μ,
      |OTSelector.fractionalAssignmentCost (E n ω) (P n ω) / (N n : ℝ)| ≤
        max (Ab n) 0 := by
  intro n
  filter_upwards [hP n, hE n, hE_nonneg n, hV n] with ω hPω hEω hnn hVω
  have hcost := OTSelector.fractionalAssignmentCost_div_le_perturbedAssignmentValue_div_add
    (hN n) hPω hEω
  calc |OTSelector.fractionalAssignmentCost (E n ω) (P n ω) / (N n : ℝ)|
      = OTSelector.fractionalAssignmentCost (E n ω) (P n ω) / (N n : ℝ) :=
        abs_of_nonneg hnn
    _ ≤ OTSelector.perturbedAssignmentValue (c n ω) (g n ω) t / (N n : ℝ) + B := hcost
    _ ≤ Ab n := hVω
    _ ≤ max (Ab n) 0 := le_max_left _ _

end OTSelector.Reconstruction

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

open ProbabilityTheory
open scoped BoundedContinuousFunction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) (⊤ : WithTop ℕ∞) M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- **hprob from the common-scale whole-path data, with the bad-event traffic
integrability replaced by the crude frozen-core bound.**

Compared with hprob_clause_of_commonScale_wholePath, the hypothesis hbadint
(integrability of the traffic on the phase-bad event, i.e. bridge (ii)) is
replaced by the crude boundedness of the frozen core cost on the phase-bad
event.  The frozen-core integrability is then derived from
integrable_of_dominated_on_compl_and_bounded_on.  The remaining bridge is (i)
off the bad event: the frozen core cost dominated by the traffic plus a
constant; the localization inputs hfrozen_dom and hfrozen_mean stay explicit. -/
theorem hprob_clause_of_commonScale_wholePath_boundedBad
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instFinslerLowerPressureMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {traffic : ∀ n, Ω n → ℝ} (htraf : ∀ n, Measurable (traffic n))
    {phaseBadSet : ∀ n, Set (Ω n)} (hbadset : ∀ n, MeasurableSet (phaseBadSet n))
    {Aamp Camp : ((K × K) →ᵇ ℝ) → ℝ → ℝ}
    (_hCamp0 : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), 0 ≤ Camp f t)
    {CBs CLs B0s : ℕ → ℝ}
    (hdata : ∀ n, OTSelector.Reconstruction.CommonScaleWholePathPressureData (P n) (traffic n)
      (phaseBadSet n) (CBs n) (CLs n) (B0s n))
    {Ab : ((K × K) →ᵇ ℝ) → ℝ → ℝ}
    (hfrozen_bad_bound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n),
      s ∈ phaseBadSet n → |frozenCost f t n s| ≤ Ab f t)
    (hfrozen_meas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Measurable (frozenCost f t n))
    (hfrozen_bound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n),
      s ∉ phaseBadSet n →
        |frozenCost f t n s| ≤ Aamp f t + Camp f t * traffic n s)
    (hfrozen_dom : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_mean : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      pressureLower f t + |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressureLower f t - ε}) atTop (𝓝 0) := by
  have hfrozen_int : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n) := by
    intro f t n
    exact OTSelector.Reconstruction.integrable_of_dominated_on_compl_and_bounded_on
      (hdata n) (hbadset n) (htraf n) (hfrozen_meas f t n)
      (Eventually.of_forall (hfrozen_bound f t n))
      (Eventually.of_forall (hfrozen_bad_bound f t n))
  exact finslerSupportedPressure_probability_lower_of_frozen_mean_lower
    hcomplete hdim μ ν K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ
    pressureLower frozenCost hfrozen_int hfrozen_dom hfrozen_mean

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
