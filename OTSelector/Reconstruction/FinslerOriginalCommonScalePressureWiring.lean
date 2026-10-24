import OTSelector.Reconstruction.FinslerOriginalCommonScaleFinalUnconditional
import OTSelector.Reconstruction.FinslerOriginalTileConcentration
import OTSelector.Reconstruction.FinslerOriginalIIDPressureLowerLocalization

/-!
# Wiring the unconditional whole-path bound into the tile/pressure lane

The atomic facts consumed by the tile/pressure chain are, for one scene law:

* the whole-path second-moment bound (MemLp) of the exact traffic off the
  common-scale phase-bad event, together with its explicit integral bound;
* the exponential bounded-path probability of that bad event.

We bundle exactly these three facts as CommonScaleWholePathPressureData, prove
that they are supplied by
ae_original_minimizer_commonScale_finalUnconditional, and derive the two
consumable consequences used by the pressure lane:

* the Markov/Chebyshev tail bound for the whole-path empirical mean, i.e. the
  bounded-path probability obtained from the second-moment bound;
* integrability of any statistic dominated by the traffic, so that the
  integrability hypothesis of the iid pressure localization is discharged by the
  common-scale whole-path bound.

The final theorem is the exact hprob clause of the iid lower pressure
localization, with its frozen-core integrability hypothesis replaced by the
domination plus the common-scale whole-path data.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- **The common-scale hypothesis consumed by the tile/pressure lane.**

For one scene law muOmega, the whole-path traffic of the actual minimizer is in
L2 off the common-scale phase-bad event and its squared integral is bounded by
2 * CB + 2 * CL; the phase-bad event itself has probability at most
probabilityBound. -/
structure CommonScaleWholePathPressureData {Ω : Type*} [MeasurableSpace Ω]
    (μΩ : Measure Ω) (traffic : Ω → ℝ) (phaseBad : Set Ω)
    (CB CL probabilityBound : ℝ) : Prop where
  /-- The whole-path traffic off the bad event is square integrable. -/
  wholePathL2 : MemLp (phaseBadᶜ.indicator traffic) 2 μΩ
  /-- Explicit squared-integral bound for the whole-path traffic. -/
  wholePathSqIntegral :
    (∫ x, (phaseBadᶜ.indicator traffic x) ^ 2 ∂μΩ) ≤ 2 * CB + 2 * CL
  /-- The bounded-path probability: the bad event has probability at most
  probabilityBound. -/
  boundedPathProbability : μΩ.real phaseBad ≤ probabilityBound

/-- Packaged output of the unconditional whole-path bound: the three facts of
CommonScaleWholePathPressureData are exactly the three conjuncts of
ae_original_minimizer_commonScale_finalUnconditional. -/
theorem commonScaleWholePathPressureData_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {μΩ : Measure Ω} {traffic : Ω → ℝ} {phaseBad : Set Ω} {CB CL B0 : ℝ}
    (hLp : MemLp (phaseBadᶜ.indicator traffic) 2 μΩ)
    (hInt : (∫ x, (phaseBadᶜ.indicator traffic x) ^ 2 ∂μΩ) ≤ 2 * CB + 2 * CL)
    (hProb : μΩ.real phaseBad ≤ B0) :
    CommonScaleWholePathPressureData μΩ traffic phaseBad CB CL B0 :=
  ⟨hLp, hInt, hProb⟩

/-- **Bounded-path probability from the whole-path second-moment bound.**

Markov/Chebyshev applied to the whole-path traffic off the phase-bad event: for
every level R > 0 the probability that the empirical mean exceeds R is at most
the bad-event probability plus the squared-integral bound divided by R ^ 2. -/
theorem boundedPathProbability_of_wholePathData {Ω : Type*} [MeasurableSpace Ω]
    {μΩ : Measure Ω} [IsProbabilityMeasure μΩ]
    {traffic : Ω → ℝ} {phaseBad : Set Ω} {CB CL B0 : ℝ}
    (hdata : CommonScaleWholePathPressureData μΩ traffic phaseBad CB CL B0)
    (htraf : Measurable traffic) (hbad : MeasurableSet phaseBad)
    {R : ℝ} (hR : 0 < R) :
    μΩ.real {s | R < traffic s} ≤
      B0 + (2 * CB + 2 * CL) / R ^ 2 := by
  let ind : Ω → ℝ := phaseBadᶜ.indicator traffic
  have hsubset : {s | R < traffic s} ⊆ phaseBad ∪ {s | R ≤ |ind s|} := by
    intro s hs
    by_cases hb : s ∈ phaseBad
    · exact Or.inl hb
    · refine Or.inr ?_
      have hmem : s ∈ phaseBadᶜ := by simpa using hb
      have hind : ind s = traffic s := by
        show phaseBadᶜ.indicator traffic s = traffic s
        exact Set.indicator_of_mem hmem traffic
      have habs : |ind s| = traffic s := by
        rw [hind, abs_of_pos (lt_trans hR hs)]
      simp only [Set.mem_ofPred_eq, habs]
      exact le_of_lt hs
  have hmeas : MeasurableSet {s | R < traffic s} :=
    measurableSet_lt measurable_const htraf
  have hmeasR : MeasurableSet {s | R ≤ |ind s|} :=
    measurableSet_le measurable_const (htraf.indicator hbad.compl).abs
  have hUnionFin : μΩ (phaseBad ∪ {s | R ≤ |ind s|}) ≠ (⊤ : ℝ≥0∞) :=
    measure_ne_top μΩ _
  have hmono : μΩ.real {s | R < traffic s} ≤
      μΩ.real (phaseBad ∪ {s | R ≤ |ind s|}) :=
    ENNReal.toReal_mono hUnionFin (measure_mono hsubset)
  have hbadFin : μΩ phaseBad ≠ (⊤ : ℝ≥0∞) := measure_ne_top μΩ _
  have hsetFin : μΩ {s | R ≤ |ind s|} ≠ (⊤ : ℝ≥0∞) := measure_ne_top μΩ _
  have hunion : μΩ.real (phaseBad ∪ {s | R ≤ |ind s|}) ≤
      μΩ.real phaseBad + μΩ.real {s | R ≤ |ind s|} := by
    have h1 : μΩ (phaseBad ∪ {s | R ≤ |ind s|}) ≤
        μΩ phaseBad + μΩ {s | R ≤ |ind s|} := measure_union_le _ _
    calc μΩ.real (phaseBad ∪ {s | R ≤ |ind s|})
        = (μΩ (phaseBad ∪ {s | R ≤ |ind s|})).toReal := rfl
      _ ≤ (μΩ phaseBad + μΩ {s | R ≤ |ind s|}).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hbadFin, hsetFin⟩) h1
      _ = μΩ.real phaseBad + μΩ.real {s | R ≤ |ind s|} :=
          ENNReal.toReal_add hbadFin hsetFin
  have hmarkov : μΩ.real {s | R ≤ |ind s|} ≤ (2 * CB + 2 * CL) / R ^ 2 := by
    have hint : Integrable (fun s => (ind s - 0) ^ 2) μΩ := by
      simpa only [sub_zero] using hdata.wholePathL2.integrable_sq
    have h := PopulationLocalPressureCore.TaylorTiles.tileDeviation_le_secondMoment μΩ ind 0 hR hint
    have hset : {s | R ≤ |ind s - 0|} = {s | R ≤ |ind s|} := by
      ext s
      simp only [Set.mem_ofPred_eq, sub_zero]
    rw [hset] at h
    have hInt : (∫ s, (ind s - 0) ^ 2 ∂μΩ) = ∫ s, (ind s) ^ 2 ∂μΩ := by
      simp only [sub_zero]
    rw [hInt] at h
    exact h.trans (div_le_div_of_nonneg_right hdata.wholePathSqIntegral (sq_nonneg R))
  calc μΩ.real {s | R < traffic s}
      ≤ μΩ.real (phaseBad ∪ {s | R ≤ |ind s|}) := hmono
    _ ≤ μΩ.real phaseBad + μΩ.real {s | R ≤ |ind s|} := hunion
    _ ≤ B0 + (2 * CB + 2 * CL) / R ^ 2 :=
        add_le_add hdata.boundedPathProbability hmarkov

/-- **Integrability from the common-scale whole-path data.**

Any measurable statistic dominated by A + C * traffic is integrable, because the
whole-path traffic is L2 off the bad event and integrable on it. This is the form
in which the frozen-core integrability hypothesis of the iid pressure
localization is discharged. -/
theorem integrable_of_dominated_by_wholePath {Ω : Type*} [MeasurableSpace Ω]
    {μΩ : Measure Ω} [IsFiniteMeasure μΩ]
    {traffic : Ω → ℝ} {phaseBad : Set Ω} {CB CL B0 : ℝ}
    (hdata : CommonScaleWholePathPressureData μΩ traffic phaseBad CB CL B0)
    (htraf : Measurable traffic) (hbad : MeasurableSet phaseBad)
    (hbadint : Integrable (phaseBad.indicator traffic) μΩ)
    {T : Ω → ℝ} (hT : Measurable T) {A C : ℝ} (_hC : 0 ≤ C)
    (hdom : ∀ s, |T s| ≤ A + C * traffic s) :
    Integrable T μΩ := by
  let ind : Ω → ℝ := phaseBadᶜ.indicator traffic
  let indBad : Ω → ℝ := phaseBad.indicator traffic
  have hsplit : traffic = ind + indBad := by
    funext s
    simp only [ind, indBad, Pi.add_apply]
    by_cases hs : s ∈ phaseBad
    · have hnot : s ∉ phaseBadᶜ := by simpa using hs
      simp only [ind, indBad, Pi.add_apply, Set.indicator_of_notMem hnot,
        Set.indicator_of_mem hs, zero_add]
    · have hmem : s ∈ phaseBadᶜ := by simpa using hs
      simp only [ind, indBad, Pi.add_apply, Set.indicator_of_mem hmem,
        Set.indicator_of_notMem hs, add_zero]
  have hindInt : Integrable ind μΩ := by
    have hsq : Integrable (fun s => ind s ^ 2) μΩ := hdata.wholePathL2.integrable_sq
    have hone : Integrable (fun _ : Ω => (1 : ℝ)) μΩ := integrable_const _
    have hmaj : Integrable (fun s => 1 + ind s ^ 2) μΩ := hone.add hsq
    have hbound : ∀ s, ‖ind s‖ ≤ ‖1 + ind s ^ 2‖ := by
      intro s
      rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ind s ^ 2)]
      have h1 : ‖ind s‖ ≤ 1 + ‖ind s‖ ^ 2 := by
        nlinarith [norm_nonneg (ind s), sq_nonneg (‖ind s‖ - 1)]
      simpa only [Real.norm_eq_abs, sq_abs] using h1
    exact hmaj.mono ((htraf.indicator hbad.compl).aestronglyMeasurable)
      (Eventually.of_forall hbound)
  have hindBadInt : Integrable indBad μΩ := by
    change Integrable (phaseBad.indicator traffic) μΩ
    exact hbadint
  have htrafficInt : Integrable traffic μΩ := by
    rw [hsplit]
    exact hindInt.add hindBadInt
  have hmajor : Integrable (fun s => A + C * traffic s) μΩ :=
    (integrable_const A).add (htrafficInt.const_mul C)
  refine hmajor.mono hT.aestronglyMeasurable ?_
  filter_upwards with s
  have hnonneg : (0 : ℝ) ≤ A + C * traffic s :=
    le_trans (abs_nonneg (T s)) (hdom s)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hnonneg]
  exact hdom s

end OTSelector.Reconstruction

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

open ProbabilityTheory
open scoped BoundedContinuousFunction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}



/-- **hprob from the common-scale whole-path data.**

This is the exact lower hprob clause of the iid pressure localization, with its
frozen-core integrability hypothesis discharged by the common-scale whole-path
bound: for every sample size the empirical scene carries the bounded-path
probability and the L2 bound on the whole-path empirical mean, and the frozen
core cost is dominated by that traffic plus a constant.  The remaining inputs are
exactly the localization inputs hfrozen_dom and hfrozen_mean, i.e. the geometric
identification of the frozen core with the pressure readout and its Campbell
mean lower bound. -/
theorem hprob_clause_of_commonScale_wholePath
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
    (hCamp0 : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), 0 ≤ Camp f t)
    {CBs CLs B0s : ℕ → ℝ}
    (hdata : ∀ n, OTSelector.Reconstruction.CommonScaleWholePathPressureData (P n) (traffic n)
      (phaseBadSet n) (CBs n) (CLs n) (B0s n))
    (hbadint : ∀ n, Integrable ((phaseBadSet n).indicator (traffic n)) (P n))
    (hfrozen_meas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Measurable (frozenCost f t n))
    (hfrozen_bound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n),
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
    exact OTSelector.Reconstruction.integrable_of_dominated_by_wholePath (hdata n) (htraf n) (hbadset n)
      (hbadint n) (hfrozen_meas f t n) (hCamp0 f t) (hfrozen_bound f t n)
  exact finslerSupportedPressure_probability_lower_of_frozen_mean_lower
    hcomplete hdim μ ν K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ
    pressureLower frozenCost hfrozen_int hfrozen_dom hfrozen_mean

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
