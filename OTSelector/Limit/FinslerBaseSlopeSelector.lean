import OTSelector.Limit.FinslerMeanSlopeSelector
import OTSelector.Analysis.Calculus.LimitFromSecantSlopes

/-!
# Selector endpoint from central convergence and finite-level tilt slopes

The only analytic inputs of the general Finsler selector that remain after this
module are:

* convergence of the physical semidiscrete means at the central tilt `0`;
* convergence of the right and left secant slopes at every fixed small tilt;
* convergence of the two limiting slope functions to one common derivative.

No pointwise convergence at nonzero tilts and no differentiability of a separately
supplied pressure are assumed.  The pressure is reconstructed from the central
limit and the slope functions: for positive tilts it is the right-slope affine
branch, and for negative tilts the left-slope branch.  Convergence at every fixed
tilt then follows from the convergence of the central values and of the slopes,
and differentiability at zero is `hasDerivAt_of_tendsto_mean_slope`.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- Central convergence plus finite-level one-sided slope convergence and their
common zero-step limit discharge all four pressure premises of the general
Finsler selector endpoint. -/
theorem existsUnique_selector_of_finsler_base_and_slope_convergence
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
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
    (hφ : let _instBaseSlopePotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (p0 : ((K × K) →ᵇ ℝ) → ℝ)
    (radius : ((K × K) →ᵇ ℝ) → ℝ) (hradius : ∀ f, 0 < radius f)
    (positiveSlope negativeSlope : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (derivative : ((K × K) →ᵇ ℝ) → ℝ)
    (hzero : ∀ f, Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n)
      atTop (𝓝 (p0 f)))
    (hpositive : ∀ (f : (K × K) →ᵇ ℝ) (h : ℝ), 0 < h → h < radius f →
      Tendsto (fun n ↦
        (finslerSemidiscreteMean F μ ν K hK hμ hν φ f h n -
          finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n) / h)
        atTop (𝓝 (positiveSlope f h)))
    (hnegative : ∀ (f : (K × K) →ᵇ ℝ) (h : ℝ), 0 < h → h < radius f →
      Tendsto (fun n ↦
        (finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n -
          finslerSemidiscreteMean F μ ν K hK hμ hν φ f (-h) n) / h)
        atTop (𝓝 (negativeSlope f h)))
    (hpositiveSlope : ∀ f : (K × K) →ᵇ ℝ,
      Tendsto (positiveSlope f) (𝓝[>] (0 : ℝ)) (𝓝 (derivative f)))
    (hnegativeSlope : ∀ f : (K × K) →ᵇ ℝ,
      Tendsto (negativeSlope f) (𝓝[>] (0 : ℝ)) (𝓝 (derivative f))) :
    let _instBaseSlopeSelectorMetric : MetricSpace M := F.metricSpace
    let _instBaseSlopeSelectorProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
        (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
      (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
        {sample | ∃ γ ∈ Pressure.empiricalOptimalFace
          (fun i ↦ X n i sample) (fun i ↦ Y n i sample), γ ∉ U}) atTop (𝓝 0)) ∧
      IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  let pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ := fun f t ↦
    if 0 ≤ t then p0 f + t * positiveSlope f t else p0 f + t * negativeSlope f (-t)
  have hpressure_zero (f : (K × K) →ᵇ ℝ) : pressure f 0 = p0 f := by
    simp only [pressure, le_refl, if_true]
    ring
  have hconv : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
      Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
        atTop (𝓝 (pressure f t)) := by
    intro f t ht
    rcases lt_trichotomy t 0 with htneg | htzero | htpos
    · have hh : 0 < -t := by linarith
      have hlt : -t < radius f := by rwa [abs_of_neg htneg] at ht
      have hlim := hnegative f (-t) hh hlt
      have hlim' : Tendsto (fun n ↦
          (finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n -
            finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) / (-t))
          atTop (𝓝 (negativeSlope f (-t))) := by
        simpa only [neg_neg] using hlim
      have hfun : (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) =
          fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n +
            t * ((finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n -
              finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) / (-t)) := by
        funext n
        have htne : t ≠ 0 := by linarith
        field_simp [htne]
        ring
      rw [hfun]
      have htarget : p0 f + t * negativeSlope f (-t) = pressure f t := by
        simp only [pressure, if_neg (not_le.mpr htneg)]
      rw [← htarget]
      exact (hzero f).add (hlim'.const_mul t)
    · subst t
      rw [hpressure_zero]
      exact hzero f
    · have hlt : t < radius f := by rwa [abs_of_pos htpos] at ht
      have hlim := hpositive f t htpos hlt
      have hfun : (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) =
          fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n +
            t * ((finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n -
              finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n) / t) := by
        funext n
        field_simp [htpos.ne']
        ring
      rw [hfun]
      have htarget : p0 f + t * positiveSlope f t = pressure f t := by
        simp only [pressure, if_pos htpos.le]
      rw [← htarget]
      exact (hzero f).add (hlim.const_mul t)
  have hderiv : ∀ f : (K × K) →ᵇ ℝ, HasDerivAt (pressure f) (derivative f) 0 := by
    intro f
    exact hasDerivAt_of_tendsto_mean_slope (hε := hradius f)
      (J := fun n t ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
      (P := pressure f) (Dpos := positiveSlope f) (Dneg := negativeSlope f)
      (d := derivative f) (hconv f) (hpositive f) (hnegative f)
      (hpositiveSlope f) (hnegativeSlope f)
  exact existsUnique_selector_of_finsler_semidiscrete_convergence
    hF hcomplete m hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
    hXlaw hYlaw hXY φ hφ pressure radius derivative hradius hconv hderiv

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
