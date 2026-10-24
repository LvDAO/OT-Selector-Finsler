import OTSelector.Limit.FinslerPressureSqueeze
import OTSelector.Geometry.FinslerSupportedSemidiscretePressure
import OTSelector.Finite.PressureRegularity

/-!
# Concavity in the tilt of the physical Dirichlet semidiscrete mean

The finite-sample supported pressure is a normalized perturbed assignment value,
so it is concave in the tilt: it is the minimum of the affine objectives of the
finitely many assignments.  The physical semidiscrete mean is the expectation of
this pressure over the original iid sample, and the expectation of an almost
everywhere concave family against a probability measure is concave.

This supplies the `hconc` hypothesis of the differentiability squeeze
`hasDerivAt_of_concave_pointwise_tendsto_of_supergradient_sequence`.
-/

open Set MeasureTheory ProbabilityTheory Manifold Filter OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace OTSelector.Probability

/-- **Concavity passes through integration.**  The integral against a probability
measure of an almost everywhere concave family of real functions is concave,
provided every member is integrable. -/
theorem concaveOn_integral_of_ae {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {s : Set ℝ}
    (hs : Convex ℝ s) {f : α → ℝ → ℝ}
    (hf : ∀ᵐ a ∂μ, ConcaveOn ℝ s (f a))
    (hint : ∀ t ∈ s, Integrable (fun a => f a t) μ) :
    ConcaveOn ℝ s (fun t => ∫ a, f a t ∂μ) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hxy : a * x + b * y ∈ s := hs hx hy ha hb hab
  have hpt : ∀ᵐ z ∂μ, a * f z x + b * f z y ≤ f z (a * x + b * y) := by
    filter_upwards [hf] with z hz
    have h := hz.2 hx hy ha hb hab
    simpa only [smul_eq_mul] using h
  calc
    a * (∫ z, f z x ∂μ) + b * (∫ z, f z y ∂μ)
        = ∫ z, (a * f z x + b * f z y) ∂μ := by
          rw [integral_add ((hint x hx).const_mul a) ((hint y hy).const_mul b),
            integral_const_mul, integral_const_mul]
    _ ≤ ∫ z, f z (a * x + b * y) ∂μ :=
          integral_mono_ae (((hint x hx).const_mul a).add ((hint y hy).const_mul b))
            (hint _ hxy) hpt

end OTSelector.Probability

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Ω] {F : ContinuousFinslerNorm E M}

/-- **Concavity of the physical semidiscrete mean in the tilt.** -/
theorem concaveOn_finslerSemidiscreteMean_tilt
    (hF : F.IsSmoothStronglyConvex)
    (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : ProbabilityMeasure M) (hdim : 2 ≤ Module.finrank ℝ E)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = (μ : Measure M))
    (hYlaw : ∀ i, P.map (Y i) = (ν : Measure M))
    (hXY : IndepFun (fun sample i ↦ X i sample) (fun sample i ↦ Y i sample) P)
    (φ : M → ℝ) (hφL : let _instConcaveMeanMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) :
    let _instConcaveMeanMetric : MetricSpace M := F.metricSpace
    ConcaveOn ℝ Set.univ
      (fun t => finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace _instProper
  let kval : ℝ := ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))
  have hkval : 0 < kval := Real.rpow_pos_of_pos (by positivity) _
  let g : M → M → ℝ := fun x y =>
    f (supportProjection μ K hK.measurableSet hμ x,
      supportProjection ν K hK.measurableSet hν y)
  let V : ℝ → Ω → ℝ := fun t s => Pressure.supportedDistancePressure μ ν K hK.measurableSet
    hμ hν (fun i => X i s) (fun j => Y j s) φ kval f t
  have hVconc : ∀ s, ConcaveOn ℝ Set.univ (fun t => V t s) := by
    intro s
    have h := concaveOn_perturbedAssignmentValue_div
      (n := n + 1)
      (cost := fun i j => kval * distanceSlackEdgeCost (fun i => X i s) (fun j => Y j s) φ i j)
      (probe := fun i j => g (X i s) (Y j s))
    simpa only [V, Pressure.supportedDistancePressure, g] using h
  have hXK : ∀ᵐ s ∂P, ∀ i, X i s ∈ K := by
    apply ae_all_iff.mpr
    intro i
    exact ae_of_ae_map (hX i).aemeasurable (by rw [hXlaw i]; exact hμ)
  have hYK : ∀ᵐ s ∂P, ∀ j, Y j s ∈ K := by
    apply ae_all_iff.mpr
    intro j
    exact ae_of_ae_map (hY j).aemeasurable (by rw [hYlaw j]; exact hν)
  have hVint : ∀ t : ℝ, Integrable (fun s => V t s) P := by
    intro t
    have hφc : Continuous φ := hφL.continuous
    have h := Pressure.integrable_supportedDistancePressure P μ ν K hK.measurableSet hμ hν
      X Y hX hY φ hφL hφc kval f t (Nat.succ_pos n) hkval.le hK hXK hYK
    simpa only [V] using h
  have hconcInt : ConcaveOn ℝ Set.univ (fun t => ∫ s, V t s ∂P) :=
    OTSelector.Probability.concaveOn_integral_of_ae P convex_univ
      (Filter.Eventually.of_forall hVconc) (fun t _ => hVint t)
  have hfun : (fun t => ∫ s, V t s ∂P) =
      (fun t => finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) := by
    funext t
    have hφc : Continuous φ := hφL.continuous
    have h := (hF.integral_supportedDistancePressure_eq_fullSemidiscreteValue m μ ν hdim
      hμchart hνchart hcomplete K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφc
      hkval f t).2
    simpa only [V, finslerSemidiscreteMean, kval] using h
  rw [hfun] at hconcInt
  exact hconcInt

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
