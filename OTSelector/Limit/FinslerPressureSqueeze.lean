import OTSelector.Probability.ExpectationConvergenceFromBounds
import OTSelector.Limit.FinslerSemidiscretePressureData
import OTSelector.Geometry.FinslerSupportedSemidiscretePressure
import OTSelector.Limit.PressureLowerBound
import OTSelector.Reconstruction.RelativeExpectedPressure
import OTSelector.Probability.SupportedIID

/-!
# The pressure squeeze for the physical Dirichlet semidiscrete mean

The physical semidiscrete mean is the expectation of the supported empirical
pressure.  Consequently:

* it is bounded below by `-|t| ‖f‖` (the deterministic slack bound);
* it is bounded above by `2 k diam(K) + |t| ‖f‖` (the identity assignment);
* a probability lower bound together with an expectation upper bound at a
  common value `L` forces it to converge to `L`.

This isolates the two sharp analytic inputs of the paper: the probability
lower bound and the second-moment expectation upper bound.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000

namespace OTSelector.Pressure
open Probability

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- The slack cost of a one-Lipschitz potential is at most twice the carrier
diameter. -/
theorem distanceSlackEdgeCost_le_two_diam
    {n : ℕ} {X Y : Fin n → M} {φ : M → ℝ} (hφ : LipschitzWith 1 φ)
    {K : Set M} (hKc : IsCompact K) (hXK : ∀ i, X i ∈ K) (hYK : ∀ j, Y j ∈ K)
    (i j : Fin n) :
    distanceSlackEdgeCost X Y φ i j ≤ 2 * Metric.diam K := by
  have hd : dist (X i) (Y j) ≤ Metric.diam K :=
    Metric.dist_le_diam_of_mem hKc.isBounded (hXK i) (hYK j)
  have hp : φ (X i) - φ (Y j) ≤ dist (X i) (Y j) := by
    have h := hφ.dist_le_mul (X i) (Y j)
    rw [NNReal.coe_one, one_mul, Real.dist_eq] at h
    exact (abs_le.mp h).2
  unfold distanceSlackEdgeCost
  linarith

/-- The supported empirical pressure is measurably dependent on the sample. -/
theorem measurable_supportedDistancePressure
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (X Y : Fin n → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (φ : M → ℝ) (hφ : Continuous φ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    Measurable (fun s ↦ supportedDistancePressure μ ν K hK hμ hν
      (fun i ↦ X i s) (fun j ↦ Y j s) φ k f t) := by
  have hφm : Measurable φ := hφ.measurable
  have hc : ∀ i j, Measurable (fun s ↦
      k * distanceSlackEdgeCost (fun i ↦ X i s) (fun j ↦ Y j s) φ i j) := by
    intro i j
    apply Measurable.const_mul
    simp only [distanceSlackEdgeCost]
    exact (((hX i).dist (hY j)).sub (hφm.comp (hY j))).add (hφm.comp (hX i))
  have hg : ∀ i j, Measurable (fun s ↦
      f (supportProjection μ K hK hμ (X i s), supportProjection ν K hK hν (Y j s))) := by
    intro i j
    exact f.continuous.measurable.comp
      (Measurable.prodMk ((measurable_supportProjection μ K hK hμ).comp (hX i))
        ((measurable_supportProjection ν K hK hν).comp (hY j)))
  simpa only [supportedDistancePressure, div_eq_mul_inv] using
    (OTSelector.Reconstruction.measurable_perturbedAssignmentValue_div
      (fun s ↦ fun i j ↦ k * distanceSlackEdgeCost (fun i ↦ X i s) (fun j ↦ Y j s) φ i j)
      (fun s ↦ fun i j ↦ f (supportProjection μ K hK hμ (X i s),
        supportProjection ν K hK hν (Y j s))) t hc hg)

end OTSelector.Pressure

namespace OTSelector.Pressure
open Probability

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- The identity assignment bounds the supported empirical pressure above by
the carrier diameter and the probe norm. -/
theorem supportedDistancePressure_le_two_diam_mul
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (X Y : Fin n → M) (φ : M → ℝ) (hφ : LipschitzWith 1 φ)
    (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (hn : 0 < n) (hk : 0 ≤ k) (hKc : IsCompact K)
    (hXK : ∀ i, X i ∈ K) (hYK : ∀ j, Y j ∈ K) :
    supportedDistancePressure μ ν K hK hμ hν X Y φ k f t ≤
      2 * k * Metric.diam K + |t| * (‖f‖₊ : ℝ) := by
  let cost : Fin n → Fin n → ℝ := fun i j ↦ k * distanceSlackEdgeCost X Y φ i j
  let probe : Fin n → Fin n → ℝ := fun i j ↦ f
    (supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j))
  have hG (i j : Fin n) : |probe i j| ≤ (‖f‖₊ : ℝ) := by
    have h := f.norm_coe_le_norm
      (supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j))
    simpa only [probe, coe_nnnorm, Real.norm_eq_abs] using h
  have hterm (i : Fin n) :
      perturbedEdgeCost cost probe t i i ≤
        2 * k * Metric.diam K + |t| * (‖f‖₊ : ℝ) := by
    have hs : distanceSlackEdgeCost X Y φ i i ≤ 2 * Metric.diam K :=
      distanceSlackEdgeCost_le_two_diam hφ hKc hXK hYK i i
    have hc : cost i i ≤ k * (2 * Metric.diam K) :=
      mul_le_mul_of_nonneg_left hs hk
    have hp : t * probe i i ≤ |t| * (‖f‖₊ : ℝ) := by
      calc t * probe i i ≤ |t * probe i i| := le_abs_self _
        _ = |t| * |probe i i| := abs_mul _ _
        _ ≤ |t| * (‖f‖₊ : ℝ) :=
            mul_le_mul_of_nonneg_left (hG i i) (abs_nonneg t)
    simp only [perturbedEdgeCost, cost]
    linarith
  have hle := perturbedAssignmentValue_le cost probe t (Equiv.refl (Fin n))
  have hcost : assignmentCost (perturbedEdgeCost cost probe t) (Equiv.refl (Fin n)) =
      ∑ i, perturbedEdgeCost cost probe t i i := rfl
  unfold supportedDistancePressure
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  refine hle.trans ?_
  rw [hcost]
  calc ∑ i : Fin n, perturbedEdgeCost cost probe t i i
      ≤ ∑ _i : Fin n, (2 * k * Metric.diam K + |t| * (‖f‖₊ : ℝ)) :=
        Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (n : ℝ) * (2 * k * Metric.diam K + |t| * (‖f‖₊ : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (2 * k * Metric.diam K + |t| * (‖f‖₊ : ℝ)) * (n : ℝ) := by ring

end OTSelector.Pressure

namespace OTSelector.Pressure
open Probability

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- The supported empirical pressure is integrable: it lies between the slack
lower bound and the identity-assignment upper bound. -/
theorem integrable_supportedDistancePressure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (X Y : Fin n → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (φ : M → ℝ) (hφ : LipschitzWith 1 φ) (hφc : Continuous φ)
    (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (hn : 0 < n) (hk : 0 ≤ k) (hKc : IsCompact K)
    (hXs : ∀ᵐ s ∂P, ∀ i, X i s ∈ K) (hYs : ∀ᵐ s ∂P, ∀ j, Y j s ∈ K) :
    Integrable (fun s ↦ supportedDistancePressure μ ν K hK hμ hν
      (fun i ↦ X i s) (fun j ↦ Y j s) φ k f t) P := by
  set G : ℝ := (‖f‖₊ : ℝ) with hGdef
  set D : ℝ := 2 * k * Metric.diam K + |t| * G with hDdef
  have hm := measurable_supportedDistancePressure μ ν K hK hμ hν X Y hX hY
    φ hφc k f t
  have hGD : |t| * G ≤ D := by
    rw [hDdef]; have := mul_nonneg hk (by positivity : (0 : ℝ) ≤ 2 * Metric.diam K)
    linarith
  refine (integrable_const (max (|t| * G) D)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [hXs, hYs] with s hxs hys
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hlow := supportedDistancePressure_ge_neg_abs_mul μ ν K hK hμ hν hn
      (fun i ↦ X i s) (fun j ↦ Y j s) φ hφ k hk f t
    have hle : |t| * G ≤ max (|t| * G) D := le_max_left _ _
    linarith
  · have hup := supportedDistancePressure_le_two_diam_mul μ ν K hK hμ hν
      (fun i ↦ X i s) (fun j ↦ Y j s) φ hφ k f t hn hk hKc hxs hys
    have hle : D ≤ max (|t| * G) D := le_max_right _ _
    linarith

end OTSelector.Pressure

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- The supported empirical pressure evaluated in the Finsler metric space. -/
noncomputable def finslerSupportedPressure
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (X Y : Fin n → M) (φ : M → ℝ) (k : ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) : ℝ :=
  let _instFinslerSupportedPressure : MetricSpace M := F.metricSpace
  Pressure.supportedDistancePressure μ ν K hK hμ hν X Y φ k f t

/-- Convergence of the physical semidiscrete mean from a probability lower
bound and an expectation upper bound for the supported empirical pressure.

The pointwise lower bound `-|t| ‖f‖ ≤ J_n` is the deterministic slack bound; it
is the only additional input beyond the two sharp asymptotic estimates. -/
theorem tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
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
    (hφ : let _instSqueezePotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t L : ℝ)
    (hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t < L - ε})
        atTop (𝓝 0))
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤ L + ε) :
    Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop (𝓝 L) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  let G : ℝ := |t| * (‖f‖₊ : ℝ)
  let k : ℕ → ℝ := fun n ↦ ((n + 1 : ℕ) : ℝ) ^
    (2 / ((Module.finrank ℝ E : ℝ) - 1))
  let V : ∀ n, Ω n → ℝ := fun n s ↦ finslerSupportedPressure F μ ν K
    hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ (k n) f t
  have hφc : Continuous φ := hφ.continuous
  have hkpos (n : ℕ) : 0 < k n :=
    Real.rpow_pos_of_pos (by positivity) _
  have hknonneg (n : ℕ) : 0 ≤ k n := (hkpos n).le
  -- Measurability of the empirical pressure.
  have hVmeas (n : ℕ) : Measurable (V n) := by
    simpa only [V, finslerSupportedPressure] using
      (Pressure.measurable_supportedDistancePressure μ ν K hK.measurableSet hμ hν
        (X n) (Y n) (hX n) (hY n) φ hφc (k n) f t)
  -- Almost sure membership of both samples in the compact carrier.
  have hXK (n : ℕ) : ∀ᵐ s ∂P n, ∀ i, X n i s ∈ K := by
    apply ae_all_iff.mpr
    intro i
    exact ae_of_ae_map (hX n i).aemeasurable (by rw [hXlaw n i]; exact hμ)
  have hYK (n : ℕ) : ∀ᵐ s ∂P n, ∀ j, Y n j s ∈ K := by
    apply ae_all_iff.mpr
    intro j
    exact ae_of_ae_map (hY n j).aemeasurable (by rw [hYlaw n j]; exact hν)
  have hVint (n : ℕ) : Integrable (V n) (P n) := by
    simpa only [V, finslerSupportedPressure] using
      (Pressure.integrable_supportedDistancePressure (P n) μ ν K hK.measurableSet hμ hν
        (X n) (Y n) (hX n) (hY n) φ hφ hφc (k n) f t (Nat.succ_pos n)
        (hknonneg n) hK (hXK n) (hYK n))
  -- The abstract squeeze engine, applied at the fixed value `L`.
  have hmotor : Tendsto (fun n ↦ ∫ s, V n s ∂P n) atTop (𝓝 L) := by
    refine OTSelector.Probability.tendsto_integral_of_probability_lower_and_integral_upper
      P V (fun n ↦ hVmeas n) (fun n ↦ hVint n) L (|L| + G) (by positivity) ?_
      ?_ ?_
    · intro n
      filter_upwards [hXK n, hYK n] with s hxs hys
      have hlow : -(|t| * (‖f‖₊ : ℝ)) ≤ V n s := by
        simpa only [V, finslerSupportedPressure] using
          (Pressure.supportedDistancePressure_ge_neg_abs_mul μ ν K
            hK.measurableSet hμ hν (Nat.succ_pos n) (fun i ↦ X n i s)
            (fun j ↦ Y n j s) φ hφ (k n) (hknonneg n) f t)
      have hLM : L - (|L| + G) ≤ -G := by
        have := le_abs_self L; linarith
      exact hLM.trans hlow
    · intro ε hε
      exact hprob ε hε
    · intro ε hε
      exact hupper ε hε
  -- Identify each empirical integral with the Dirichlet semidiscrete mean.
  have hident (n : ℕ) : ∫ s, V n s ∂P n =
      finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n := by
    rw [finslerSemidiscreteMean]
    simp only [V, finslerSupportedPressure, k]
    exact (hF.integral_supportedDistancePressure_eq_fullSemidiscreteValue m μ ν
      hdim hμchart hνchart hcomplete K hK hμ hν (P n) (X n) (Y n) (hX n) (hY n)
      (hXi n) (hYi n) (hXlaw n) (hYlaw n) (hXY n) φ hφc (hkpos n) f t).2
  exact hmotor.congr' (Filter.Eventually.of_forall hident)

/-- The analytic squeeze packages the single pressure producer: if the target
pressure is differentiable and is both a probability-lower and an
expectation-upper limit of the supported empirical pressure, then it is the
pointwise pressure limit of the physical semidiscrete means. -/
theorem exists_finsler_pressure_producer_of_squeeze
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
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
    (hφ : let _instSqueezeProducerPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((K × K) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hprob : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressure f t - ε}) atTop (𝓝 0))
    (hupper : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε → ∀ᶠ n in atTop,
      ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤
          pressure f t + ε) :
    let _instSqueezeProducerMetric : MetricSpace M := F.metricSpace
    ∃ (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
      (radius derivative : ((K × K) →ᵇ ℝ) → ℝ),
      (∀ f, 0 < radius f) ∧
      (∀ f, HasDerivAt (pressure f) (derivative f) 0) ∧
      (∀ f t, |t| < radius f →
        Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
          atTop (𝓝 (pressure f t))) := by
  refine ⟨pressure, radius, derivative, hradius, hderiv, ?_⟩
  intro f t ht
  exact tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper
    hF hcomplete m hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
    hXlaw hYlaw hXY φ hφ f t (pressure f t)
    (fun ε hε ↦ hprob f t ε ht hε) (fun ε hε ↦ hupper f t ε ht hε)

/-- The probability lower bound and the expectation upper bound, together with
differentiability of the target pressure, give the whole-face selector directly. -/
theorem existsUnique_selector_of_finsler_squeeze
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
    (hφ : let _instSqueezeSelectorPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((K × K) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hprob : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressure f t - ε}) atTop (𝓝 0))
    (hupper : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε → ∀ᶠ n in atTop,
      ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤
          pressure f t + ε) :
    let _instSqueezeSelectorMetric : MetricSpace M := F.metricSpace
    let _instSqueezeSelectorProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
        (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
      (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
        {sample | ∃ γ ∈ Pressure.empiricalOptimalFace
          (fun i ↦ X n i sample) (fun i ↦ Y n i sample), γ ∉ U}) atTop (𝓝 0)) ∧
      IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  have hdim2 : 2 ≤ Module.finrank ℝ E := by omega
  have hconv : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
      Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
        atTop (𝓝 (pressure f t)) := by
    intro f t ht
    exact tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper
      hF hcomplete m hdim2 μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
      hXlaw hYlaw hXY φ hφ f t (pressure f t)
      (fun ε hε ↦ hprob f t ε ht hε) (fun ε hε ↦ hupper f t ε ht hε)
  exact existsUnique_selector_of_finsler_semidiscrete_convergence
    hF hcomplete m hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
    hXlaw hYlaw hXY φ hφ pressure radius derivative hradius hconv hderiv

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
