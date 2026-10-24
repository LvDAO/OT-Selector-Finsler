import OTSelector.Reconstruction.FinslerOriginalClassPressureUnitDensity
import OTSelector.Probability.WeightedMarkNormalization
import OTSelector.Reconstruction.FinslerRelativeLawActualWindowReferenceWeights

/-! Scalar retention keeps the actual normalized original class law unchanged.
Its only pressure effect is the continuous physical density weight and tilt. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {I J : Type*} [Fintype I] [Fintype J]
  [MeasurableSpace I] [MeasurableSpace J]
  [MeasurableSingletonClass I] [MeasurableSingletonClass J]

/-- Scaling every original pair-class weight scales its actual raw measure by
that same scalar, including zero individual rows and columns. -/
theorem clockClassPairMeasure_const_mul (P₀ : I → J → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    clockClassPairMeasure (fun i j ↦ c * P₀ i j) = c.toNNReal • clockClassPairMeasure P₀ := by
  rw [← Measure.coe_nnreal_smul]
  simp only [clockClassPairMeasure, finiteClassPopulationCoupling, ENNReal.ofReal_mul hc,
    Finset.smul_sum, smul_smul]
  rfl

/-- Positive scalar retention does not change the actual normalized original
joint class law. Its lost mass is kept in the separate physical intensity. -/
theorem normalizedClockClassPairMeasure_const_mul (P₀ : I → J → ℝ)
    (hP₀ : ∀ i j, 0 ≤ P₀ i j) (hmass : 0 < ∑ i, ∑ j, P₀ i j)
    {c : ℝ} (hc : 0 < c) :
    normalizedClockClassPairMeasure (fun i j ↦ c * P₀ i j) =
      normalizedClockClassPairMeasure P₀ := by
  rw [normalizedClockClassPairMeasure,clockClassPairMeasure_const_mul P₀ hc.le]
  apply normalizedFiniteLaw_smul _ hc
  rw [clockClassPairMeasure_real_univ P₀ hP₀]
  exact hmass

/-- Every original finite-intensity legal pressure is identical after a
positive scalar retention of the raw pair weights: both normalized marginal
laws, the literal legal graph and all cost data remain the same. -/
theorem finiteClassLegalPressure_normalized_weights_const_mul
    (P₀ : I → J → ℝ) (hP₀ : ∀ i j, 0 ≤ P₀ i j)
    (hmass : 0 < ∑ i, ∑ j, P₀ i j) {c : ℝ} (hc : 0 < c)
    (q : ℕ) (allowed : I → J → Prop) (r : ℝ≥0)
    (kin : I → J → (Fin q → ℝ) → ℝ) (probe : I → J → ℝ) (t : ℝ) :
    let hscaled : ∀ i j, 0 ≤ c * P₀ i j := fun i j ↦ mul_nonneg hc.le (hP₀ i j)
    let hscaledMass : 0 < ∑ i, ∑ j, c * P₀ i j := by
      simpa only [← Finset.mul_sum] using mul_pos hc hmass
    let π := clockClassJointProbability P₀ hP₀ hmass
    let πscaled := clockClassJointProbability (fun i j ↦ c * P₀ i j) hscaled hscaledMass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let αscaled := πscaled.map measurable_fst.aemeasurable
    let βscaled := πscaled.map measurable_snd.aemeasurable
    finiteClassLegalPressure q allowed (αscaled : Measure _) (βscaled : Measure _) r kin probe t =
      finiteClassLegalPressure q allowed (α : Measure _) (β : Measure _) r kin probe t := by
  simp only [ProbabilityMeasure.toMeasure_map, clockClassJointProbability, ProbabilityMeasure.coe_mk,
    normalizedClockClassPairMeasure_const_mul P₀ hP₀ hmass hc]

/-- The physical density pressure extends continuously to zero density. Its
positive Haar kinetic exponent avoids any global positive lower density bound. -/
theorem continuous_density_weighted_pressure {q : ℝ} (hq : 2 < q)
    {p : ℝ → ℝ} (hp : Continuous p) :
    Continuous (fun x : ℝ × ℝ ↦ x.1 ^ (1 - 2 / q) * p (x.2 * x.1 ^ (2 / q))) := by
  have hqpos : 0 < q := by linarith
  have ha : 0 ≤ 1 - 2 / q := by
    have h := (div_lt_one hqpos).mpr hq
    linarith
  have hb : 0 ≤ 2 / q := div_nonneg (by norm_num) hqpos.le
  exact ((Real.continuous_rpow_const ha).comp continuous_fst).mul
    (hp.comp (continuous_snd.mul ((Real.continuous_rpow_const hb).comp continuous_fst)))

/-- At zero density the true Haar-weighted contribution vanishes, even when
the unit-density stationary pressure at tilt zero is nonzero. -/
theorem density_weighted_pressure_zero {q : ℝ} (hq : 2 < q) (p : ℝ → ℝ) (t : ℝ) :
    (0 : ℝ) ^ (1 - 2 / q) * p (t * (0 : ℝ) ^ (2 / q)) = 0 := by
  have hqpos : 0 < q := by linarith
  have ha : 0 < 1 - 2 / q := sub_pos.mpr ((div_lt_one hqpos).mpr hq)
  rw [Real.zero_rpow ha.ne',zero_mul]

/-- Removing a scalar retention error has the exact continuous density effect
on a fixed original class model. This also covers a null limiting density. -/
theorem tendsto_density_weighted_pressure_retention {q density t : ℝ} (hq : 2 < q)
    {p : ℝ → ℝ} (hp : Continuous p) :
    Tendsto (fun η : ℝ ↦ ((1 - η) * density) ^ (1 - 2 / q) *
        p (t * ((1 - η) * density) ^ (2 / q))) (𝓝 0)
      (𝓝 (density ^ (1 - 2 / q) * p (t * density ^ (2 / q)))) := by
  have hmap : Tendsto (fun η : ℝ ↦ ((1 - η) * density,t)) (𝓝 0) (𝓝 (density,t)) := by
    have hfirst : Tendsto (fun η : ℝ ↦ (1 - η) * density) (𝓝 0) (𝓝 density) := by
      have hid : Tendsto (fun η : ℝ ↦ η) (𝓝 0) (𝓝 0) := tendsto_id
      have hc : Tendsto (fun _η : ℝ ↦ (1 : ℝ)) (𝓝 0) (𝓝 1) := tendsto_const_nhds
      simpa only [sub_zero, one_mul] using ((hc.sub hid).mul_const density)
    exact hfirst.prodMk_nhds tendsto_const_nhds
  exact (continuous_density_weighted_pressure hq hp).continuousAt.tendsto.comp hmap

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual reference class weights thin their zero-retention original
weights by exactly `1-η`; the original joint clock-window mask is unchanged. -/
theorem PopulationLocalPressureCore.originalWindowReferenceWeights_retention
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width) (η : ℝ) (j k : Fin Q.count) :
    D.originalWindowReferenceWeights γ gap range i ref Q η j k =
      (1 - η) * D.originalWindowReferenceWeights γ gap range i ref Q 0 j k := by
  simp only [originalWindowReferenceWeights,maskedClockFlow]
  split_ifs <;> ring

/-- The original reference normalized joint class law is independent of scalar
retention. Its actual nonzero original mass is the only normalization premise. -/
theorem PopulationLocalPressureCore.normalized_originalWindowReferenceWeights_retention
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width) {η : ℝ} (hη : η < 1)
    (hP₀ : ∀ j k, 0 ≤ D.originalWindowReferenceWeights γ gap range i ref Q 0 j k)
    (hmass : 0 < ∑ j, ∑ k, D.originalWindowReferenceWeights γ gap range i ref Q 0 j k) :
    normalizedClockClassPairMeasure (D.originalWindowReferenceWeights γ gap range i ref Q η) =
      normalizedClockClassPairMeasure (D.originalWindowReferenceWeights γ gap range i ref Q 0) := by
  have heq : D.originalWindowReferenceWeights γ gap range i ref Q η =
      fun j k ↦ (1 - η) * D.originalWindowReferenceWeights γ gap range i ref Q 0 j k :=
    funext fun j ↦ funext fun k ↦ D.originalWindowReferenceWeights_retention γ gap i ref Q η j k
  rw [heq]
  exact normalizedClockClassPairMeasure_const_mul _ hP₀ hmass (sub_pos.mpr hη)

end OTSelector.Reconstruction
