import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalSceneNormalized
import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureBound

/-!
# Actual signed legal pressure pays the normalized shifted energy exactly

The probe is retained with its sign. Only the nonnegative shift is charged by
the actual normalized maximum-cardinality mass, whose original mean is at most
one. This avoids estimating the retained probe twice before the Palm limit.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The true normalized signed optimum has exactly the original normalized
legal pressure as its mean; this keeps its probe sign unchanged. -/
theorem integrable_and_integral_legalMarkedNormalizedOptimalPlan_eq_scalePressure
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (fun ω ↦ ∫ e, legalMarkedPhysicalTiltedEdge q kin g t e
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω)
      (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ∧
    (∫ ω, ∫ e, legalMarkedPhysicalTiltedEdge q kin g t e
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) =
      legalMarkedScalePressure q id id α β kin g L t := by
  have ht := integrable_and_integral_legalMarkedOptimalPlan_eq_pressure q hq hL.le
    α β hC hG hk hkb hhom hg hgb t
  have heq (ω : TwoMarkedCloudSpace q ℝ ℝ) :=
    integral_legalMarkedNormalizedOptimalPlan q hL.le kin g t ω
      (legalMarkedPhysicalTiltedEdge q kin g t)
  constructor
  · exact (ht.1.const_mul (L ^ q)⁻¹).congr (.of_forall (fun ω ↦ (heq ω).symm))
  · simp_rw [heq]
    rw [integral_const_mul, ht.2]
    simp only [legalMarkedScalePressure, hL, ↓reduceIte, div_eq_mul_inv, mul_comm]

/-- The true normalized original maximum-cardinality mass has an integrable
real readout and mean at most one, directly from its original count mean. -/
theorem integrable_and_integral_legalMarkedNormalizedOptimalPlan_mass_le_one
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Integrable (fun ω ↦ (legalMarkedNormalizedOptimalPlan q L kin g t ω).real univ)
      (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ∧
    (∫ ω, (legalMarkedNormalizedOptimalPlan q L kin g t ω).real univ
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤ 1 := by
  have : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ,
      IsFiniteMeasure (legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    fun ω ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t ω
  have hm : Measurable (fun ω ↦ legalMarkedNormalizedOptimalPlan q L kin g t ω univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp
      (measurable_legalMarkedNormalizedOptimalPlan q L hk hg t)
  have hb := lintegral_legalMarkedNormalizedOptimalPlan_univ_le_one q hL α β kin g t
  constructor
  · exact integrable_toReal_of_lintegral_ne_top hm.aemeasurable (hb.trans_lt ENNReal.one_lt_top).ne
  · change (∫ ω, (legalMarkedNormalizedOptimalPlan q L kin g t ω univ).toReal
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤ 1
    rw [integral_toReal hm.aemeasurable (.of_forall (fun ω ↦ measure_lt_top _ _))]
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hb

/-- The actual full shifted signed cost is bounded by the actual signed legal
pressure plus one shift. The true selected probe is never replaced by a bound. -/
theorem lintegral_legalMarkedNormalizedOptimalPlan_shifted_signed_le
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (legalMarkedPhysicalTiltedEdge q kin g t e + |t| * G)
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤
      ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) := by
  let Γ := legalMarkedNormalizedOptimalPlan q L kin g t
  have : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ, IsFiniteMeasure (Γ ω) :=
    fun ω ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t ω
  let F (e : LegalMarkedPhysicalEdge q) := legalMarkedPhysicalTiltedEdge q kin g t e + |t| * G
  have hFn : ∀ e, 0 ≤ F e := by
    intro e
    have habs : |t * g e.1.2 e.2.2| ≤ |t| * G := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg t)
    dsimp [F, legalMarkedPhysicalTiltedEdge]
    linarith [(abs_le.mp habs).1, hkn e.1.2 e.2.2 (e.2.1 - e.1.1)]
  have hV0 : ENNReal.ofReal (L ^ q) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hL q)).ne'
  have hint (ω : TwoMarkedCloudSpace q ℝ ℝ) (f : LegalMarkedPhysicalEdge q → ℝ) : Integrable f (Γ ω) :=
    (integrable_legalMarkedFixedOptimalPlan q (mSourceCount ω) (mTargetCount ω)
      L (L ^ q) kin g t ω f).smul_measure (ENNReal.inv_ne_top.mpr hV0)
  have heq (ω : TwoMarkedCloudSpace q ℝ ℝ) :
      (∫ e, F e ∂Γ ω) =
        (∫ e, legalMarkedPhysicalTiltedEdge q kin g t e ∂Γ ω) + |t| * G * (Γ ω).real univ := by
    rw [show F = fun e ↦ legalMarkedPhysicalTiltedEdge q kin g t e + |t| * G from rfl,
      integral_add (hint ω _) (integrable_const _), integral_const]
    simp only [smul_eq_mul, mul_comm]
  obtain ⟨ht, htmean⟩ := integrable_and_integral_legalMarkedNormalizedOptimalPlan_eq_scalePressure q hq hL
    α β hC hG hk hkb hhom hg hgb t
  obtain ⟨hm, hmmean⟩ := integrable_and_integral_legalMarkedNormalizedOptimalPlan_mass_le_one q hL α β hk hg t
  have hI : Integrable (fun ω ↦ ∫ e, F e ∂Γ ω)
      (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) :=
    (ht.add (hm.const_mul (|t| * G))).congr (.of_forall (fun ω ↦ (heq ω).symm))
  have hinner (ω : TwoMarkedCloudSpace q ℝ ℝ) :
      (∫⁻ e, ENNReal.ofReal (F e) ∂Γ ω) = ENNReal.ofReal (∫ e, F e ∂Γ ω) :=
    (ofReal_integral_eq_lintegral_ofReal (hint ω _) (.of_forall hFn)).symm
  change (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (F e) ∂Γ ω
    ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤ _
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal hI (.of_forall (fun ω ↦ integral_nonneg hFn))]
  apply ENNReal.ofReal_le_ofReal
  simp_rw [heq]
  rw [integral_add ht (hm.const_mul (|t| * G)), integral_const_mul, htmean]
  nlinarith [mul_le_mul_of_nonneg_left hmmean (mul_nonneg (abs_nonneg t) hG)]

end OTSelector.Reconstruction
