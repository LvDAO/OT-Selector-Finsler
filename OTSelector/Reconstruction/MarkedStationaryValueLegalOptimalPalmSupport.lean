import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalPalmLimit
import OTSelector.Probability.MarkedCloudCarriers
import OTSelector.Transport.CyclicMonotonicity.CountableRectangleSupport

/-!
# The original legal clock gap survives actual optimal scene limits

The same original mark pair carrier gives every sampled legal edge the fixed
positive clock gap. Actual rooting preserves it exactly. Open bad-clock mass
is lower semicontinuous, so every actual weak scene limit and its constructed
full-dimensional paired-edge Palm retain this legal support.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
local instance markedStationaryValueLegalOptimalPalmSupportLocalPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Actual product-a.e. scalar separation becomes one simultaneous carrier for
all edges of the actual signed legal optimum. -/
theorem ae_clockGap_legalMarkedOptimalPlan (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (ρ : ℝ≥0) {δ : ℝ} (hsep : ∀ᵐ p ∂α.prod β, δ ≤ |p.2 - p.1|) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      ∀ᵐ e ∂legalMarkedOptimalPlan q L r kin g t ω, δ ≤ e.2.2 - e.1.2 := by
  classical
  filter_upwards [ae_all_mMarkPair q α β ρ (P := fun a b ↦ δ ≤ |b - a|) hsep] with ω hω
  unfold legalMarkedOptimalPlan legalMarkedFixedOptimalPlan
  rw [ae_finsetSum_measure_iff]
  intro e he
  have hgset : MeasurableSet {e : LegalMarkedPhysicalEdge q | δ ≤ e.2.2 - e.1.2} :=
    measurableSet_le measurable_const (measurable_snd.snd.sub measurable_fst.snd)
  rw [ae_dirac_iff hgset]
  have hf : mSourceMark ω e.1 < mTargetMark ω e.2 := by
    have h := (firstLegalMarkedOptimalMatching_isLegalOptimal q (mSourceCount ω)
      (mTargetCount ω) id id r kin g t ω).1 he
    simpa only [legalMarkedGraph, Finset.mem_filter, Finset.mem_univ, true_and, id_eq] using h
  have hpos : 0 ≤ mTargetMark ω e.2 - mSourceMark ω e.1 := by linarith
  simpa only [legalMarkedPhysicalEdge, abs_of_nonneg hpos] using hω e.1 e.2

/-- Actual original root averaging has identically zero bad-clock mass. -/
theorem lintegral_legalMarkedOptimalRootedSceneLaw_bad_clock_eq_zero
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t L : ℝ) (hL : 0 < L)
    {δ : ℝ} (hsep : ∀ᵐ p ∂α.prod β, δ ≤ |p.2 - p.1|) :
    (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.2.2 - e.1.2 < δ}
      ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure
        (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) = 0 := by
  have : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ,
      IsFiniteMeasure (legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    fun ω ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t ω
  have hbad : IsOpen {e : LegalMarkedPhysicalEdge q | e.2.2 - e.1.2 < δ} :=
    isOpen_lt (continuous_snd.snd.sub continuous_fst.snd) continuous_const
  have hread : Measurable (fun scene : CavityLocalScene
      (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
      (scene.1 : Measure (LegalMarkedPhysicalEdge q)) {e | e.2.2 - e.1.2 < δ}) :=
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hbad).comp continuous_fst).measurable
  unfold legalMarkedOptimalRootedSceneLaw
  rw [lintegral_physicalSceneRootedLocalSceneLaw _ _ _ _ _ _ _ _ _ _ _ _ _ _ hread]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_clockGap_legalMarkedOptimalPlan q L (L ^ q) kin g t α β
    (Real.toNNReal (L ^ q)) hsep] with ω hω
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards with z
  change physicalSceneRootedPlan (legalMarkedNormalizedOptimalPlan q L kin g t ω)
    (legalMarkedCenteredCoordinate q L) Prod.snd (L ^ q) z {e | e.2.2 - e.1.2 < δ} = 0
  rw [physicalSceneRootedPlan, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_physicalSceneRootedObservation _
      (measurable_legalMarkedCenteredCoordinate q L) Prod.snd measurable_snd z) hbad.measurableSet]
  have hzero : legalMarkedNormalizedOptimalPlan q L kin g t ω {e | e.2.2 - e.1.2 < δ} = 0 := by
    rw [legalMarkedNormalizedOptimalPlan, Measure.smul_apply, smul_eq_mul]
    have hz : legalMarkedOptimalPlan q L (L ^ q) kin g t ω {e | e.2.2 - e.1.2 < δ} = 0 := by
      simpa only [not_le] using ae_iff.mp hω
    rw [hz, mul_zero]
  change ENNReal.ofReal (L ^ q) *
    legalMarkedNormalizedOptimalPlan q L kin g t ω {e | e.2.2 - e.1.2 < δ} = 0
  rw [hzero, mul_zero]

/-- Every weak limit of these actual canonical legal optimum laws preserves
the original separated clock support, including its constructed paired Palm. -/
theorem ae_cubePalm_clockGap_of_legalMarkedOptimalRootedSceneLaw_tendsto
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    {Q : ProbabilityMeasure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    {δ : ℝ} (hsep : ∀ᵐ p ∂α.prod β, δ ≤ |p.2 - p.1|) :
    (∀ᵐ scene ∂(Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))),
      ∀ᵐ e ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q)), δ ≤ e.2.2 - e.1.2) ∧
    (∀ᵐ m ∂cubePalm (Fin q) (physicalScenePairCampbell
      (Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))),
      δ ≤ m.1.2 - m.1.1) := by
  have hbad : IsOpen {e : LegalMarkedPhysicalEdge q | e.2.2 - e.1.2 < δ} :=
    isOpen_lt (continuous_snd.snd.sub continuous_fst.snd) continuous_const
  have hz := ae_eq_zero_of_lowerSemicontinuous_lintegral_tendsto_zero Q _ hweak
    (fun scene ↦ (scene.1 : Measure (LegalMarkedPhysicalEdge q)) {e | e.2.2 - e.1.2 < δ})
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hbad).comp continuous_fst) ?_
  · have hs : ∀ᵐ scene ∂(Q : Measure (CavityLocalScene
        (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))),
        ∀ᵐ e ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q)), δ ≤ e.2.2 - e.1.2 := by
      filter_upwards [hz] with scene hscene
      simpa only [ae_iff, not_le] using hscene
    exact ⟨hs, ae_cubePalm_of_physicalScenePlan _
      (measurableSet_le measurable_const (measurable_fst.snd.sub measurable_fst.fst)) hs⟩
  · simp_rw [lintegral_legalMarkedOptimalRootedSceneLaw_bad_clock_eq_zero q hq α β kin hk g hg
      t _ _ hsep]
    exact tendsto_const_nhds

end OTSelector.Reconstruction
