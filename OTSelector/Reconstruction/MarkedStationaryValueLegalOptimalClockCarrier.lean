import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalPalmSupport

/-!
# Original closed clock carriers of actual legal optimal scenes

Original product-law clock support is kept by every selected finite edge,
by the actual physical rooting map and by every weak scene limit. This is a
closed-support assertion, not a claim about distributions of selected points.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance markedStationaryValueLegalOptimalClockCarrierLocalPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual original mark-pair law supplies one simultaneous support event
for every edge of the canonical legal optimum. -/
theorem ae_clockPair_mem_legalMarkedOptimalPlan (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (ρ : ℝ≥0) {K : Set (ℝ × ℝ)} (hK : MeasurableSet K)
    (hpair : ∀ᵐ p ∂α.prod β, p ∈ K) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      ∀ᵐ e ∂legalMarkedOptimalPlan q L r kin g t ω, (e.1.2, e.2.2) ∈ K := by
  classical
  filter_upwards [ae_all_mMarkPair q α β ρ (P := fun a b ↦ (a, b) ∈ K) hpair] with ω hω
  unfold legalMarkedOptimalPlan legalMarkedFixedOptimalPlan
  rw [ae_finsetSum_measure_iff]
  intro e he
  have hm : MeasurableSet {e : LegalMarkedPhysicalEdge q | (e.1.2, e.2.2) ∈ K} :=
    hK.preimage (measurable_fst.snd.prodMk measurable_snd.snd)
  rw [ae_dirac_iff hm]
  exact hω e.1 e.2

/-- The original closed clock support gives exactly zero bad-clock mass
under the actual independent original environment and Haar root. -/
theorem lintegral_legalMarkedOptimalRootedSceneLaw_outside_clockPair_eq_zero
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t L : ℝ) (hL : 0 < L)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K) (hpair : ∀ᵐ p ∂α.prod β, p ∈ K) :
    (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | (e.1.2, e.2.2) ∉ K}
      ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure
        (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) = 0 := by
  have : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ,
      IsFiniteMeasure (legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    fun ω ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t ω
  have hbad : IsOpen {e : LegalMarkedPhysicalEdge q | (e.1.2, e.2.2) ∉ K} :=
    hK.isOpen_compl.preimage (continuous_fst.snd.prodMk continuous_snd.snd)
  have hread : Measurable (fun scene : CavityLocalScene
      (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
      (scene.1 : Measure (LegalMarkedPhysicalEdge q)) {e | (e.1.2, e.2.2) ∉ K}) :=
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hbad).comp continuous_fst).measurable
  unfold legalMarkedOptimalRootedSceneLaw
  rw [lintegral_physicalSceneRootedLocalSceneLaw _ _ _ _ _ _ _ _ _ _ _ _ _ _ hread]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_clockPair_mem_legalMarkedOptimalPlan q L (L ^ q) kin g t α β
    (Real.toNNReal (L ^ q)) hK.measurableSet hpair] with ω hω
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards with z
  change physicalSceneRootedPlan (legalMarkedNormalizedOptimalPlan q L kin g t ω)
    (legalMarkedCenteredCoordinate q L) Prod.snd (L ^ q) z {e | (e.1.2, e.2.2) ∉ K} = 0
  rw [physicalSceneRootedPlan, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_physicalSceneRootedObservation _
      (measurable_legalMarkedCenteredCoordinate q L) Prod.snd measurable_snd z) hbad.measurableSet]
  have hzero : legalMarkedNormalizedOptimalPlan q L kin g t ω {e | (e.1.2, e.2.2) ∉ K} = 0 := by
    rw [legalMarkedNormalizedOptimalPlan, Measure.smul_apply, smul_eq_mul]
    have hz : legalMarkedOptimalPlan q L (L ^ q) kin g t ω {e | (e.1.2, e.2.2) ∉ K} = 0 :=
      ae_iff.mp hω
    rw [hz, mul_zero]
  change ENNReal.ofReal (L ^ q) *
    legalMarkedNormalizedOptimalPlan q L kin g t ω {e | (e.1.2, e.2.2) ∉ K} = 0
  rw [hzero, mul_zero]

/-- Both the actual weak scene limit and its paired Palm keep the same
original closed clock carrier. -/
theorem ae_cubePalm_clockPair_mem_of_legalMarkedOptimalRootedSceneLaw_tendsto
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    {Q : ProbabilityMeasure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    {K : Set (ℝ × ℝ)} (hK : IsClosed K) (hpair : ∀ᵐ p ∂α.prod β, p ∈ K) :
    (∀ᵐ scene ∂(Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))),
      ∀ᵐ e ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q)), (e.1.2, e.2.2) ∈ K) ∧
    (∀ᵐ m ∂cubePalm (Fin q) (physicalScenePairCampbell
      (Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))),
      m.1 ∈ K) := by
  have hbad : IsOpen {e : LegalMarkedPhysicalEdge q | (e.1.2, e.2.2) ∉ K} :=
    hK.isOpen_compl.preimage (continuous_fst.snd.prodMk continuous_snd.snd)
  have hz := ae_eq_zero_of_lowerSemicontinuous_lintegral_tendsto_zero Q _ hweak
    (fun scene ↦ (scene.1 : Measure (LegalMarkedPhysicalEdge q)) {e | (e.1.2, e.2.2) ∉ K})
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hbad).comp continuous_fst) ?_
  · have hs : ∀ᵐ scene ∂(Q : Measure (CavityLocalScene
        (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))),
        ∀ᵐ e ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q)), (e.1.2, e.2.2) ∈ K := by
      filter_upwards [hz] with scene hscene
      exact ae_iff.mpr hscene
    exact ⟨hs, ae_cubePalm_of_physicalScenePlan _
      (hK.measurableSet.preimage measurable_fst) hs⟩
  · simp_rw [lintegral_legalMarkedOptimalRootedSceneLaw_outside_clockPair_eq_zero q hq α β
      kin hk g hg t _ _ hK hpair]
    exact tendsto_const_nhds

end OTSelector.Reconstruction
