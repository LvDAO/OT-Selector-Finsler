import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCountExhaustion
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficVolume

/-! Count-weighted bad events on the actual unchanged full original scene. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}

/-- The actual full input count of one immutable color over a spatial set and all clocks. -/
def originalScreeningActualColorCount (K : Set (Fin q → ℝ)) (c : Fin 2)
    (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  ((scene.2 : Measure (LegalColoredInputPoint q)) ((K ×ˢ (univ : Set ℝ)) ×ˢ {c})).toReal

/-- The actual sum of both unchanged full input counts, with no selected endpoints. -/
def originalScreeningActualCount (K : Set (Fin q → ℝ))
    (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  originalScreeningActualColorCount K 0 scene + originalScreeningActualColorCount K 1 scene

/-- Actual full input counts remain measurable before selecting the exceptional event. -/
theorem measurable_originalScreeningActualColorCount
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (c : Fin 2) :
    Measurable (originalScreeningActualColorCount K c) :=
  ((Measure.measurable_coe ((hK.prod MeasurableSet.univ).prod (measurableSet_singleton c))).comp
    (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal

theorem measurable_originalScreeningActualCount
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) :
    Measurable (originalScreeningActualCount K) :=
  (measurable_originalScreeningActualColorCount hK 0).add
    (measurable_originalScreeningActualColorCount hK 1)

theorem originalScreeningActualCount_nonneg (K : Set (Fin q → ℝ))
    (scene : LegalMarkedOptimalInputScene q) : 0 ≤ originalScreeningActualCount K scene :=
  add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

variable {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q α β kin g)

/-- Each genuine full input color has its exact volume mean and square-root volume
deviation on any finite-volume spatial set, including all scalar clocks. -/
theorem LegalWeightedStationaryPoissonMatching.originalScreeningActualColorCount_moments
    (K : Set (Fin q → ℝ)) (c : Fin 2) (hK : MeasurableSet K) (hfin : volume K ≠ ∞) :
    (∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      (scene.2 : Measure (LegalColoredInputPoint q)) ((K ×ˢ (univ : Set ℝ)) ×ˢ {c}) < ∞) ∧
    Integrable (originalScreeningActualColorCount K c)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ scene, originalScreeningActualColorCount K c scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) = volume.real K ∧
    (∫ scene, |originalScreeningActualColorCount K c scene - volume.real K|
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ Real.sqrt (volume.real K) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  have : IsProbabilityMeasure α := by
    rw [← Q.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  have : IsProbabilityMeasure β := by
    rw [← Q.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  let νc : Measure ℝ := if c = 0 then α else β
  have : IsProbabilityMeasure νc := by
    dsimp [νc]
    split <;> infer_instance
  have hν : legalMarkedInputColorIntensity q (Q.law : Measure (LegalMarkedOptimalInputScene q)) c =
      (volume : Measure (Fin q → ℝ)).prod νc := by
    fin_cases c
    · simpa [νc] using Q.inputColorIntensities_eq_volume_prod.1
    · simpa [νc] using Q.inputColorIntensities_eq_volume_prod.2
  have hlaw : ∀ {A L : Set (LegalMarkedPhysicalPoint q)}, MeasurableSet A → IsCompact L →
      A ⊆ L → HasLaw (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {c}))
        ((poissonMeasure (((volume : Measure (Fin q → ℝ)).prod νc) A).toNNReal).map
          (Nat.cast : ℕ → ℝ≥0∞)) (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
    intro A L hA hL hAL
    fin_cases c
    · simpa [νc] using Q.original_source_countLaw_of_compact_carrier hA hL hAL
    · simpa [νc] using Q.original_target_countLaw_of_compact_carrier hA hL hAL
  have h := originalActualInputColorCount_moments_of_compact_laws
    (Q.law : Measure (LegalMarkedOptimalInputScene q)) c
    ((volume : Measure (Fin q → ℝ)).prod νc) hν hlaw (hK.prod MeasurableSet.univ)
    (by simpa only [Measure.prod_prod, measure_univ, mul_one] using hfin)
  simp only [Measure.prod_prod, measure_univ, mul_one] at h
  convert h using 1
  rfl

/-- The actual sum of both full original colors has mean twice the physical volume and
centered first moment at most twice its square root, without color/event independence. -/
theorem LegalWeightedStationaryPoissonMatching.originalScreeningActualCount_moments
    (K : Set (Fin q → ℝ)) (hK : MeasurableSet K) (hfin : volume K ≠ ∞) :
    (∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), ∀ c : Fin 2,
      (scene.2 : Measure (LegalColoredInputPoint q)) ((K ×ˢ (univ : Set ℝ)) ×ˢ {c}) < ∞) ∧
    Integrable (originalScreeningActualCount K) (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ scene, originalScreeningActualCount K scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) = 2 * volume.real K ∧
    (∫ scene, |originalScreeningActualCount K scene - 2 * volume.real K|
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ 2 * Real.sqrt (volume.real K) := by
  have hs := Q.originalScreeningActualColorCount_moments K 0 hK hfin
  have ht := Q.originalScreeningActualColorCount_moments K 1 hK hfin
  have hIs := (hs.2.1.sub (integrable_const (volume.real K))).abs
  have hIt := (ht.2.1.sub (integrable_const (volume.real K))).abs
  refine ⟨?_, hs.2.1.add ht.2.1, ?_, ?_⟩
  · filter_upwards [hs.1, ht.1] with scene h0 h1
    intro c
    fin_cases c <;> assumption
  · change (∫ scene, originalScreeningActualColorCount K 0 scene +
        originalScreeningActualColorCount K 1 scene
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) = 2 * volume.real K
    rw [integral_add hs.2.1 ht.2.1, hs.2.2.1, ht.2.2.1]
    ring
  · calc
      _ ≤ ∫ scene, |originalScreeningActualColorCount K 0 scene - volume.real K| +
          |originalScreeningActualColorCount K 1 scene - volume.real K|
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
        apply integral_mono (((hs.2.1.add ht.2.1).sub (integrable_const (2 * volume.real K))).abs)
          (hIs.add hIt)
        intro scene
        change |originalScreeningActualColorCount K 0 scene +
          originalScreeningActualColorCount K 1 scene - 2 * volume.real K| ≤ _
        have he : originalScreeningActualColorCount K 0 scene +
            originalScreeningActualColorCount K 1 scene - 2 * volume.real K =
            (originalScreeningActualColorCount K 0 scene - volume.real K) +
            (originalScreeningActualColorCount K 1 scene - volume.real K) := by ring
        rw [he]
        exact abs_add_le _ _
      _ = _ := integral_add hIs hIt
      _ ≤ _ := by linarith [hs.2.2.2, ht.2.2.2]

/-- Any measurable selected bad event is controlled by its original probability and the
actual two-color full input count discrepancy, even when it depends on the entire scene. -/
theorem LegalWeightedStationaryPoissonMatching.integral_indicator_originalScreeningActualCount_le
    (K : Set (Fin q → ℝ)) (hK : MeasurableSet K) (hfin : volume K ≠ ∞)
    (bad : Set (LegalMarkedOptimalInputScene q)) (hbad : MeasurableSet bad) :
    (∫ scene, bad.indicator (originalScreeningActualCount K) scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      2 * volume.real K * (Q.law : Measure (LegalMarkedOptimalInputScene q)).real bad +
        2 * Real.sqrt (volume.real K) := by
  have h := Q.originalScreeningActualCount_moments K hK hfin
  exact (integral_indicator_le_center_mass_add_abs
    (Q.law : Measure (LegalMarkedOptimalInputScene q)) h.2.1
    (2 * volume.real K) bad hbad).trans (add_le_add le_rfl h.2.2.2)

/-- The actual two-color full input count in the same chosen physical side-2R cube. -/
abbrev originalScreeningPhysicalCubeActualCount
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :=
  originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))

/-- Exact mean and sqrt-volume centered discrepancy for the same-frame full input count. -/
theorem LegalWeightedStationaryPoissonMatching.originalScreeningPhysicalCubeActualCount_moments
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    Integrable (originalScreeningPhysicalCubeActualCount b R)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ scene, originalScreeningPhysicalCubeActualCount b R scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) =
        2 * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) ∧
    (∫ scene, |originalScreeningPhysicalCubeActualCount b R scene -
        2 * volume.real (originalCenteredPhysicalCubeRegion b (2 * R))|
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        2 * Real.sqrt (volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) :=
  (Q.originalScreeningActualCount_moments _ (measurableSet_originalOrientedTraffic_cube b R)
    (by rw [volume_originalOrientedTraffic_cube]; exact isCompact_Icc.measure_ne_top)).2

/-- The requested actual count-weighted exceptional estimate in the same original cube. -/
theorem LegalWeightedStationaryPoissonMatching.integral_indicator_originalScreeningPhysicalCubeActualCount_le
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (bad : Set (LegalMarkedOptimalInputScene q)) (hbad : MeasurableSet bad) :
    (∫ scene, bad.indicator (originalScreeningPhysicalCubeActualCount b R) scene
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      2 * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
        (Q.law : Measure (LegalMarkedOptimalInputScene q)).real bad +
      2 * Real.sqrt (volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) :=
  Q.integral_indicator_originalScreeningActualCount_le _
    (measurableSet_originalOrientedTraffic_cube b R)
    (by rw [volume_originalOrientedTraffic_cube]; exact isCompact_Icc.measure_ne_top) bad hbad

end OTSelector.Reconstruction
