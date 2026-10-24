import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShift

/-!
# Exact actual true Palm under continuous clock-dependent shifts

The same source anchor moves by its original source clock shift, while the
full original displacement gains target shift minus source shift. Original
joint stationarity supplies the actual Haar-times-Palm Campbell decomposition;
Haar skew translation then produces the exact transformed true Palm.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local instance markedStationaryValueLegalStationaryClockShiftPalmInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryClockShiftPalmPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Both original clocks remain fixed; the full displacement gains exactly
target clock shift minus source clock shift. -/
def legalPairMarkClockShift (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (m : PhysicalPairPalmMark (Fin q)) : PhysicalPairPalmMark (Fin q) :=
  (m.1, m.2 + b 1 m.1.2 - b 0 m.1.1)

theorem measurable_legalPairMarkClockShift (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    Measurable (legalPairMarkClockShift q b) :=
  measurable_fst.prodMk ((measurable_snd.add
    ((b 1).continuous.measurable.comp measurable_fst.snd)).sub
      ((b 0).continuous.measurable.comp measurable_fst.fst))

/-- Only the actual spatial source anchor is moved in this intermediate
map; its original paired clocks and full displacement are retained. -/
def legalPairSourceAnchorClockShift (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) :
    (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) := (p.1 + b 0 p.2.1.1, p.2)

theorem measurable_legalPairSourceAnchorClockShift (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) : Measurable (legalPairSourceAnchorClockShift q b) :=
  (measurable_fst.add ((b 0).continuous.measurable.comp measurable_snd.fst.fst)).prodMk measurable_snd

/-- Haar times any original paired-mark measure is unchanged by the actual
source-clock dependent source-anchor translation. -/
theorem measurePreserving_legalPairSourceAnchorClockShift (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (η : Measure (PhysicalPairPalmMark (Fin q))) [SFinite η] :
    MeasurePreserving (legalPairSourceAnchorClockShift q b)
      ((volume : Measure (Fin q → ℝ)).prod η) ((volume : Measure (Fin q → ℝ)).prod η) := by
  change MeasurePreserving (fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
    (p.1 + b 0 p.2.1.1, p.2)) _ _
  have hskew : MeasurePreserving
      (fun p : PhysicalPairPalmMark (Fin q) × (Fin q → ℝ) ↦ (p.1, p.2 + b 0 p.1.1.1))
      (η.prod (volume : Measure (Fin q → ℝ))) (η.prod (volume : Measure (Fin q → ℝ))) :=
    (MeasurePreserving.id η).skew_product
      (measurable_snd.add ((b 0).continuous.measurable.comp measurable_fst.fst.fst))
      (.of_forall (fun m ↦ (measurePreserving_add_right volume (b 0 m.1.1)).map_eq))
  have hswap₁ : MeasurePreserving Prod.swap
      ((volume : Measure (Fin q → ℝ)).prod η) (η.prod (volume : Measure (Fin q → ℝ))) :=
    Measure.measurePreserving_swap
  have hswap₂ : MeasurePreserving Prod.swap
      (η.prod (volume : Measure (Fin q → ℝ))) ((volume : Measure (Fin q → ℝ)).prod η) :=
    Measure.measurePreserving_swap
  have h := hswap₂.comp (hskew.comp hswap₁)
  simpa only [Function.comp_def, Prod.swap_prod_mk, Prod.fst_swap, Prod.snd_swap] using h

/-- The actual source anchor and the full original mark move together. -/
def legalPairAnchorClockShift (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) :
    (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) :=
  (p.1 + b 0 p.2.1.1, legalPairMarkClockShift q b p.2)

theorem measurable_legalPairAnchorClockShift (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    Measurable (legalPairAnchorClockShift q b) :=
  (measurable_fst.add ((b 0).continuous.measurable.comp measurable_snd.fst.fst)).prodMk
    ((measurable_legalPairMarkClockShift q b).comp measurable_snd)

/-- The true pair anchor of each actual shifted edge has exactly this
source-clock and full-displacement transformation. -/
theorem physicalPairAnchor_legalClockShiftEdge (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (e : LegalMarkedPhysicalEdge q) :
    physicalPairAnchor (legalClockShiftEdge q b e) =
      legalPairAnchorClockShift q b (physicalPairAnchor e) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · change (e.2.1 + b 1 e.2.2) - (e.1.1 + b 0 e.1.2) =
        (e.2.1 - e.1.1) + b 1 e.2.2 - b 0 e.1.2
      abel

/-- Campbell covariance uses every original edge of the actual pushed
joint scene and retains both original clocks and the entire displacement. -/
theorem physicalScenePairCampbell_clockShift_legalInputLaw (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    physicalScenePairCampbell (legalMarkedInputPairLaw q
      (legalMarkedInputClockShiftLaw q b Q) :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))).map
          (legalPairAnchorClockShift q b) := by
  apply Measure.ext
  intro B hB
  have hpre : MeasurableSet (legalPairAnchorClockShift q b ⁻¹' B) :=
    hB.preimage (measurable_legalPairAnchorClockShift q b)
  rw [Measure.map_apply (measurable_legalPairAnchorClockShift q b) hB]
  simp only [physicalScenePairCampbell, Measure.bind_apply hB
    (Kernel.measurable _).aemeasurable, Measure.bind_apply hpre (Kernel.measurable _).aemeasurable]
  change (∫⁻ scene, physicalScenePairKernel scene B
      ∂((Q : Measure (LegalMarkedOptimalInputScene q)).map
        (legalMarkedInputSceneClockShift q b)).map Prod.fst) =
    ∫⁻ scene, physicalScenePairKernel scene (legalPairAnchorClockShift q b ⁻¹' B)
      ∂(Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst
  rw [lintegral_map (Kernel.measurable_coe _ hB) measurable_fst,
    lintegral_map (Kernel.measurable_coe _ hpre) measurable_fst]
  have hBjoint : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      physicalScenePairKernel s.1 B) := (Kernel.measurable_coe _ hB).comp measurable_fst
  have hchange := lintegral_map (μ := (Q : Measure (LegalMarkedOptimalInputScene q))) hBjoint
    (continuous_legalMarkedInputSceneClockShift q b).measurable
  rw [hchange]
  apply lintegral_congr_ae
  filter_upwards with s
  rw [physicalScenePairKernel_apply, physicalScenePairKernel_apply]
  change (((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map
      (legalClockShiftEdge q b)).map physicalPairAnchor) B =
    ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map physicalPairAnchor)
      (legalPairAnchorClockShift q b ⁻¹' B)
  rw [Measure.map_map measurable_physicalPairAnchor
      (legalClockShiftEdge q b).continuous.measurable,
    Measure.map_apply measurable_physicalPairAnchor hpre,
    Measure.map_apply (measurable_physicalPairAnchor.comp
      (legalClockShiftEdge q b).continuous.measurable) hB]
  congr 1
  ext e
  simp only [mem_preimage, Function.comp_def, physicalPairAnchor_legalClockShiftEdge]

/-- The exact whole Haar-times-mark Campbell product transforms by the
unchanged original Palm mark push, after the actual source skew translation. -/
theorem map_volume_prod_legalPairAnchorClockShift (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (η : Measure (PhysicalPairPalmMark (Fin q))) [SFinite η] :
    ((volume : Measure (Fin q → ℝ)).prod η).map (legalPairAnchorClockShift q b) =
      (volume : Measure (Fin q → ℝ)).prod (η.map (legalPairMarkClockShift q b)) := by
  have hm : Measurable (Prod.map (id : (Fin q → ℝ) → (Fin q → ℝ)) (legalPairMarkClockShift q b)) :=
    measurable_id.prodMap (measurable_legalPairMarkClockShift q b)
  have hfactor : legalPairAnchorClockShift q b =
      Prod.map (id : (Fin q → ℝ) → (Fin q → ℝ)) (legalPairMarkClockShift q b) ∘
        legalPairSourceAnchorClockShift q b := rfl
  rw [hfactor, ← Measure.map_map hm (measurable_legalPairSourceAnchorClockShift q b),
    (measurePreserving_legalPairSourceAnchorClockShift q b η).map_eq]
  calc
    _ = ((volume : Measure (Fin q → ℝ)).map id).prod (η.map (legalPairMarkClockShift q b)) :=
      (Measure.map_prod_map _ _ measurable_id (measurable_legalPairMarkClockShift q b)).symm
    _ = _ := by rw [Measure.map_id]

/-- The actual full source-anchored true Palm is exactly the push of the
original probability Palm by target shift minus source shift. No input-law,
new-Palm, finite second moment, or first-variation premise enters. -/
theorem legalMarkedJointPalm_clockShift_of_weighted_stationary
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    legalMarkedJointPalm q (legalMarkedInputClockShiftLaw q b M.law) =
      (legalMarkedJointPalm q M.law).map (legalPairMarkClockShift q b) := by
  let P := legalMarkedInputPairLaw q M.law
  let η := legalMarkedJointPalm q M.law
  have : IsProbabilityMeasure η := M.palm_probability
  have hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂(P : Measure (CavityLocalScene
        (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) < ∞ := by
    rw [← physicalScenePairCampbell_unitCube]
    rw [← cubePalm_apply (Fin q) _ MeasurableSet.univ]
    change η univ < ∞
    rw [measure_univ]
    norm_num
  have hcamp : physicalScenePairCampbell (P : Measure (CavityLocalScene
      (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod η :=
    physicalScenePairCampbell_eq_volume_prod_cubePalm _
      (measurePreserving_legalMarkedInputPairLaw q M.law M.stationary) hunit
  have hnew : physicalScenePairCampbell (legalMarkedInputPairLaw q
      (legalMarkedInputClockShiftLaw q b M.law) :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod (η.map (legalPairMarkClockShift q b)) := by
    rw [physicalScenePairCampbell_clockShift_legalInputLaw, hcamp,
      map_volume_prod_legalPairAnchorClockShift]
  apply Measure.ext
  intro B hB
  change cubePalm (Fin q) _ B = η.map (legalPairMarkClockShift q b) B
  rw [cubePalm_apply (Fin q) _ hB, hnew, Measure.prod_prod, volume_palmUnitCube, one_mul]

/-- The actual shifted true Palm retains its original unit source intensity. -/
theorem LegalWeightedStationaryPoissonMatching.clockShift_palm_probability
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    IsProbabilityMeasure (legalMarkedJointPalm q (legalMarkedInputClockShiftLaw q b M.law)) := by
  rw [legalMarkedJointPalm_clockShift_of_weighted_stationary M b]
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  exact Measure.isProbabilityMeasure_map (measurable_legalPairMarkClockShift q b).aemeasurable

/-- The actual shifted true Palm has the same unchanged original source clock law. -/
theorem LegalWeightedStationaryPoissonMatching.clockShift_source_clock
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    (legalMarkedJointPalm q (legalMarkedInputClockShiftLaw q b M.law)).map (fun m ↦ m.1.1) = α := by
  rw [legalMarkedJointPalm_clockShift_of_weighted_stationary M b,
    Measure.map_map measurable_fst.fst (measurable_legalPairMarkClockShift q b)]
  simpa only [Function.comp_def, legalPairMarkClockShift] using M.source_clock

/-- The actual shifted true Palm has the same unchanged original target clock law. -/
theorem LegalWeightedStationaryPoissonMatching.clockShift_target_clock
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    (legalMarkedJointPalm q (legalMarkedInputClockShiftLaw q b M.law)).map (fun m ↦ m.1.2) = β := by
  rw [legalMarkedJointPalm_clockShift_of_weighted_stationary M b,
    Measure.map_map measurable_fst.snd (measurable_legalPairMarkClockShift q b)]
  simpa only [Function.comp_def, legalPairMarkClockShift] using M.target_clock

end OTSelector.Reconstruction
