import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsSets
import OTSelector.Reconstruction.OriginalMarkedWindowCounts
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockCounts

/-! Original window-plus-surviving-reserve clock laws and their literal observed counts. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The original full input inherits the actual source and target grid cover from its
true Palm clock marginals, on one event for both original colours. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalInputs_clockSlab_cover
    {q : ℕ} {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) (G : OriginalStageClockGrid)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      (∀ᵐ p ∂legalInputColorMeasure q scene.2 0, p.2 ∈ ⋃ i, G.sourceCell i) ∧
      (∀ᵐ p ∂legalInputColorMeasure q scene.2 1, p.2 ∈ ⋃ j, G.targetCell j) := by
  have hmS : MeasurableSet (⋃ i, G.sourceCell i) := MeasurableSet.iUnion (fun _ ↦ measurableSet_Ico)
  have hmT : MeasurableSet (⋃ j, G.targetCell j) := MeasurableSet.iUnion (fun _ ↦ measurableSet_Ioc)
  have hpS : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m.1.1 ∈ ⋃ i, G.sourceCell i :=
    ae_of_ae_map measurable_fst.fst.aemeasurable (by rw [Q.source_clock]; exact hs)
  have hpT : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m.1.2 ∈ ⋃ j, G.targetCell j :=
    ae_of_ae_map measurable_fst.snd.aemeasurable (by rw [Q.target_clock]; exact ht)
  have hpalm : ∀ᵐ m ∂legalMarkedJointPalm q Q.law,
      m.1.1 ∈ ⋃ i, G.sourceCell i ∧ m.1.2 ∈ ⋃ j, G.targetCell j := hpS.and hpT
  have hB : MeasurableSet {m : PhysicalPairPalmMark (Fin q) |
      m.1.1 ∈ ⋃ i, G.sourceCell i ∧ m.1.2 ∈ ⋃ j, G.targetCell j} :=
    (hmS.preimage measurable_fst.fst).inter (hmT.preimage measurable_fst.snd)
  filter_upwards [Q.full_matching,Q.ae_ae_original_pairKernel_of_palm hB hpalm]
    with scene hfull hp
  rw [physicalScenePairKernel_apply] at hp
  have hedge := ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hp
  constructor
  · rw [← hfull.source_marginal]
    exact (ae_map_iff measurable_fst.aemeasurable (hmS.preimage measurable_snd)).mpr
      (hedge.mono fun _ h ↦ h.1)
  · rw [← hfull.target_marginal]
    exact (ae_map_iff measurable_snd.aemeasurable (hmT.preimage measurable_snd)).mpr
      (hedge.mono fun _ h ↦ h.2)

/-- Actual finite original arrays turn the total natural count readout into the true
original window mass for every measurable clock set. -/
theorem originalMainPhysicalBlockCount_mass_of_original_array {q n : ℕ}
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) {C : Set ℝ} (hC : MeasurableSet C)
    (color : Fin 2) (scene : LegalMarkedOptimalInputScene q)
    (x : Fin n → LegalMarkedPhysicalPoint q)
    (hx : (legalInputColorMeasure q scene.2 color).restrict {p | p.1 ∈ K} = ∑ i, Measure.dirac (x i)) :
    ((legalInputColorMeasure q scene.2 color).restrict {p | p.1 ∈ K}).real {p | p.2 ∈ C} =
      (originalMainPhysicalBlockCount K C color scene : ℝ) := by
  classical
  rw [originalMainPhysicalBlockCount_eq_original_array hK hC color scene x hx,hx]
  have hW : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ C} := hC.preimage measurable_snd
  have hm : (∑ i, Measure.dirac (x i)) {p | p.2 ∈ C} =
      ((Finset.univ.filter (fun i ↦ (x i).2 ∈ C)).card : ℝ≥0∞) := by
    simp [Measure.finsetSum_apply,Measure.dirac_apply' _ hW,Set.indicator_apply,Finset.sum_boole]
  rw [measureReal_def,hm]
  simp

/-- The literal clock law of an original spatial window and exactly its surviving
original reserve indices. No new spatial or selected-index law is assigned. -/
def originalWindowReserveClockLaw {q : ℕ} (K : Set (Fin q → ℝ)) (color : Fin 2)
    (scene : LegalMarkedOptimalInputScene q) (reserve : MarkedCloudSpace q ℝ)
    (kept : Finset (Fin reserve.1)) : Measure ℝ :=
  (((legalInputColorMeasure q scene.2 color).restrict {p | p.1 ∈ K}) +
    originalStageRemainingReserveMeasure reserve kept).map Prod.snd

/-- Actual original finite window arrays internally give a finite augmented clock law. -/
theorem originalWindowReserveClockLaw_finite_of_array {q n : ℕ}
    (K : Set (Fin q → ℝ)) (color : Fin 2) (scene : LegalMarkedOptimalInputScene q)
    (reserve : MarkedCloudSpace q ℝ) (kept : Finset (Fin reserve.1))
    (x : Fin n → LegalMarkedPhysicalPoint q)
    (hx : (legalInputColorMeasure q scene.2 color).restrict {p | p.1 ∈ K} = ∑ i, Measure.dirac (x i)) :
    IsFiniteMeasure (originalWindowReserveClockLaw K color scene reserve kept) := by
  have : IsFiniteMeasure ((legalInputColorMeasure q scene.2 color).restrict {p | p.1 ∈ K}) := by
    rw [hx]
    infer_instance
  unfold originalWindowReserveClockLaw
  infer_instance

/-- The augmented law inherits the actual full-input cover and the literal support
of the retained original reserve indices. -/
theorem ae_originalWindowReserveClockLaw_mem {q : ℕ}
    (K : Set (Fin q → ℝ)) (color : Fin 2) (scene : LegalMarkedOptimalInputScene q)
    (reserve : MarkedCloudSpace q ℝ) (kept : Finset (Fin reserve.1))
    {U : Set ℝ} (hU : MeasurableSet U)
    (hmain : ∀ᵐ p ∂legalInputColorMeasure q scene.2 color, p.2 ∈ U)
    (hkept : ∀ i ∈ kept, (reserve.2 i).2 ∈ U) :
    ∀ᵐ c ∂originalWindowReserveClockLaw K color scene reserve kept, c ∈ U := by
  apply (ae_map_iff measurable_snd.aemeasurable hU).mpr
  apply ae_add_measure_iff.mpr
  refine ⟨ae_restrict_of_ae hmain,?_⟩
  apply ae_finsetSum_measure_iff.mpr
  intro i hi
  exact (ae_dirac_iff (hU.preimage measurable_snd)).mpr (hkept i hi)

/-- Measurable clock sets read the same actual window mass and true integer reserve count. -/
theorem originalWindowReserveClockLaw_real {q : ℕ}
    (K : Set (Fin q → ℝ)) (color : Fin 2) (scene : LegalMarkedOptimalInputScene q)
    (reserve : MarkedCloudSpace q ℝ) (kept : Finset (Fin reserve.1))
    [IsFiniteMeasure ((legalInputColorMeasure q scene.2 color).restrict {p | p.1 ∈ K})]
    {C : Set ℝ} (hC : MeasurableSet C) :
    (originalWindowReserveClockLaw K color scene reserve kept).real C =
      ((legalInputColorMeasure q scene.2 color).restrict {p | p.1 ∈ K}).real {p | p.2 ∈ C} +
        (originalStageRemainingReserveClassCount reserve kept C : ℝ) := by
  unfold originalWindowReserveClockLaw
  rw [measureReal_def,Measure.map_apply measurable_snd hC]
  change (((legalInputColorMeasure q scene.2 color).restrict {p | p.1 ∈ K} +
    originalStageRemainingReserveMeasure reserve kept).real {p | p.2 ∈ C}) = _
  rw [measureReal_add_apply,originalStageRemainingReserveMeasure_class_mass reserve kept hC]

end OTSelector.Reconstruction
