import OTSelector.Reconstruction.OriginalStageResidualDensityReflectedMass

/-! Literal surviving original reserve indices, class counts, and exact prefix increments. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The unchanged reserve observations at precisely their surviving original indices. -/
def originalStageRemainingReserveMeasure {q : ℕ} (z : MarkedCloudSpace q ℝ)
    (kept : Finset (Fin z.1)) : Measure (LegalMarkedPhysicalPoint q) :=
  ∑ i ∈ kept, Measure.dirac (z.2 i)

instance originalStageRemainingReserveMeasure_finite {q : ℕ} (z : MarkedCloudSpace q ℝ)
    (kept : Finset (Fin z.1)) : IsFiniteMeasure (originalStageRemainingReserveMeasure z kept) := by
  unfold originalStageRemainingReserveMeasure
  infer_instance

/-- Count the original surviving reserve indices in the actual scalar mark class. -/
def originalStageRemainingReserveClassCount {q : ℕ} (z : MarkedCloudSpace q ℝ)
    (kept : Finset (Fin z.1)) (C : Set ℝ) : ℕ :=
  (kept.filter (fun i : Fin z.1 ↦ (z.2 i).2 ∈ C)).card

/-- The actual surviving point measure has exactly its integer original-index class count. -/
theorem originalStageRemainingReserveMeasure_class_mass {q : ℕ} (z : MarkedCloudSpace q ℝ)
    (kept : Finset (Fin z.1)) {C : Set ℝ} (hC : MeasurableSet C) :
    (originalStageRemainingReserveMeasure z kept).real {p | p.2 ∈ C} =
      (originalStageRemainingReserveClassCount z kept C : ℝ) := by
  have hset : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ C} :=
    hC.preimage measurable_snd
  have he : originalStageRemainingReserveMeasure z kept {p | p.2 ∈ C} =
      (originalStageRemainingReserveClassCount z kept C : ℝ≥0∞) := by
    simp [originalStageRemainingReserveMeasure, Measure.finsetSum_apply,
      Measure.dirac_apply' _ hset, originalStageRemainingReserveClassCount, Set.indicator_apply]
  exact congrArg ENNReal.toReal he

/-- Source prefix and target prefix increments are exactly their true half-open slab counts. -/
theorem originalStageClockMeasure_prefix_increments {q : ℕ}
    (π : Measure (LegalMarkedPhysicalPoint q)) [IsFiniteMeasure π] {s t : ℝ} (hst : s ≤ t) :
    π.real {p | p.2 < t} - π.real {p | p.2 < s} = π.real {p | p.2 ∈ Ico s t} ∧
    π.real {p | p.2 ≤ t} - π.real {p | p.2 ≤ s} = π.real {p | p.2 ∈ Ioc s t} := by
  constructor
  · have hsub : {p : LegalMarkedPhysicalPoint q | p.2 < s} ⊆ {p | p.2 < t} :=
      fun p hp ↦ hp.trans_le hst
    have he : {p : LegalMarkedPhysicalPoint q | p.2 < t} \ {p | p.2 < s} =
        {p | p.2 ∈ Ico s t} := by
      ext p
      simp only [mem_sdiff, mem_ofPred_eq, mem_Ico, not_lt]
      exact and_comm
    have hm := measureReal_sdiff (μ := π) hsub (measurableSet_lt measurable_snd measurable_const)
    rw [he] at hm
    exact hm.symm
  · have hsub : {p : LegalMarkedPhysicalPoint q | p.2 ≤ s} ⊆ {p | p.2 ≤ t} :=
      fun p hp ↦ hp.trans hst
    have he : {p : LegalMarkedPhysicalPoint q | p.2 ≤ t} \ {p | p.2 ≤ s} =
        {p | p.2 ∈ Ioc s t} := by
      ext p
      simp only [mem_sdiff, mem_ofPred_eq, mem_Ioc, not_le]
      exact and_comm
    have hm := measureReal_sdiff (μ := π) hsub (measurableSet_le measurable_snd measurable_const)
    rw [he] at hm
    exact hm.symm

/-- The signed surviving reserve prefix is read from those same original index sets. -/
def originalStageRemainingReservePrefix {q : ℕ} (source target : MarkedCloudSpace q ℝ)
    (sourceKept : Finset (Fin source.1)) (targetKept : Finset (Fin target.1)) (c : ℝ) : ℝ :=
  (originalStageRemainingReserveClassCount source sourceKept (Iio c) : ℝ) -
    (originalStageRemainingReserveClassCount target targetKept (Iic c) : ℝ)

/-- Actual remaining reserve prefixes telescope to actual class counts, including clock ties. -/
theorem originalStageRemainingReservePrefix_increment {q : ℕ}
    (source target : MarkedCloudSpace q ℝ) (sourceKept : Finset (Fin source.1))
    (targetKept : Finset (Fin target.1)) {s t : ℝ} (hst : s ≤ t) :
    originalStageRemainingReservePrefix source target sourceKept targetKept t -
      originalStageRemainingReservePrefix source target sourceKept targetKept s =
      (originalStageRemainingReserveClassCount source sourceKept (Ico s t) : ℝ) -
      (originalStageRemainingReserveClassCount target targetKept (Ioc s t) : ℝ) := by
  have hs := (originalStageClockMeasure_prefix_increments
    (originalStageRemainingReserveMeasure source sourceKept) hst).1
  have ht := (originalStageClockMeasure_prefix_increments
    (originalStageRemainingReserveMeasure target targetKept) hst).2
  change (originalStageRemainingReserveMeasure source sourceKept).real
      {p | p.2 ∈ Iio t} - (originalStageRemainingReserveMeasure source sourceKept).real
      {p | p.2 ∈ Iio s} = _ at hs
  change (originalStageRemainingReserveMeasure target targetKept).real
      {p | p.2 ∈ Iic t} - (originalStageRemainingReserveMeasure target targetKept).real
      {p | p.2 ∈ Iic s} = _ at ht
  simp only [originalStageRemainingReserveMeasure_class_mass source sourceKept measurableSet_Iio,
    originalStageRemainingReserveMeasure_class_mass source sourceKept measurableSet_Ico] at hs
  simp only [originalStageRemainingReserveMeasure_class_mass target targetKept measurableSet_Iic,
    originalStageRemainingReserveMeasure_class_mass target targetKept measurableSet_Ioc] at ht
  unfold originalStageRemainingReservePrefix
  linarith

end OTSelector.Reconstruction
