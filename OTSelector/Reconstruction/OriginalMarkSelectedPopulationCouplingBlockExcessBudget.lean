import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockMainCountMoment
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockCountMoment
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockSelection
import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawJoinedExperiment

/-! The actual full main-plus-reserve block imbalance is the genuine total
excess deleted by the two original selectors and has a square-root count budget. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}

/-- The finite original-index count and the literal original observed cloud count agree. -/
theorem originalReserveObservedBlockCount_eq_natCount (S : Set ℝ) (z : MarkedCloudSpace q ℝ) :
    originalReserveObservedBlockCount S z = originalReserveBlockCount z.1 (fun i ↦ (z.2 i).2) S := by
  rw [originalReserveBlockCount, originalReserveClassNatIndices_eq_map_fin, Finset.card_map]
  rfl

/-- Absolute full color imbalance in one actual clock block, retaining every
original main input and both independent original reserve prefixes. -/
def originalFullBlockDiscrepancy (K : Set (Fin q → ℝ)) (S T : Set ℝ)
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  |((originalMainPhysicalBlockCount K S 0 p.1 : ℝ) + originalReserveObservedBlockCount S p.2.1) -
    ((originalMainPhysicalBlockCount K T 1 p.1 : ℝ) + originalReserveObservedBlockCount T p.2.2)|

theorem measurable_originalFullBlockDiscrepancy {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Measurable (originalFullBlockDiscrepancy K S T) := by
  have hs : Measurable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (originalMainPhysicalBlockCount K S 0 p.1 : ℝ)) := ((measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
    (measurable_originalMainPhysicalBlockCount hK hS 0)).comp measurable_fst
  have ht : Measurable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (originalMainPhysicalBlockCount K T 1 p.1 : ℝ)) := ((measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
    (measurable_originalMainPhysicalBlockCount hK hT 1)).comp measurable_fst
  have hrs : Measurable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (originalReserveObservedBlockCount S p.2.1 : ℝ)) := ((measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
    (measurable_originalReserveObservedBlockCount hS)).comp measurable_snd.fst
  have hrt : Measurable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (originalReserveObservedBlockCount T p.2.2 : ℝ)) := ((measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
    (measurable_originalReserveObservedBlockCount hT)).comp measurable_snd.snd
  exact ((hs.add hrs).sub (ht.add hrt)).abs

private theorem nat_excess_sum (m n : ℕ) :
    ((m-n : ℕ) : ℝ) + ((n-m : ℕ) : ℝ) = |(m : ℝ)-(n : ℝ)| := by
  rcases le_total m n with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, zero_add, Nat.cast_sub h,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, add_zero, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

/-- The two actual block selectors request exactly this full original color
imbalance. No successful deletion or reserve-capacity assumption is needed. -/
theorem originalReserveBlockExcess_sum_eq_fullDiscrepancy
    (K : Set (Fin q → ℝ)) (S T : Set ℝ)
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :
    (originalReserveBlockExcess K 0 1 S T
      (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) : ℝ) +
    (originalReserveBlockExcess K 1 0 T S
      (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) : ℝ) =
      originalFullBlockDiscrepancy K S T p := by
  simpa only [originalReserveBlockExcess, originalReserveExcessInputAux,
    originalSourceReserveExperimentSplice, originalTargetReserveExperimentSplice,
    originalFullBlockDiscrepancy, originalReserveObservedBlockCount_eq_natCount, Nat.cast_add] using
    nat_excess_sum
      (originalMainPhysicalBlockCount K S 0 p.1 + originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2) S)
      (originalMainPhysicalBlockCount K T 1 p.1 + originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2) T)

variable {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The same actual joint experiment supplies both full block counts. Their
imbalance is bounded by the internally proved main and reserve fluctuations. -/
theorem LegalWeightedStationaryPoissonMatching.originalFullBlockDiscrepancy_integrable_and_integral_le
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hbal : α S = β T) :
    Integrable (originalFullBlockDiscrepancy K S T) (originalMainReserveExperimentLaw Q rate) ∧
    (∫ p, originalFullBlockDiscrepancy K S T p ∂originalMainReserveExperimentLaw Q rate) ≤
      Real.sqrt (2 * volume.real K * α.real S) + Real.sqrt (2 * (rate : ℝ) * α.real S) := by
  let main := fun scene ↦ |(originalMainPhysicalBlockCount K S 0 scene : ℝ) -
    (originalMainPhysicalBlockCount K T 1 scene : ℝ)|
  let reserve := fun z : TwoMarkedCloudSpace q ℝ ℝ ↦
    |(originalReserveObservedBlockCount S z.1 : ℝ) - (originalReserveObservedBlockCount T z.2 : ℝ)|
  have hm := Q.originalMainPhysicalBlockCount_abs_sub_integrable_and_integral_le hK hS hT hbal
  have hr := originalReserveObservedBlockCount_abs_sub_integrable_and_integral_le (q := q) α β rate hS hT hbal
  have hmi : Integrable (fun p ↦ main p.1) (originalMainReserveExperimentLaw Q rate) :=
    hm.1.comp_fst (twoMarkedCloudLaw q ℝ ℝ α β rate)
  have hri : Integrable (fun p ↦ reserve p.2) (originalMainReserveExperimentLaw Q rate) :=
    hr.1.comp_snd (Q.law : Measure (LegalMarkedOptimalInputScene q))
  have hup : Integrable (fun p ↦ main p.1 + reserve p.2) (originalMainReserveExperimentLaw Q rate) :=
    hmi.add hri
  have hpoint (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :
      originalFullBlockDiscrepancy K S T p ≤ main p.1 + reserve p.2 := by
    unfold originalFullBlockDiscrepancy main reserve
    calc
      _ = |((originalMainPhysicalBlockCount K S 0 p.1 : ℝ) - originalMainPhysicalBlockCount K T 1 p.1) +
        ((originalReserveObservedBlockCount S p.2.1 : ℝ) - originalReserveObservedBlockCount T p.2.2)| := by
          congr 1
          ring
      _ ≤ _ := abs_add_le _ _
  have hI : Integrable (originalFullBlockDiscrepancy K S T) (originalMainReserveExperimentLaw Q rate) :=
    hup.mono' (measurable_originalFullBlockDiscrepancy hK.measurableSet hS hT).aestronglyMeasurable
      (.of_forall fun p ↦ by
        change |originalFullBlockDiscrepancy K S T p| ≤ main p.1 + reserve p.2
        rw [abs_of_nonneg (show 0 ≤ originalFullBlockDiscrepancy K S T p from abs_nonneg _)]
        exact hpoint p)
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ p, main p.1 + reserve p.2 ∂originalMainReserveExperimentLaw Q rate :=
      integral_mono hI hup hpoint
    _ = (∫ scene, main scene ∂(Q.law : Measure _)) +
        ∫ z, reserve z ∂twoMarkedCloudLaw q ℝ ℝ α β rate := by
      rw [integral_add hmi hri]
      simp only [originalMainReserveExperimentLaw, integral_fun_fst, integral_fun_snd,
        measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ _ := add_le_add hm.2 hr.2

end OTSelector.Reconstruction
