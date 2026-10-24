import OTSelector.Reconstruction.OriginalReserveFullWorkingInputExperiment
import OTSelector.Reconstruction.OriginalReserveUnitInputClockBlockCounts

/-! Literal FULL label cardinalities equal the genuine original main and reserve class counts. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The actual full-array identity internally gives every Borel clock-class
Nat cardinality as original-main count plus original-reserve count. -/
theorem originalWorkingInput_fullArray_clockBlock_counts {q : ℕ}
    (K : Set (Fin q → ℝ)) (main : LegalMarkedOptimalInputScene q)
    (reserve full : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hread : (main.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) + legalInputTwoBlockMeasure q reserve =
        legalInputTwoBlockMeasure q full)
    {C : Set ℝ} (hC : MeasurableSet C) (color : Fin 2) :
    (if color = 0 then blockSetCount (univ ×ˢ C) full.1 else
      blockSetCount (univ ×ˢ C) full.2) =
      originalMainPhysicalBlockCount K C color main +
        (if color = 0 then blockSetCount (univ ×ˢ C) reserve.1 else
          blockSetCount (univ ×ˢ C) reserve.2) := by
  let U : Set (LegalColoredInputPoint q) := (univ ×ˢ C) ×ˢ {color}
  have hm := congrArg (fun ζ : Measure (LegalColoredInputPoint q) ↦ ζ U) hread
  rw [Measure.add_apply] at hm
  have hfin : ((main.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K)) U + legalInputTwoBlockMeasure q reserve U < ∞ := by
    rw [hm]
    exact measure_lt_top _ _
  have hreal := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_add (ENNReal.add_lt_top.mp hfin).1.ne
    (ENNReal.add_lt_top.mp hfin).2.ne] at hreal
  simp only [U, originalFiniteInputArrays_color_block_mass _ hC,
    ENNReal.toReal_natCast] at hreal
  have hf := congrArg Nat.floor hreal
  rw [Nat.floor_add_natCast ENNReal.toReal_nonneg, Nat.floor_natCast] at hf
  rw [originalMainPhysicalBlockCount_eq_restrict K hC]
  exact hf.symm

namespace OriginalReserveFullWorkingInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))} {ρ R : ℝ}
  (X : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R)

/-- Each literal FULL label filter in the same working experiment has exactly
the actual original-main clock-class count plus the raw original-reserve count.
No new labels, balancing or count identity is an input. -/
theorem ae_fullArray_clockBlock_counts {C : Set ℝ} (hC : MeasurableSet C) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      ∀ color : Fin 2,
      (if color = 0 then
        (Finset.univ.filter (fun i : Fin p.2.1.1 ↦
          ((originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.2).1.2 i).2 ∈ C)).card
      else
        (Finset.univ.filter (fun j : Fin p.2.2.1 ↦
          ((originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.2).2.2 j).2 ∈ C)).card) =
      originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2*R)) C color p.1.1 +
        (if color = 0 then originalReserveBlockCount p.1.2.2.1.1
          (fun i ↦ (p.1.2.2.1.2 i).2) C else
          originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C) := by
  filter_upwards [X.ae_full_arrays] with p hp
  intro color
  have hc := originalWorkingInput_fullArray_clockBlock_counts
    (originalCenteredPhysicalCubeRegion b (2*R)) p.1.1
    (originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.1.2.2)
    (originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.2) hp hC color
  rw [originalMappedReserveCloudArrays_clockBlockCount _ p.1.2.2 C color] at hc
  simpa only [blockSetCount, mem_prod, mem_univ, true_and,
    originalMappedReserveCloudArrays, originalMappedReserveTwoCloud,
    originalMappedReserveCloud, originalPhysicalReserveCloudArrays, cloudEncode,
    mapBlockData, Prod.map_apply, id_eq] using hc

end OriginalReserveFullWorkingInputExperiment
end OTSelector.Reconstruction
