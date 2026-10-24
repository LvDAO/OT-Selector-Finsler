import OTSelector.Reconstruction.OriginalReserveWorkingFullCounts
import OTSelector.Reconstruction.OriginalReserveUnitInputCounts

/-! Genuine FULL total counts coincide with the same original main-plus-reserve count readout. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Literal full-array equality gives the actual real-valued color counts,
with finiteness of each main summand derived from the same full finite array. -/
theorem originalWorkingInput_fullArray_color_counts {q : ℕ}
    (K : Set (Fin q → ℝ)) (main : LegalMarkedOptimalInputScene q)
    (reserve full : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hread : (main.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) + legalInputTwoBlockMeasure q reserve =
        legalInputTwoBlockMeasure q full) (color : Fin 2) :
    ((if color = 0 then full.1.1 else full.2.1 : ℕ) : ℝ) =
      originalScreeningActualColorCount K color main +
        ((if color = 0 then reserve.1.1 else reserve.2.1 : ℕ) : ℝ) := by
  let C : Set (LegalColoredInputPoint q) := univ ×ˢ {color}
  have hm := congrArg (fun ζ : Measure (LegalColoredInputPoint q) ↦ ζ C) hread
  rw [Measure.add_apply] at hm
  have hfin : ((main.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K)) C + legalInputTwoBlockMeasure q reserve C < ∞ := by
    rw [hm]
    exact measure_lt_top _ _
  have hreal := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_add (ENNReal.add_lt_top.mp hfin).1.ne
    (ENNReal.add_lt_top.mp hfin).2.ne] at hreal
  simp only [C, originalFiniteInputArrays_color_mass, ENNReal.toReal_natCast] at hreal
  rw [originalSpatialWindowColorCount_eq_restrict_count K color]
  exact hreal.symm

namespace OriginalReserveFullWorkingInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))} {ρ R : ℝ}
  (X : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R)

/-- The genuine FULL total count equals the actual original main plus both
literal raw reserve prefixes in this same experiment. Hence arbitrary bad-event
weighted count costs use this exact original FULL count, with no independence. -/
theorem ae_fullArray_total_counts :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      (∀ color : Fin 2,
        ((if color = 0 then p.2.1.1 else p.2.2.1 : ℕ) : ℝ) =
          originalScreeningActualColorCount (originalCenteredPhysicalCubeRegion b (2*R)) color p.1.1 +
            ((if color = 0 then p.1.2.2.1.1 else p.1.2.2.2.1 : ℕ) : ℝ)) ∧
      (p.2.1.1 : ℝ) + (p.2.2.1 : ℝ) =
        originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2*R)) p.1.1 +
          ((p.1.2.2.1.1 : ℝ) + (p.1.2.2.2.1 : ℝ)) := by
  filter_upwards [X.ae_full_arrays] with p hp
  have hc (color : Fin 2) := originalWorkingInput_fullArray_color_counts
    (originalCenteredPhysicalCubeRegion b (2*R)) p.1.1
    (originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.1.2.2)
    (originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) p.2) hp color
  refine ⟨hc, ?_⟩
  have hs := hc 0
  have ht := hc 1
  simp only [↓reduceIte, one_ne_zero] at hs ht
  change (p.2.1.1 : ℝ) = originalScreeningActualColorCount
    (originalCenteredPhysicalCubeRegion b (2*R)) 0 p.1.1 + (p.1.2.2.1.1 : ℝ) at hs
  change (p.2.2.1 : ℝ) = originalScreeningActualColorCount
    (originalCenteredPhysicalCubeRegion b (2*R)) 1 p.1.1 + (p.1.2.2.2.1 : ℝ) at ht
  simp only [originalScreeningActualCount]
  linarith only [hs, ht]

end OriginalReserveFullWorkingInputExperiment
end OTSelector.Reconstruction
