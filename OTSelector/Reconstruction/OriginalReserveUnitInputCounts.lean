import OTSelector.Reconstruction.OriginalReserveUnitInputExperiment
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCount
import OTSelector.Reconstruction.OriginalLegalWeightedReserveClockBudget

/-! Actual global, main and reserve counts are read from the same original finite-window point measures. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The actual whole-color count is evaluation of the same physical-window input restriction. -/
theorem originalSpatialWindowColorCount_eq_restrict_count {q : ℕ}
    (K : Set (Fin q → ℝ)) (c : Fin 2) (scene : LegalMarkedOptimalInputScene q) :
    originalScreeningActualColorCount K c scene =
      (((scene.2 : Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K))
        ((univ : Set (LegalMarkedPhysicalPoint q)) ×ˢ {c})).toReal := by
  rw [originalScreeningActualColorCount,
    Measure.restrict_apply (MeasurableSet.univ.prod (measurableSet_singleton c))]
  congr 2
  ext p
  simp only [mem_prod, mem_univ, true_and, mem_singleton_iff, mem_inter_iff,
    mem_preimage, Function.comp_apply]
  tauto

/-- Every finite original array retains its literal color count, including duplicates. -/
theorem originalFiniteInputArrays_color_mass {q : ℕ}
    (arrays : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (c : Fin 2) :
    legalInputTwoBlockMeasure q arrays ((univ : Set (LegalMarkedPhysicalPoint q)) ×ˢ {c}) =
      ((if c = 0 then arrays.1.1 else arrays.2.1 : ℕ) : ℝ≥0∞) := by
  have h : c = 0 ∨ c = 1 := by omega
  rcases h with rfl | rfl
  · rw [legalInputTwoBlockMeasure_sourceCount q MeasurableSet.univ]
    simp [blockSetCount]
  · rw [legalInputTwoBlockMeasure_targetCount q MeasurableSet.univ]
    simp [blockSetCount]

/-- A literal full-array input identity identifies the actual global color
counts and total count in that same experiment. -/
theorem originalInputWindow_counts_eq_fullArrays {q : ℕ}
    (K : Set (Fin q → ℝ)) (scene : LegalMarkedOptimalInputScene q)
    (full : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hfull : (scene.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) = legalInputTwoBlockMeasure q full) :
    (∀ c : Fin 2, originalScreeningActualColorCount K c scene =
      ((if c = 0 then full.1.1 else full.2.1 : ℕ) : ℝ)) ∧
    originalScreeningActualCount K scene = (full.1.1 : ℝ) + (full.2.1 : ℝ) := by
  have hc (c : Fin 2) : originalScreeningActualColorCount K c scene =
      ((if c = 0 then full.1.1 else full.2.1 : ℕ) : ℝ) := by
    rw [originalSpatialWindowColorCount_eq_restrict_count, hfull,
      originalFiniteInputArrays_color_mass, ENNReal.toReal_natCast]
  refine ⟨hc, ?_⟩
  simp only [originalScreeningActualCount, hc, ↓reduceIte, one_ne_zero]

/-- Finite full arrays make all actual main and reserve count summands finite;
the actual global counts therefore equal main counts plus literal reserve counts,
with their original dependence on every bad-cut event retained. -/
theorem originalUnitInput_counts_eq_main_add_reserve {q : ℕ}
    (K : Set (Fin q → ℝ)) (unit main : LegalMarkedOptimalInputScene q)
    (reserve full : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hfull : (unit.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) = legalInputTwoBlockMeasure q full)
    (hdecomp : (unit.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) =
      (main.2 : Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K) +
        legalInputTwoBlockMeasure q reserve) :
    (∀ c : Fin 2, originalScreeningActualColorCount K c unit =
      originalScreeningActualColorCount K c main +
        ((if c = 0 then reserve.1.1 else reserve.2.1 : ℕ) : ℝ)) ∧
    originalScreeningActualCount K unit = originalScreeningActualCount K main +
      ((reserve.1.1 : ℝ) + (reserve.2.1 : ℝ)) := by
  have hc (c : Fin 2) : originalScreeningActualColorCount K c unit =
      originalScreeningActualColorCount K c main +
        ((if c = 0 then reserve.1.1 else reserve.2.1 : ℕ) : ℝ) := by
    let C : Set (LegalColoredInputPoint q) := univ ×ˢ {c}
    have hmass := congrArg (fun μ : Measure (LegalColoredInputPoint q) ↦ μ C) hdecomp
    rw [Measure.add_apply] at hmass
    have hfinite : ((main.2 : Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' K)) C + legalInputTwoBlockMeasure q reserve C < ∞ := by
      rw [← hmass, hfull]
      exact measure_lt_top _ _
    have hm : (((main.2 : Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' K)) C) ≠ ∞ := (ENNReal.add_lt_top.mp hfinite).1.ne
    have hr : legalInputTwoBlockMeasure q reserve C ≠ ∞ :=
      (ENNReal.add_lt_top.mp hfinite).2.ne
    rw [originalSpatialWindowColorCount_eq_restrict_count,
      originalSpatialWindowColorCount_eq_restrict_count]
    change (((unit.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K)) C).toReal = _
    rw [hmass, ENNReal.toReal_add hm hr]
    simp only [C, originalFiniteInputArrays_color_mass, ENNReal.toReal_natCast]
  refine ⟨hc, ?_⟩
  simp only [originalScreeningActualCount, hc, ↓reduceIte, one_ne_zero]
  ring

end OTSelector.Reconstruction
