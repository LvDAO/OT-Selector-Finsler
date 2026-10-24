import OTSelector.Reconstruction.OriginalReserveFullUnitInputExperiment
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockCounts

/-! Clock-block counts retain the same unit, main, reserve and full original-array identities. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- The actual clock-block count evaluates this same window restriction. -/
theorem originalMainPhysicalBlockCount_eq_restrict {q : ℕ} (K : Set (Fin q → ℝ))
    {C : Set ℝ} (hC : MeasurableSet C) (color : Fin 2) (scene : LegalMarkedOptimalInputScene q) :
    originalMainPhysicalBlockCount K C color scene =
      ⌊(((scene.2 : Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K))
        (((univ : Set (Fin q → ℝ)) ×ˢ C) ×ˢ {color})).toReal⌋₊ := by
  rw [originalMainPhysicalBlockCount,
    Measure.restrict_apply ((MeasurableSet.univ.prod hC).prod (measurableSet_singleton color))]
  congr 3
  ext p
  simp only [mem_prod, mem_univ, true_and, mem_singleton_iff, mem_inter_iff,
    mem_preimage, Function.comp_apply]
  tauto

/-- A literal finite array identifies the mass of every original clock block. -/
theorem originalFiniteInputArrays_color_block_mass {q : ℕ}
    (arrays : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    {C : Set ℝ} (hC : MeasurableSet C) (color : Fin 2) :
    legalInputTwoBlockMeasure q arrays (((univ : Set (Fin q → ℝ)) ×ˢ C) ×ˢ {color}) =
      ((if color = 0 then blockSetCount (univ ×ˢ C) arrays.1 else
        blockSetCount (univ ×ˢ C) arrays.2 : ℕ) : ℝ≥0∞) := by
  have h : color = 0 ∨ color = 1 := by omega
  rcases h with rfl | rfl
  · rw [legalInputTwoBlockMeasure_sourceCount q (MeasurableSet.univ.prod hC)]
    rfl
  · rw [legalInputTwoBlockMeasure_targetCount q (MeasurableSet.univ.prod hC)]
    rfl

/-- Full-array identity internally gives all actual original clock-block counts. -/
theorem originalInputWindow_clockBlockCounts_eq_fullArrays {q : ℕ}
    (K : Set (Fin q → ℝ)) (scene : LegalMarkedOptimalInputScene q)
    (full : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hfull : (scene.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) = legalInputTwoBlockMeasure q full)
    {C : Set ℝ} (hC : MeasurableSet C) (color : Fin 2) :
    originalMainPhysicalBlockCount K C color scene =
      if color = 0 then blockSetCount (univ ×ˢ C) full.1 else blockSetCount (univ ×ˢ C) full.2 := by
  rw [originalMainPhysicalBlockCount_eq_restrict K hC, hfull,
    originalFiniteInputArrays_color_block_mass full hC, ENNReal.toReal_natCast, Nat.floor_natCast]

/-- Actual unit/main decomposition gives the true block count sum. Finiteness
comes from the literal full array, including coincident original observations. -/
theorem originalUnitInput_clockBlockCounts_eq_main_add_reserve {q : ℕ}
    (K : Set (Fin q → ℝ)) (unit main : LegalMarkedOptimalInputScene q)
    (reserve full : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hfull : (unit.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) = legalInputTwoBlockMeasure q full)
    (hdecomp : (unit.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K) =
      (main.2 : Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K) +
        legalInputTwoBlockMeasure q reserve)
    {C : Set ℝ} (hC : MeasurableSet C) (color : Fin 2) :
    originalMainPhysicalBlockCount K C color unit =
      originalMainPhysicalBlockCount K C color main +
        (if color = 0 then blockSetCount (univ ×ˢ C) reserve.1 else blockSetCount (univ ×ˢ C) reserve.2) := by
  let U : Set (LegalColoredInputPoint q) := (univ ×ˢ C) ×ˢ {color}
  have hmass := congrArg (fun ζ : Measure (LegalColoredInputPoint q) ↦ ζ U) hdecomp
  rw [Measure.add_apply] at hmass
  have hfinite : ((main.2 : Measure (LegalColoredInputPoint q)).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' K)) U + legalInputTwoBlockMeasure q reserve U < ∞ := by
    rw [← hmass, hfull]
    exact measure_lt_top _ _
  have hm := (ENNReal.add_lt_top.mp hfinite).1.ne
  have hr := (ENNReal.add_lt_top.mp hfinite).2.ne
  rw [originalMainPhysicalBlockCount_eq_restrict K hC,
    originalMainPhysicalBlockCount_eq_restrict K hC]
  change ⌊(((unit.2 : Measure (LegalColoredInputPoint q)).restrict
    ((Prod.fst ∘ Prod.fst) ⁻¹' K)) U).toReal⌋₊ = _
  rw [hmass, ENNReal.toReal_add hm hr]
  simp only [U, originalFiniteInputArrays_color_block_mass reserve hC, ENNReal.toReal_natCast]
  exact Nat.floor_add_natCast ENNReal.toReal_nonneg _

/-- Physical placement preserves every original index and its clock-block count. -/
theorem originalMappedReserveCloudArrays_clockBlockCount {q : ℕ}
    (F : (Fin q → ℝ) → (Fin q → ℝ)) (cloud : TwoMarkedCloudSpace q ℝ ℝ)
    (C : Set ℝ) (color : Fin 2) :
    (if color = 0 then blockSetCount (univ ×ˢ C) (originalMappedReserveCloudArrays q F cloud).1 else
      blockSetCount (univ ×ˢ C) (originalMappedReserveCloudArrays q F cloud).2) =
    if color = 0 then originalReserveBlockCount cloud.1.1 (fun i ↦ (cloud.1.2 i).2) C else
      originalReserveBlockCount cloud.2.1 (fun i ↦ (cloud.2.2 i).2) C := by
  have h : color = 0 ∨ color = 1 := by omega
  rcases h with rfl | rfl <;>
    simp [blockSetCount, originalMappedReserveCloudArrays, originalMappedReserveTwoCloud,
      originalMappedReserveCloud, originalPhysicalReserveCloudArrays, cloudEncode,
      originalReserveBlockCount, originalReserveClassNatIndices_eq_map_fin]

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- Every proved base-experiment event survives the entire full-array lift. -/
theorem ae_of_base {P : OriginalReserveUnitExperimentSpace q → Prop}
    (h : ∀ᵐ p ∂(X.baseLaw : Measure (OriginalReserveUnitExperimentSpace q)), P p) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)), P p.1 := by
  have h' : ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      Prod.fst, P p := by
    rw [X.fullLaw_fst]
    exact h
  exact ae_of_ae_map measurable_fst.aemeasurable h'

/-- In the same full joining every actual clock-block count equals the literal
full original-array count and the actual main plus unchanged reserve counts. -/
theorem ae_clockBlock_counts {C : Set ℝ} (hC : MeasurableSet C) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      ∀ color : Fin 2,
      originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) C color
        (originalReserveUnitInputReadout q θ hθ hθ1 p.1) =
        (if color = 0 then originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2) C else
          originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2) C) ∧
      originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) C color
        (originalReserveUnitInputReadout q θ hθ hθ1 p.1) =
        originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) C color
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1 +
        (if color = 0 then originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) C else
          originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C) := by
  filter_upwards [X.ae_full_input, X.ae_of_base X.ae_base_inputs] with p hfull hbase
  intro color
  constructor
  · rw [originalInputWindow_clockBlockCounts_eq_fullArrays _ _ _ hfull hC color,
      originalMappedReserveCloudArrays_clockBlockCount]
  · rw [originalUnitInput_clockBlockCounts_eq_main_add_reserve _ _ _ _ _ hfull hbase.2 hC color,
      originalMappedReserveCloudArrays_clockBlockCount]

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
