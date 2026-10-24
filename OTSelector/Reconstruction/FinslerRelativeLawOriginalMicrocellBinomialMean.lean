import OTSelector.Reconstruction.FinslerRelativeLawOriginalMicrocellBinomialLaw
import OTSelector.Reconstruction.FinslerRelativeLawOriginalAffineRawValue
import OTSelector.Reconstruction.FinslerRelativeLawActualOriginalCoordinateClassPrefix
import OTSelector.Reconstruction.FinslerConcreteUpperClassBinomialShape

/-! Original true-coordinate Haar/class means equal their literal binomial shape means. -/
open Set Function MeasureTheory ProbabilityTheory BoxIntegral
open scoped Topology ENNReal NNReal BigOperators unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- The actual positive original subcell mean, with its full physical
coordinates and binomial retained count, is exactly the affine binomial shape
mean. Integrability transfers both ways; no endpoint resampling is involved. -/
theorem exists_original_microcell_binomial_mean_laws
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (classMass : ℝ≥0) (s : Set E) (hs : MeasurableSet s)
        (n : ℕ) [NeZero n] (ν : Fin q → ℤ) (N : ℕ)
        (hmass : μ (s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) ≠ 0)
        (hbox : (c * classMass) * ((n : ℝ≥0)⁻¹) ^ q ≤ 1)
        (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
        (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
        (source : A → ℝ) (target : B → ℝ), Measurable source → Measurable target →
      ∀ (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ),
      Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)) →
      Measurable (Function.uncurry probe) → ∀ tilt : ℝ,
      let K := s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))
      let _inst := normalized_original_unitPartitionCell_probability μ e n ν
        (hs.inter ((unitPartition.box n ν).measurableSet_coe.preimage e.continuous.measurable))
        inter_subset_right hmass
      let p : unitInterval := ⟨((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0),
        NNReal.coe_nonneg _, (by exact_mod_cast hbox)⟩
      let originalLaw := (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod α)
        (binomWeight N (μ K * (classMass : ℝ≥0∞)).toNNReal)).prod
          (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod β)
            (binomWeight N (μ K * (classMass : ℝ≥0∞)).toNNReal))
      let raw := fun d : BlockData (E × A) × BlockData (E × B) ↦ unclampedBlockLegalTilted q source target N kin probe tilt
        (mapBlockData (Prod.map e id) d.1) (mapBlockData (Prod.map e id) d.2)
      let shape := originalMicrocellShape e n ν s
      (Integrable raw originalLaw ↔ Integrable
        (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦ unclampedBlockLegalTilted q source target N kin probe tilt
          (mapBlockData (affineMarkedPoint (fun l ↦ (ν l : ℝ) / n) ((n : ℝ≥0)⁻¹)) d.1)
          (mapBlockData (affineMarkedPoint (fun l ↦ (ν l : ℝ) / n) ((n : ℝ≥0)⁻¹)) d.2))
        ((binomialShapeBlockLaw q α N p shape).prod (binomialShapeBlockLaw q β N p shape))) ∧
      (∫ d, raw d ∂originalLaw) = affineClassBinomialShapeExpectation source target α β N p
        ((n : ℝ≥0)⁻¹) (fun l ↦ (ν l : ℝ) / n) shape kin probe tilt := by
  obtain ⟨c, hc, hlaws⟩ := exists_original_microcell_intensity_laws μ e
  refine ⟨c, hc, ?_⟩
  intro classMass s hs n _ ν N hmass hbox A B _ _ α _ β _ source target hsource htarget
    kin probe hk hp tilt
  letI : Nonempty A := nonempty_of_isProbabilityMeasure α
  letI : Nonempty B := nonempty_of_isProbabilityMeasure β
  let K := s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))
  letI := normalized_original_unitPartitionCell_probability μ e n ν
    (hs.inter ((unitPartition.box n ν).measurableSet_coe.preimage e.continuous.measurable))
    inter_subset_right hmass
  let p : unitInterval := ⟨((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0),
    NNReal.coe_nonneg _, (by exact_mod_cast hbox)⟩
  let originalS : Measure (BlockData (E × A)) := blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod α)
    (binomWeight N (μ K * (classMass : ℝ≥0∞)).toNNReal)
  let originalT : Measure (BlockData (E × B)) := blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod β)
    (binomWeight N (μ K * (classMass : ℝ≥0∞)).toNNReal)
  letI : SFinite originalS := sfinite_original_binomial_blockDataLaw _ _ _
  letI : SFinite originalT := sfinite_original_binomial_blockDataLaw _ _ _
  let origin : Fin q → ℝ := fun l ↦ (ν l : ℝ) / n
  let side : ℝ≥0 := (n : ℝ≥0)⁻¹
  have hside : 0 < side := inv_pos.mpr (by exact_mod_cast n.pos_of_neZero)
  let obsS := mapBlockData (Prod.map (affineHaarCubeCoord e origin side) (id : A → A))
  let obsT := mapBlockData (Prod.map (affineHaarCubeCoord e origin side) (id : B → B))
  have hmS : Measurable obsS := measurable_mapBlockData
    ((measurable_affineHaarCubeCoord e origin side).prodMap measurable_id)
  have hmT : Measurable obsT := measurable_mapBlockData
    ((measurable_affineHaarCubeCoord e origin side).prodMap measurable_id)
  let shape := originalMicrocellShape e n ν s
  have hcount : (μ K * (classMass : ℝ≥0∞)).toNNReal =
      ((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q) *
        restrictionWeight (cubeMeasure (Fin q) 1) shape := by
    rw [(hlaws n ν).2 classMass s hs, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
    rfl
  have hmapS : originalS.map obsS = binomialShapeBlockLaw q α N p shape := by
    have h := original_microcell_blockDataLaw_map μ e n ν hs hmass α
      (binomWeight N (μ K * (classMass : ℝ≥0∞)).toNNReal)
    dsimp only at h
    dsimp only [originalS, obsS, origin, side]
    rw [hcount] at h ⊢
    simpa only [binomialShapeBlockLaw, p, Real.toNNReal_coe] using h
  have hmapT : originalT.map obsT = binomialShapeBlockLaw q β N p shape := by
    have h := original_microcell_blockDataLaw_map μ e n ν hs hmass β
      (binomWeight N (μ K * (classMass : ℝ≥0∞)).toNNReal)
    dsimp only at h
    dsimp only [originalT, obsT, origin, side]
    rw [hcount] at h ⊢
    simpa only [binomialShapeBlockLaw, p, Real.toNNReal_coe] using h
  have hmap : (originalS.prod originalT).map (Prod.map obsS obsT) =
      (binomialShapeBlockLaw q α N p shape).prod (binomialShapeBlockLaw q β N p shape) := by
    rw [← Measure.map_prod_map _ _ hmS hmT, hmapS, hmapT]
  let value := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
    unclampedBlockLegalTilted q source target N kin probe tilt
      (mapBlockData (affineMarkedPoint origin side) d.1) (mapBlockData (affineMarkedPoint origin side) d.2)
  have hvalue : Measurable value := measurable_unclampedBlockLegalTilted_affine
    q hsource htarget (N : ℝ) hk hp origin side tilt
  have hraw : (fun d : BlockData (E × A) × BlockData (E × B) ↦
      unclampedBlockLegalTilted q source target N kin probe tilt
        (mapBlockData (Prod.map e id) d.1) (mapBlockData (Prod.map e id) d.2)) =
      value ∘ Prod.map obsS obsT := by
    funext d
    rcases d with ⟨dS, dT⟩
    dsimp only [Function.comp_def, value, Prod.map_apply, obsS, obsT]
    rw [mapBlockData_affineHaarCubeCoord_restore e origin hside,
      mapBlockData_affineHaarCubeCoord_restore e origin hside]
  dsimp only
  rw [hraw]
  constructor
  · have h := integrable_map_measure (μ := originalS.prod originalT)
      hvalue.aestronglyMeasurable (hmS.prodMap hmT).aemeasurable
    rw [hmap] at h
    exact h.symm
  · have h := integral_map (μ := originalS.prod originalT)
      (hmS.prodMap hmT).aemeasurable hvalue.aestronglyMeasurable
    rw [hmap] at h
    exact h.symm

end OTSelector.Reconstruction
