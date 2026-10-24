import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonBlocks
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingCubeNormalization
import OTSelector.Probability.MarkedShapeLaw

/-! The actual normalized uniform hole law and its unchanged original finite Poisson observations. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Closed-cube representation of the actual normalized original spatial restriction. -/
def originalShapeHolePoissonSpatialLaw (q : ℕ) (H : Set (Fin q → ℝ)) : Measure (DyadicUnitCube q) :=
  (restrictedPointLaw (cubeMeasure (Fin q) 1) H).map originalUnitCubeNormalization

instance originalShapeHolePoissonSpatialLaw_probability (q : ℕ) (H : Set (Fin q → ℝ)) :
    IsProbabilityMeasure (originalShapeHolePoissonSpatialLaw q H) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  exact Measure.isProbabilityMeasure_map measurable_originalUnitCubeNormalization.aemeasurable

/-- Coordinate readout recovers the actual conditional spatial probability,
including a null hole whose fallback spatial law is never used by a positive count. -/
theorem originalShapeHolePoissonSpatialLaw_map (q : ℕ) (H : Set (Fin q → ℝ)) :
    (originalShapeHolePoissonSpatialLaw q H).map dyadicCubePoint =
      restrictedPointLaw (cubeMeasure (Fin q) 1) H := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  have hpoint : Measurable (dyadicCubePoint (q := q)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  have hunit : ∀ᵐ x ∂cubeMeasure (Fin q) 1, x ∈ unitCube q :=
    (mem_ae_iff_prob_eq_one (measurableSet_unitCube q)).2 (cubeMeasure_unitCube q)
  have hmem : ∀ᵐ x ∂restrictedPointLaw (cubeMeasure (Fin q) 1) H, x ∈ unitCube q := by
    unfold restrictedPointLaw
    split_ifs
    · exact hunit
    · exact Measure.ae_smul_measure (ae_restrict_of_ae hunit) _
  rw [originalShapeHolePoissonSpatialLaw,Measure.map_map hpoint measurable_originalUnitCubeNormalization]
  calc
    _ = (restrictedPointLaw (cubeMeasure (Fin q) 1) H).map id := Measure.map_congr (by
      filter_upwards [hmem] with x hx
      exact dyadicCubePoint_originalUnitCubeNormalization_of_mem_unitCube x hx)
    _ = _ := Measure.map_id

/-- The original actual finite shape blocks as a readout of the independent
Poisson counts and original closed-cube iid sequences. -/
def originalShapeHolePoissonRawBlocks {q : ℕ}
    (z : (ℕ × ℕ) × ((ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ))) :=
  Prod.map (mapBlockData (Prod.map dyadicCubePoint id)) (mapBlockData (Prod.map dyadicCubePoint id))
    (originalShapeHolePoissonBlocks z)

/-- Exact actual shape law, with the outer intensity thinned only in the count
coordinate. Physical displacements and all original clock marks are unchanged. -/
theorem originalShapeHolePoisson_raw_blocks_law
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (r : ℝ≥0) (H : Set (Fin q → ℝ)) :
    MeasurePreserving (originalShapeHolePoissonRawBlocks (q := q))
      (originalShapeHolePoissonLaw (originalShapeHolePoissonSpatialLaw q H) α β
        (r*restrictionWeight (cubeMeasure (Fin q) 1) H))
      ((shapeBlockLaw q α r H).prod (shapeBlockLaw q β r H)) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  let space := originalShapeHolePoissonSpatialLaw q H
  let a := r*restrictionWeight (cubeMeasure (Fin q) 1) H
  let read : DyadicUnitCube q × ℝ → (Fin q → ℝ) × ℝ := Prod.map dyadicCubePoint id
  have hp : Measurable (dyadicCubePoint (q := q)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  have hr : Measurable read := hp.prodMap measurable_id
  have hS : (space.prod α).map read = (restrictedPointLaw (cubeMeasure (Fin q) 1) H).prod α := by
    rw [← Measure.map_prod_map _ _ hp measurable_id,originalShapeHolePoissonSpatialLaw_map,Measure.map_id]
  have hT : (space.prod β).map read = (restrictedPointLaw (cubeMeasure (Fin q) 1) H).prod β := by
    rw [← Measure.map_prod_map _ _ hp measurable_id,originalShapeHolePoissonSpatialLaw_map,Measure.map_id]
  have hs : MeasurePreserving (mapBlockData read)
      (blockDataLaw (space.prod α) (fun n ↦ poissonMeasure a {n})) (shapeBlockLaw q α r H) :=
    ⟨measurable_mapBlockData hr,blockDataLaw_mapPoints _ _ hr hS _⟩
  have ht : MeasurePreserving (mapBlockData read)
      (blockDataLaw (space.prod β) (fun n ↦ poissonMeasure a {n})) (shapeBlockLaw q β r H) :=
    ⟨measurable_mapBlockData hr,blockDataLaw_mapPoints _ _ hr hT _⟩
  have : SFinite (blockDataLaw (space.prod α) (fun n ↦ poissonMeasure a {n})) := by
    unfold blockDataLaw
    infer_instance
  have : SFinite (blockDataLaw (space.prod β) (fun n ↦ poissonMeasure a {n})) := by
    unfold blockDataLaw
    infer_instance
  exact (hs.prod ht).comp (originalShapeHolePoisson_blocks_law space α β a)

end OTSelector.Reconstruction
