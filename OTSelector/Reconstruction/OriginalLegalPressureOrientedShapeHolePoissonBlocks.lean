import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonMean
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonLaw
import OTSelector.Probability.BlockDataTransport

/-! The conditioned independent Poisson arrays have their literal finite block laws. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Keep the two actual counts and exactly their original finite iid prefixes. -/
def originalShapeHolePoissonBlocks {q : ℕ}
    (z : (ℕ × ℕ) × ((ℕ → DyadicUnitCube q × ℝ) × (ℕ → DyadicUnitCube q × ℝ))) :
    BlockData (DyadicUnitCube q × ℝ) × BlockData (DyadicUnitCube q × ℝ) :=
  (⟨z.1.1,fun i : Fin z.1.1 ↦ z.2.1 i⟩,⟨z.1.2,fun j : Fin z.1.2 ↦ z.2.2 j⟩)

/-- Conditioning on the independent original Poisson counts gives exactly the
original two independent block laws. No law of unused or selected positions is
assumed. The original finite enumerations and mark coordinates are unchanged. -/
theorem originalShapeHolePoisson_blocks_law
    {q : ℕ} (space : Measure (DyadicUnitCube q)) [IsProbabilityMeasure space]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (a : ℝ≥0) :
    MeasurePreserving (originalShapeHolePoissonBlocks (q := q))
      (originalShapeHolePoissonLaw space α β a)
      ((blockDataLaw (space.prod α) (fun n ↦ poissonMeasure a {n})).prod
        (blockDataLaw (space.prod β) (fun n ↦ poissonMeasure a {n}))) := by
  let embed := fun z : ℕ × (ℕ → DyadicUnitCube q × ℝ) ↦
    (⟨z.1,fun i : Fin z.1 ↦ z.2 i⟩ : BlockData (DyadicUnitCube q × ℝ))
  have hm : Measurable embed := measurable_from_prod_countable_right fun n ↦
    (measurable_sigma_mk n).comp (by fun_prop)
  have hS : MeasurePreserving embed
      ((poissonMeasure a).prod (Measure.infinitePi (fun _ : ℕ ↦ space.prod α)))
      (blockDataLaw (space.prod α) (fun n ↦ poissonMeasure a {n})) :=
    ⟨hm,(blockDataLaw_eq_map_cloud (space.prod α) a).symm⟩
  have hT : MeasurePreserving embed
      ((poissonMeasure a).prod (Measure.infinitePi (fun _ : ℕ ↦ space.prod β)))
      (blockDataLaw (space.prod β) (fun n ↦ poissonMeasure a {n})) :=
    ⟨hm,(blockDataLaw_eq_map_cloud (space.prod β) a).symm⟩
  exact (hS.prod hT).comp (originalShapeHolePoisson_shuffle (poissonMeasure a) (poissonMeasure a)
    (Measure.infinitePi (fun _ : ℕ ↦ space.prod α)) (Measure.infinitePi (fun _ : ℕ ↦ space.prod β)))

end OTSelector.Reconstruction
