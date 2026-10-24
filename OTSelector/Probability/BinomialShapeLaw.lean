import OTSelector.Probability.CountRestriction
import OTSelector.Probability.MarkedShapeLaw
import OTSelector.Probability.MarkedCountShapeCloud

/-! Literal original binomial shape-prefix laws and expectation transport.
The spatial shape and the original full-box retention may change with N. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Exact original finite shape law: the point law is normalized inside the
shape, and the count keeps the original box probability times shape mass. -/
def binomialShapeBlockLaw (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (N : ℕ) (p : I) (S : Set (Fin q → ℝ)) :
    Measure (BlockData ((Fin q → ℝ) × A)) := by
  let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  exact blockDataLaw ((restrictedPointLaw (cubeMeasure (Fin q) 1) S).prod α)
    (binomWeight N (Real.toNNReal (p : ℝ) * restrictionWeight (cubeMeasure (Fin q) 1) S))

/-- Spatial restriction of the original binomial cloud has exactly its actual
shape prefix law, including the zero-count law of a null shape. -/
theorem map_shapeCloud_markedBinomialLaw (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (N : ℕ) (p : I)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    (markedCountLaw q α (ProbabilityTheory.binomial N p)).map (shapeCloud S) =
      binomialShapeBlockLaw q α N p S := by
  unfold binomialShapeBlockLaw
  let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have h := map_binomial_restrictedPrefix ((cubeMeasure (Fin q) 1).prod α) N p
    (hS.preimage measurable_fst)
  have heq : shapeCloud (A := A) S = restrictedPrefix (Prod.fst ⁻¹' S) :=
    funext (shapeCloud_eq_restrictedPrefix q S)
  rw [heq]
  simpa only [markedCountLaw, markedSeqLaw, restrictedPointLaw_prod_fst _ _,
    restrictionWeight_prod_fst] using h

/-- The two actual original restricted colors remain independent with their
literal finite-prefix distributions. -/
theorem map_shapeCloud_twoMarkedBinomialLaw (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    (twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)).map
      (Prod.map (shapeCloud S) (shapeCloud S)) =
      (binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S) := by
  unfold twoMarkedCountLaw
  rw [← Measure.map_prod_map _ _ (measurable_shapeCloud hS) (measurable_shapeCloud hS),
    map_shapeCloud_markedBinomialLaw q α N p hS, map_shapeCloud_markedBinomialLaw q β N p hS]

/-- A measurable original finite-prefix observable has the identical expected
value under the actual shape law and its literal full-box restriction. -/
theorem shapeCloud_binomial_integrable_integral (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (F : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) → ℝ)
    (hF : Measurable F)
    (hI : Integrable (fun sample : TwoMarkedCloudSpace q A B ↦
      F (shapeCloud S sample.1, shapeCloud S sample.2))
      (twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p))) :
    Integrable F ((binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S)) ∧
    (∫ d, F d ∂(binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S)) =
      ∫ sample, F (shapeCloud S sample.1, shapeCloud S sample.2)
        ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p) := by
  let sel : TwoMarkedCloudSpace q A B →
      BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) :=
    Prod.map (shapeCloud S) (shapeCloud S)
  have hsel : Measurable sel :=
    ((measurable_shapeCloud (A := A) hS).comp measurable_fst).prodMk
      ((measurable_shapeCloud (A := B) hS).comp measurable_snd)
  have hlaw : (twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)).map sel =
      (binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S) :=
    map_shapeCloud_twoMarkedBinomialLaw q α β N p hS
  constructor
  · rw [← hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable hsel.aemeasurable).mpr hI
  · rw [← hlaw, integral_map hsel.aemeasurable hF.aestronglyMeasurable]
    rfl

end OTSelector.Probability
