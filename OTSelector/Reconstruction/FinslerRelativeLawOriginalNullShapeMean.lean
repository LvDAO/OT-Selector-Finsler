import OTSelector.Reconstruction.FinslerRelativeLawOriginalNullValue
import OTSelector.Reconstruction.FinslerConcreteUpperClassBinomialShape

/-! Haar-null microscopic shapes have exact empty binomial prefixes and zero physical mean. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

/-- A null shape reads the empty prefix under the original full-box binomial
experiment, independently of its unused conditional fallback law. -/
theorem binomialShapeBlockLaw_eq_empty_of_null
    {A : Type*} [MeasurableSpace A] (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (N : ℕ) (p : unitInterval) {S : Set (Fin q → ℝ)}
    (hnull : (cubeMeasure (Fin q) 1) S = 0) :
    binomialShapeBlockLaw q α N p S = Measure.dirac (emptyOriginalBlockData ((Fin q → ℝ) × A)) := by
  letI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  unfold binomialShapeBlockLaw
  rw [show restrictionWeight (cubeMeasure (Fin q) 1) S = 0 from by
    simp only [restrictionWeight, hnull, ENNReal.toNNReal_zero], mul_zero]
  exact blockDataLaw_binomWeight_zero _ N

/-- The true signed physical affine value of a null shape has zero mean and
is integrable for arbitrary raw kernels. No global cost bound is needed. -/
theorem integrable_integral_affineClassBinomialShape_null
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q : ℕ) (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (source : A → ℝ) (target : B → ℝ) (N : ℕ) (p : unitInterval) (side : ℝ≥0)
    (origin : Fin q → ℝ) {S : Set (Fin q → ℝ)} (hnull : (cubeMeasure (Fin q) 1) S = 0)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (tilt : ℝ) :
    Integrable (fun d ↦ unclampedBlockLegalTilted q source target N kin probe tilt
      (mapBlockData (affineMarkedPoint origin side) d.1)
      (mapBlockData (affineMarkedPoint origin side) d.2))
      ((binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S)) ∧
    affineClassBinomialShapeExpectation source target α β N p side origin S kin probe tilt = 0 := by
  let law := (binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S)
  let value := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
    unclampedBlockLegalTilted q source target N kin probe tilt
      (mapBlockData (affineMarkedPoint origin side) d.1)
      (mapBlockData (affineMarkedPoint origin side) d.2)
  have hlaw : law = Measure.dirac
      (emptyOriginalBlockData ((Fin q → ℝ) × A), emptyOriginalBlockData ((Fin q → ℝ) × B)) := by
    dsimp only [law]
    rw [binomialShapeBlockLaw_eq_empty_of_null q α N p hnull,
      binomialShapeBlockLaw_eq_empty_of_null q β N p hnull, Measure.dirac_prod_dirac]
  have h := integrable_integral_zero_of_map_empty_prefix law id measurable_id
    (by simpa only [Measure.map_id] using hlaw) value (by
      simp only [value, mapBlockData_emptyOriginalBlockData, unclampedBlockLegalTilted_empty_source])
  exact h

end OTSelector.Reconstruction
