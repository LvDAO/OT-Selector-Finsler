import OTSelector.Probability.CavitySemidiscreteLocalPlan
import OTSelector.Probability.CavitySemidiscreteSpatialRooting
import OTSelector.Probability.DirichletOriginalTargetScene

/-!
# Actual scaled target clouds of original semidiscrete plans

The original finite weights and observed targets define the same target marginal
as the actual rooted allocation plans. Its vague carrier and measurability follow
from the finite atomic formula; no replacement cloud is sampled.
-/

open MeasureTheory Set Function TopologicalSpace
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {Y : Type*} [MeasurableSpace Y]

instance isFiniteMeasure_semidiscreteLabelMeasure (p : Fin (m + 1) → ℝ) :
    IsFiniteMeasure (semidiscreteLabelMeasure p) := by
  constructor
  simp [semidiscreteLabelMeasure, Measure.finsetSum_apply, Measure.smul_apply]

/-- The actual target marginal, with its original weights and total-mass scale. -/
def semidiscreteTargetCloud (p : Fin (m + 1) → ℝ) (y : Fin (m + 1) → Y)
    (N : ℝ) : Measure Y :=
  ENNReal.ofReal N • (semidiscreteLabelMeasure p).map y

instance isFiniteMeasure_semidiscreteTargetCloud (p : Fin (m + 1) → ℝ)
    (y : Fin (m + 1) → Y) (N : ℝ) : IsFiniteMeasure (semidiscreteTargetCloud p y N) := by
  constructor
  simp only [semidiscreteTargetCloud, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem semidiscreteTargetCloud_eq_sum (p : Fin (m + 1) → ℝ)
    (y : Fin (m + 1) → Y) (N : ℝ) :
    semidiscreteTargetCloud p y N =
      ENNReal.ofReal N • ∑ j, ENNReal.ofReal (p j) • Measure.dirac (y j) := by
  unfold semidiscreteTargetCloud semidiscreteLabelMeasure
  rw [Measure.map_finset_sum' (measurable_of_finite y).aemeasurable]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_smul, Measure.map_dirac' (measurable_of_finite y)]

/-- Original feasible allocations have exactly the same observed target cloud. -/
theorem IsSemidiscreteAllocation.snd_scaled_observed_plan
    {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (f : S → X) (hf : Measurable f)
    (y : Fin (m + 1) → Y) (N : ℝ) :
    (ENNReal.ofReal N • (semidiscreteAllocationMeasure μ a).map (Prod.map f y)).snd =
      semidiscreteTargetCloud p y N := by
  unfold Measure.snd semidiscreteTargetCloud
  rw [Measure.map_smul, Measure.map_map measurable_snd (hf.prodMap (measurable_of_finite y))]
  congr 1
  change (semidiscreteAllocationMeasure μ a).map (y ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_of_finite y) measurable_snd, ha.isCoupling.2]

/-- Applying the same actual spatial root to both endpoints preserves the exact
scaled target marginal. -/
theorem IsSemidiscreteAllocation.snd_cavitySpatialRootedPlan
    {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure ((ι → ℝ) × A)} {p : Fin (m + 1) → ℝ}
    {a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a)
    (y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (z : ι → ℝ) :
    (cavitySpatialRootedPlan μ a y N z).snd =
      semidiscreteTargetCloud p (fun j ↦ cavitySpatialTranslate z (y j)) N :=
  ha.snd_scaled_observed_plan (cavitySpatialTranslate z)
    (measurable_cavitySpatialTranslate.comp (measurable_const.prodMk measurable_id)) _ _

/-- The cloud is a Giry-measurable observation of its original weights and points. -/
theorem measurable_semidiscreteTargetCloud
    {Ω : Type*} [MeasurableSpace Ω]
    (p : Ω → Fin (m + 1) → ℝ) (hp : ∀ j, Measurable (fun ω ↦ p ω j))
    (y : Ω → Fin (m + 1) → Y) (hy : ∀ j, Measurable (fun ω ↦ y ω j))
    (N : Ω → ℝ) (hN : Measurable N) :
    Measurable (fun ω ↦ semidiscreteTargetCloud (p ω) (y ω) (N ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [semidiscreteTargetCloud_eq_sum, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul]
  apply hN.ennreal_ofReal.mul
  exact Finset.measurable_sum _ (fun j _ ↦ (hp j).ennreal_ofReal.mul
    ((Measure.measurable_coe hU).comp (Measure.measurable_dirac.comp (hy j))))

section Vague
variable [TopologicalSpace Y] [BorelSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace Y] [SecondCountableTopology Y]

/-- The original finite target cloud as an actual locally finite measure. -/
def semidiscreteLocalTargetCloud (p : Fin (m + 1) → ℝ)
    (y : Fin (m + 1) → Y) (N : ℝ) : LocalFiniteMeasure Y :=
  ⟨semidiscreteTargetCloud p y N, inferInstance⟩

/-- The same original cloud is Borel measurable for the proved vague topology. -/
theorem measurable_semidiscreteLocalTargetCloud
    {Ω : Type*} [MeasurableSpace Ω]
    (p : Ω → Fin (m + 1) → ℝ) (hp : ∀ j, Measurable (fun ω ↦ p ω j))
    (y : Ω → Fin (m + 1) → Y) (hy : ∀ j, Measurable (fun ω ↦ y ω j))
    (N : Ω → ℝ) (hN : Measurable N) :
    Measurable (fun ω ↦ semidiscreteLocalTargetCloud (p ω) (y ω) (N ω)) :=
  measurable_localFiniteMeasure_of_measurable_measure _
    (measurable_semidiscreteTargetCloud p hp y hy N hN)

end Vague
end OTSelector.Probability
