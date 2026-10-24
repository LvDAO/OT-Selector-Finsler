import OTSelector.Probability.CavitySemidiscretePressureValue
import LeanPool.Vlasov.OT.Coupling
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Semidiscrete allocations as actual coupling measures

Each source-to-label allocation produces its full measure on the source-label product.
Both marginals and every integrable paired cost are preserved exactly. Coefficients
need only be measurable almost everywhere, as in the original allocation primal.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- The actual target-label marginal specified by real mass coordinates. -/
def semidiscreteLabelMeasure (p : Fin (m + 1) → ℝ) : Measure (Fin (m + 1)) :=
  ∑ j, ENNReal.ofReal (p j) • Measure.dirac j

/-- The actual product measure of a source-to-label allocation. -/
def semidiscreteAllocationMeasure (μ : Measure S) (a : S → Fin (m + 1) → ℝ) :
    Measure (S × Fin (m + 1)) :=
  ∑ j, (μ.withDensity (fun s ↦ ENNReal.ofReal (a s j))).map (fun s ↦ (s, j))

@[simp]
theorem semidiscreteLabelMeasure_singleton (p : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    semidiscreteLabelMeasure p {j} = ENNReal.ofReal (p j) := by
  simp [semidiscreteLabelMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply', Pi.single_apply]

/-- The label submeasure has exactly the allocated mass. -/
theorem IsSemidiscreteAllocation.withDensity_univ {μ : Measure S}
    {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (j : Fin (m + 1)) :
    μ.withDensity (fun s ↦ ENNReal.ofReal (a s j)) univ = ENNReal.ofReal (p j) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (ha.integrable j)
      (ha.nonneg.mono fun _ h ↦ h j), ha.mass]

/-- The density submeasures sum to the original source measure. -/
theorem IsSemidiscreteAllocation.sum_withDensity {μ : Measure S}
    {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) :
    ∑ j, μ.withDensity (fun s ↦ ENNReal.ofReal (a s j)) = μ := by
  ext B hB
  rw [Measure.finsetSum_apply]
  simp_rw [withDensity_apply _ hB]
  rw [← lintegral_finsetSum' _ (fun j _ ↦
    ((ha.integrable j).aestronglyMeasurable.aemeasurable.ennreal_ofReal).restrict)]
  have heq : (fun s ↦ ∑ j, ENNReal.ofReal (a s j)) =ᵐ[μ.restrict B] fun _ ↦ 1 := by
    filter_upwards [ae_restrict_of_ae ha.nonneg, ae_restrict_of_ae ha.sum_one] with s hn hs
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hn j), hs, ENNReal.ofReal_one]
  rw [lintegral_congr_ae heq]
  simp

/-- Every feasible allocation is a coupling of the exact original source and label marginals. -/
theorem IsSemidiscreteAllocation.isCoupling {μ : Measure S}
    {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) :
    Vlasov.IsCoupling (semidiscreteAllocationMeasure μ a) μ (semidiscreteLabelMeasure p) := by
  constructor
  · rw [semidiscreteAllocationMeasure, Measure.map_finset_sum' measurable_fst.aemeasurable]
    have heq (j : Fin (m + 1)) :
        ((μ.withDensity (fun s ↦ ENNReal.ofReal (a s j))).map (fun s ↦ (s, j))).map
          Prod.fst = μ.withDensity (fun s ↦ ENNReal.ofReal (a s j)) := by
      rw [Measure.map_map measurable_fst (by fun_prop)]
      exact Measure.map_id
    simpa only [heq] using ha.sum_withDensity
  · rw [semidiscreteAllocationMeasure, Measure.map_finset_sum' measurable_snd.aemeasurable]
    unfold semidiscreteLabelMeasure
    apply Finset.sum_congr rfl
    intro j _
    rw [Measure.map_map measurable_snd (by fun_prop)]
    change (μ.withDensity (fun s ↦ ENNReal.ofReal (a s j))).map (fun _ ↦ j) = _
    rw [Measure.map_const, ha.withDensity_univ]

/-- Integrable paired costs remain integrable for the constructed allocation coupling. -/
theorem IsSemidiscreteAllocation.integrable_allocationMeasure {μ : Measure S}
    {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (c : S → Fin (m + 1) → ℝ)
    (hcm : Measurable (Function.uncurry c))
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ) :
    Integrable (Function.uncurry c) (semidiscreteAllocationMeasure μ a) := by
  apply integrable_finsetSum_measure.mpr
  intro j _
  apply (integrable_map_measure hcm.aestronglyMeasurable
    (measurable_id.prodMk measurable_const).aemeasurable).mpr
  apply (integrable_withDensity_iff_integrable_smul₀'
    (ha.integrable j).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun s ↦ ENNReal.ofReal_lt_top)).mpr
  exact (ha.integrable_mul c hc j).congr (ha.nonneg.mono fun s hs ↦ by
    simp only [ENNReal.toReal_ofReal (hs j), smul_eq_mul, Function.comp_def,
      Function.uncurry_apply_pair, id_eq])

/-- Passing from allocation coefficients to a coupling preserves the actual full paired cost. -/
theorem IsSemidiscreteAllocation.integral_allocationMeasure {μ : Measure S}
    {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (c : S → Fin (m + 1) → ℝ)
    (hcm : Measurable (Function.uncurry c))
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ) :
    ∫ z, c z.1 z.2 ∂semidiscreteAllocationMeasure μ a =
      semidiscreteAllocationCost μ c a := by
  have hi := ha.integrable_allocationMeasure c hcm hc
  change Integrable (Function.uncurry c) (∑ j,
    (μ.withDensity (fun s ↦ ENNReal.ofReal (a s j))).map (fun s ↦ (s, j))) at hi
  change (∫ z, Function.uncurry c z ∂semidiscreteAllocationMeasure μ a) = _
  rw [semidiscreteAllocationMeasure, integral_finsetSum_measure
    (integrable_finsetSum_measure.mp hi)]
  unfold semidiscreteAllocationCost
  rw [integral_finsetSum _ (fun j _ ↦ ha.integrable_mul c hc j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_map (show AEMeasurable (fun s : S ↦ (s, j))
      (μ.withDensity (fun s ↦ ENNReal.ofReal (a s j))) from (by fun_prop))
    hcm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      (ha.integrable j).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun s ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ha.nonneg] with s hs
  simp only [ENNReal.toReal_ofReal (hs j), smul_eq_mul, Function.uncurry]

end OTSelector.Probability
