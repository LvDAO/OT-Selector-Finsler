import OTSelector.Probability.MarkedCountShapeCloud
import OTSelector.Probability.MarkedBlockValueIntegral

/-! Exact finite-prefix pushforwards for the original independent count law.
In particular the original binomial weights are unchanged. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- The actual binomial singleton probabilities are the existing original
retained-prefix weights, including zero and unit success probability. -/
theorem binomial_singleton_eq_binomWeight (N : ℕ) (p : I) (n : ℕ) :
    ProbabilityTheory.binomial N p {n} = binomWeight N (Real.toNNReal (p : ℝ)) n := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by unfold binomWeight; finiteness)).mp
  rw [← measureReal_def, binomial_real_singleton]
  simp only [binomWeight, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.coe_toReal,
    NNReal.coe_sub (Real.toNNReal_le_one.mpr p.2.2), NNReal.coe_one,
    Real.coe_toNNReal _ (show (0 : ℝ) ≤ p from p.2.1)]

/-- Reading the original used prefix gives its literal finite block law. -/
theorem markedCountLaw_map_prefix (q : ℕ) {A : Type*} [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (κ : Measure ℕ) [IsProbabilityMeasure κ] :
    (markedCountLaw q α κ).map (fun z : MarkedCloudSpace q A ↦
      (⟨z.1, fun i : Fin z.1 ↦ z.2 i⟩ : BlockData ((Fin q → ℝ) × A))) =
        blockDataLaw ((cubeMeasure (Fin q) 1).prod α) (fun n ↦ κ {n}) := by
  let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  simpa only [markedCountLaw, markedSeqLaw] using
    (blockDataLaw_eq_map_count_cloud ((cubeMeasure (Fin q) 1).prod α) κ).symm

/-- Both independent original binomial prefixes have exactly the original
finite-block product law used by the retained physical observation theorem. -/
theorem twoMarkedBinomialLaw_map_prefix (q : ℕ) {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) :
    (twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)).map
      (Prod.map (fun z : MarkedCloudSpace q A ↦
        (⟨z.1, fun i : Fin z.1 ↦ z.2 i⟩ : BlockData ((Fin q → ℝ) × A)))
        (fun z : MarkedCloudSpace q B ↦
          (⟨z.1, fun i : Fin z.1 ↦ z.2 i⟩ : BlockData ((Fin q → ℝ) × B)))) =
      (blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
        (binomWeight N (Real.toNNReal (p : ℝ)))).prod
      (blockDataLaw ((cubeMeasure (Fin q) 1).prod β)
        (binomWeight N (Real.toNNReal (p : ℝ)))) := by
  unfold twoMarkedCountLaw
  rw [← Measure.map_prod_map _ _ (measurable_blockDataMk q A) (measurable_blockDataMk q B),
    markedCountLaw_map_prefix, markedCountLaw_map_prefix]
  simp only [binomial_singleton_eq_binomWeight]

end OTSelector.Probability
