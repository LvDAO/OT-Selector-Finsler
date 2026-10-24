import OTSelector.Probability.PoissonPrefixMoments

/-! Expected changed-mark counts in the actual original used Poisson prefixes.
The positions and the full original iid sequence are preserved. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- Number of original used marks whose two coupled readings disagree. -/
def markedCloudMismatchCount (q : ℕ) {A : Type*}
    (z : MarkedCloudSpace q (A × A)) : ℕ :=
  poissonPrefixCount {p : (Fin q → ℝ) × (A × A) | p.2.1 ≠ p.2.2} z

theorem integrable_markedCloudMismatchCount (q : ℕ) {A : Type*}
    [MeasurableSpace A] [MeasurableEq A]
    (κ : Measure (A × A)) [IsProbabilityMeasure κ] (r : ℝ≥0) :
    Integrable (fun z ↦ (markedCloudMismatchCount q z : ℝ))
      (markedPoissonLaw q (A × A) κ r) := by
  letI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  exact integrable_poissonPrefixCount ((cubeMeasure (Fin q) 1).prod κ) r
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)).compl

/-- The exact expected changed count is the original count mean times the
actual coupled-law disagreement mass. No filtered leftovers are assigned iid. -/
theorem integral_markedCloudMismatchCount (q : ℕ) {A : Type*}
    [MeasurableSpace A] [MeasurableEq A]
    (κ : Measure (A × A)) [IsProbabilityMeasure κ] (r : ℝ≥0) :
    (∫ z, (markedCloudMismatchCount q z : ℝ) ∂markedPoissonLaw q (A × A) κ r) =
      (r : ℝ) * (κ {p | p.1 ≠ p.2}).toReal := by
  letI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have hset : {p : (Fin q → ℝ) × (A × A) | p.2.1 ≠ p.2.2} =
      univ ×ˢ {p : A × A | p.1 ≠ p.2} := by
    ext p
    simp only [mem_prod,mem_univ,true_and,mem_ofPred_eq]
  have hm := integral_poissonPrefixCount ((cubeMeasure (Fin q) 1).prod κ) r
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)).compl
  change (∫ z, (markedCloudMismatchCount q z : ℝ) ∂markedPoissonLaw q (A × A) κ r) =
    (r : ℝ) * (((cubeMeasure (Fin q) 1).prod κ)
      {p : (Fin q → ℝ) × (A × A) | p.2.1 ≠ p.2.2}).toReal at hm
  rw [hm,hset,Measure.prod_prod,measure_univ,one_mul]

end OTSelector.Reconstruction
