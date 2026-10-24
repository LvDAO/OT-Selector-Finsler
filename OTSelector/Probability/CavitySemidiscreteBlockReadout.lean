import OTSelector.Probability.CavitySemidiscreteTargetBlockWitness
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurable actual source-target block masses

Moving source sets and target-label sets are read against the actual allocation.
Joint measurability supplies measurable block masses and bounded cycle witnesses.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

/-- Jointly measurable allocation coefficients and measurable moving blocks give a
measurable actual block-mass readout. -/
theorem measurable_parameterized_semidiscreteBlockMass
    (μ : Measure S) [SFinite μ] (a : V × S → Fin (m + 1) → ℝ)
    (ha : ∀ j, Measurable (fun x ↦ a x j))
    (A : V → Set S) (hA : MeasurableSet {x : V × S | x.2 ∈ A x.1})
    (J : V → Finset (Fin (m + 1))) (hJ : ∀ j, MeasurableSet {z | j ∈ J z}) :
    Measurable (fun z ↦ semidiscreteBlockMass μ (fun s ↦ a (z, s)) (A z) (J z)) := by
  classical
  have hAz (z : V) : MeasurableSet (A z) :=
    hA.preimage (measurable_const.prodMk measurable_id)
  have hi (j : Fin (m + 1)) : Measurable
      (fun z ↦ ∫ s in A z, a (z, s) j ∂μ) := by
    have hm := (((ha j).indicator hA).stronglyMeasurable.integral_prod_right'
      (ν := μ)).measurable
    change Measurable (fun z ↦ ∫ s, (A z).indicator (fun s ↦ a (z, s) j) s ∂μ) at hm
    simpa only [integral_indicator (hAz _)] using hm
  have hs : Measurable (fun z ↦ ∑ j : Fin (m + 1),
      if j ∈ J z then ∫ s in A z, a (z, s) j ∂μ else 0) :=
    Finset.measurable_sum Finset.univ
      (fun j _ ↦ Measurable.ite (hJ j) (hi j) measurable_const)
  simpa only [Finset.sum_ite_mem, Finset.univ_inter, semidiscreteBlockMass] using hs

/-- The bounded cycle witness is the smaller of one and the two actual block masses. -/
def semidiscreteCycleBlockWitness (μ : Measure S) (a : S → Fin (m + 1) → ℝ)
    (A B : Set S) (J L : Finset (Fin (m + 1))) : ℝ :=
  min 1 (min (semidiscreteBlockMass μ a A J) (semidiscreteBlockMass μ a B L))

theorem IsSemidiscreteAllocation.cycleBlockWitness_nonneg
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (A B : Set S)
    (J L : Finset (Fin (m + 1))) :
    0 ≤ semidiscreteCycleBlockWitness μ a A B J L :=
  le_min zero_le_one (le_min (ha.blockMass_nonneg A J) (ha.blockMass_nonneg B L))

theorem semidiscreteCycleBlockWitness_le_one
    (μ : Measure S) (a : S → Fin (m + 1) → ℝ) (A B : Set S)
    (J L : Finset (Fin (m + 1))) :
    semidiscreteCycleBlockWitness μ a A B J L ≤ 1 := min_le_left _ _

theorem measurable_parameterized_semidiscreteCycleBlockWitness
    (μ : Measure S) [SFinite μ] (a : V × S → Fin (m + 1) → ℝ)
    (ha : ∀ j, Measurable (fun x ↦ a x j))
    (A B : V → Set S)
    (hA : MeasurableSet {x : V × S | x.2 ∈ A x.1})
    (hB : MeasurableSet {x : V × S | x.2 ∈ B x.1})
    (J L : V → Finset (Fin (m + 1)))
    (hJ : ∀ j, MeasurableSet {z | j ∈ J z})
    (hL : ∀ j, MeasurableSet {z | j ∈ L z}) :
    Measurable (fun z ↦ semidiscreteCycleBlockWitness μ
      (fun s ↦ a (z, s)) (A z) (B z) (J z) (L z)) :=
  measurable_const.min
    ((measurable_parameterized_semidiscreteBlockMass μ a ha A hA J hJ).min
      (measurable_parameterized_semidiscreteBlockMass μ a ha B hB L hL))

end OTSelector.Probability
