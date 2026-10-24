import OTSelector.Probability.CavitySemidiscreteCoupling
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real

/-!
# Real-to-ENNReal energy bridge for semidiscrete allocations

The mark-window estimates consume `ℝ≥0∞`-valued energy integrals, while the
Dirichlet energy theorem returns real allocation costs.  This module converts
one to the other exactly, using the allocation coupling and nonnegativity of the
base cost.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {S : Type*} [MeasurableSpace S] {m : ℕ}

/-- The `ℝ≥0∞` lintegral of a nonnegative measurable edge cost against the
allocation coupling is the `ofReal` of its semidiscrete allocation cost. -/
theorem lintegral_ofReal_semidiscreteAllocationCost
    (μ : Measure S) [IsProbabilityMeasure μ]
    (a : S → Fin (m + 1) → ℝ) {p : Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a)
    (c : S → Fin (m + 1) → ℝ) (hcm : Measurable (Function.uncurry c))
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hcn : ∀ᵐ s ∂μ, ∀ j, 0 ≤ c s j) :
    (∫⁻ e, ENNReal.ofReal (c e.1 e.2)
        ∂semidiscreteAllocationMeasure μ a) =
      ENNReal.ofReal (semidiscreteAllocationCost μ c a) := by
  have hreal : (∫ e, c e.1 e.2 ∂semidiscreteAllocationMeasure μ a) =
      semidiscreteAllocationCost μ c a :=
    ha.integral_allocationMeasure c hcm hc
  have hci : Integrable (fun e : S × Fin (m + 1) ↦ c e.1 e.2)
      (semidiscreteAllocationMeasure μ a) :=
    ha.integrable_allocationMeasure c hcm hc
  have hmp : MeasurePreserving Prod.fst (semidiscreteAllocationMeasure μ a) μ :=
    ⟨measurable_fst, ha.isCoupling.1⟩
  have hnonneg : ∀ᵐ e ∂semidiscreteAllocationMeasure μ a, 0 ≤ c e.1 e.2 :=
    (hmp.quasiMeasurePreserving.ae hcn).mono fun e he ↦ he e.2
  have hof := ofReal_integral_eq_lintegral_ofReal hci hnonneg
  rw [hreal] at hof
  exact hof.symm

/-- The same bridge with the joint environment measure, for a measurable family
of allocations that is feasible almost everywhere. -/
theorem lintegral_ofReal_semidiscreteAllocationCost_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (a : Ω → S → Fin (m + 1) → ℝ) (p : Ω → Fin (m + 1) → ℝ)
    (hfeas : ∀ᵐ ω ∂P, IsSemidiscreteAllocation μ (p ω) (fun s ↦ a ω s))
    (c : Ω → S → Fin (m + 1) → ℝ)
    (hcm : ∀ ω, Measurable (Function.uncurry (c ω)))
    (hc : ∀ ω j, Integrable (fun s ↦ c ω s j) μ)
    (hcn : ∀ᵐ ω ∂P, ∀ᵐ s ∂μ, ∀ j, 0 ≤ c ω s j) :
    (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (c ω e.1 e.2)
        ∂semidiscreteAllocationMeasure μ (fun s ↦ a ω s) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (semidiscreteAllocationCost μ (c ω) (fun s ↦ a ω s)) ∂P := by
  apply lintegral_congr_ae
  filter_upwards [hfeas, hcn] with ω hω hcω
  exact lintegral_ofReal_semidiscreteAllocationCost μ (fun s ↦ a ω s) hω
    (c ω) (hcm ω) (hc ω) hcω

end OTSelector.Probability
