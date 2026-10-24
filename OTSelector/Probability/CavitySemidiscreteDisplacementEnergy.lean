import OTSelector.Transport.Semidiscrete.Calibration
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Semidiscrete displacement energy from a base-cost lower bound

A pointwise quadratic lower bound for the base edge cost controls the expected
squared displacement of every feasible semidiscrete allocation.  The statement is
coordinate-free in the source space: a measurable spatial coordinate extracts the
label used by the displacement, and the target points live in the same normed
space.  No optimality, uniqueness or compactness is assumed.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S V : Type*} [MeasurableSpace S] [NormedAddCommGroup V] {m : ℕ}

/-- A quadratic lower bound on the base cost controls the expected squared
coordinate displacement of every feasible allocation. -/
theorem semidiscrete_displacement_energy_le
    (μ : Measure S) [IsProbabilityMeasure μ]
    (coord : S → V)
    (Y : Fin (m + 1) → V)
    (c : S → Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hd : ∀ j, Integrable (fun s ↦ ‖Y j - coord s‖ ^ 2) μ)
    {q : ℝ}
    (hbound : ∀ᵐ s ∂μ, ∀ j, q * ‖Y j - coord s‖ ^ 2 ≤ c s j) :
    Integrable (fun s ↦ ∑ j, a s j * ‖Y j - coord s‖ ^ 2) μ ∧
      q * (∫ s, ∑ j, a s j * ‖Y j - coord s‖ ^ 2 ∂μ) ≤
        semidiscreteAllocationCost μ c a := by
  have hdisp (j : Fin (m + 1)) :
      Integrable (fun s ↦ a s j * ‖Y j - coord s‖ ^ 2) μ := by
    apply (hd j).bdd_mul (ha.integrable j).aestronglyMeasurable
    filter_upwards [ha.nonneg, ha.ae_le_one] with s hn hu
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn j)] using hu j
  have hleft : Integrable (fun s ↦ ∑ j, a s j * ‖Y j - coord s‖ ^ 2) μ :=
    integrable_finsetSum Finset.univ fun j _ ↦ hdisp j
  have hright : Integrable (fun s ↦ ∑ j, a s j * c s j) μ :=
    integrable_finsetSum Finset.univ fun j _ ↦ ha.integrable_mul c hc j
  have hle : (fun s ↦ q * ∑ j, a s j * ‖Y j - coord s‖ ^ 2) ≤ᵐ[μ]
      fun s ↦ ∑ j, a s j * c s j := by
    filter_upwards [ha.nonneg, hbound] with s hn hb
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      q * (a s j * ‖Y j - coord s‖ ^ 2) = a s j * (q * ‖Y j - coord s‖ ^ 2) := by ring
      _ ≤ a s j * c s j := mul_le_mul_of_nonneg_left (hb j) (hn j)
  refine ⟨hleft, ?_⟩
  have hmono := integral_mono_ae (hleft.const_mul q) hright hle
  rw [integral_const_mul] at hmono
  exact hmono

end OTSelector.Probability
