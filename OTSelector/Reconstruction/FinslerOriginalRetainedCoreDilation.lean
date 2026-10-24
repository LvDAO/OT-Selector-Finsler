import OTSelector.MeasureTheory.DensityPowerChangeOfMeasure

/-!
# Retained-core dilation to the weighted stationary value

This module isolates the dilation step of the retained core: a retained mass
fraction lam of the original stationary population carries the pressure
lam^(1 - 2/q) I(t lam^(2/q)), and the difference from the full dilated pressure
is exactly a boundary loss controlled by the mass of the region that is not
retained.

1. **Exact dilation identity at constant retained density**
   (retainedPressure_constantDensity): the pressure of the retained core, with
   retained density lam against the original population measure, equals
   lam^(1 - 2/q) times the population pressure at the dilated tilt
   t lam^(2/q).  This is the identity
   (1 - rho)^(1 - 2/q) I_w(t (1 - rho)^(2/q)) of the finite-value comparison at
   the level of the population integral.

2. **Retained pressure on a retained region**
   (retainedPressure_indicator_scale): if the retained core is the region S with
   retained density lam on S and zero outside, then its pressure equals
   lam^(1 - 2/q) times the population pressure integrated over S at the dilated
   tilt.  So the dilation is exact on the retained region.

3. **Boundary-loss bound** (retainedCore_boundaryLoss): the difference between
   the population integral over the retained region and the full population
   integral is bounded by the uniform pressure bound B times the mass of the
   complementary boundary.

4. **Dilation up to boundary loss** (retainedCore_pressure_boundaryLoss): the
   retained-core pressure differs from the dilated full pressure
   lam^(1 - 2/q) int I(t lam^(2/q)) by at most lam^(1 - 2/q) B mu.real S^c.
   This is the paper's "identical up to boundary losses" statement for the
   retained core.

## Remaining gap

The population-level dilation identity, its region form and the boundary-loss
bound are proved here.  The passage to the actual marked Poisson legal matching
requires applying this with the local legal pressure function of the weighted
stationary Palm minimizer and identifying the population measure with the Palm
law of the candidate weighted stationary matching, the boundary mass being the
loss of the box truncation.  That Palm identification is the remaining modeling
step; it is not a statement about the dilation algebra.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

variable {X : Type*} [MeasurableSpace X]

/-- **Exact retained-core dilation at constant retained density.**  If the
retained core carries the constant density lam against the original population
measure mu, then its pressure at tilt t equals lam^(1 - 2/q) times the
population pressure at the dilated tilt t lam^(2/q). -/
theorem retainedPressure_constantDensity
    (μ : Measure X) {q : ℕ} (I : X → ℝ → ℝ) (t : ℝ)
    {lam : ℝ} (hlam : 0 < lam) :
    (∫ x, lam ^ (-(2 / (q : ℝ))) * I x (t * lam ^ (2 / (q : ℝ)))
        ∂(μ.withDensity (fun _ => ENNReal.ofReal lam))) =
      lam ^ (1 - 2 / (q : ℝ)) *
        (∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) := by
  rw [withDensity_const, integral_smul_measure, ENNReal.toReal_ofReal hlam.le,
    smul_eq_mul, integral_const_mul]
  have hsplit : lam * lam ^ (-(2 / (q : ℝ))) = lam ^ (1 - 2 / (q : ℝ)) := by
    rw [show (1 : ℝ) - 2 / (q : ℝ) = 1 + -(2 / (q : ℝ)) by ring,
      Real.rpow_add hlam, Real.rpow_one]
  rw [← hsplit]
  ring

/-- **Retained pressure on a retained region.**  If the retained core is the
measurable region S with retained density lam on S and zero outside, then its
pressure at tilt t equals lam^(1 - 2/q) times the population pressure integrated
over S at the dilated tilt. -/
theorem retainedPressure_indicator_scale
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S) {q : ℕ}
    (I : X → ℝ → ℝ) (t : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (∫ x, lam ^ (-(2 / (q : ℝ))) * I x (t * lam ^ (2 / (q : ℝ)))
        ∂(μ.withDensity (S.indicator (fun _ => ENNReal.ofReal lam)))) =
      lam ^ (1 - 2 / (q : ℝ)) *
        (∫ x in S, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) := by
  rw [withDensity_indicator hS, withDensity_const, integral_smul_measure,
    ENNReal.toReal_ofReal hlam.le, smul_eq_mul, integral_const_mul]
  have hsplit : lam * lam ^ (-(2 / (q : ℝ))) = lam ^ (1 - 2 / (q : ℝ)) := by
    rw [show (1 : ℝ) - 2 / (q : ℝ) = 1 + -(2 / (q : ℝ)) by ring,
      Real.rpow_add hlam, Real.rpow_one]
  rw [← hsplit]
  ring

/-- **Boundary-loss bound.**  Replacing the full population integral of a
function bounded by B by the integral over the retained region S loses at most
B times the mass of the complementary region. -/
theorem retainedCore_boundaryLoss
    (μ : Measure X) [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S)
    {f : X → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) (hint : Integrable f μ) :
    |(∫ x in S, f x ∂μ) - (∫ x, f x ∂μ)| ≤ B * μ.real Sᶜ := by
  have hsplit : (∫ x, f x ∂μ) =
      (∫ x in S, f x ∂μ) + (∫ x in Sᶜ, f x ∂μ) := by
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hS]
    rw [integral_add_measure hint.restrict hint.restrict]
  have hb : |∫ x in Sᶜ, f x ∂μ| ≤ B * μ.real Sᶜ := by
    have hnorm : ‖∫ x in Sᶜ, f x ∂μ‖ ≤ B * μ.real Sᶜ :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top (μ := μ) (s := Sᶜ))
        (fun x _ => by
          rw [Real.norm_eq_abs]
          exact hB x)
    simpa only [Real.norm_eq_abs] using hnorm
  rw [hsplit]
  have hsub : (∫ x in S, f x ∂μ) -
      ((∫ x in S, f x ∂μ) + (∫ x in Sᶜ, f x ∂μ)) = -(∫ x in Sᶜ, f x ∂μ) := by ring
  rw [hsub, abs_neg]
  exact hb

/-- **Dilation up to boundary loss.**  The retained-core pressure differs from
the dilated full population pressure by at most lam^(1 - 2/q) times the uniform
boundary pressure B times the mass outside the retained region. -/
theorem retainedCore_pressure_boundaryLoss
    (μ : Measure X) [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S)
    {q : ℕ} (I : X → ℝ → ℝ) (t : ℝ) {lam B : ℝ}
    (hlam : 0 < lam) (hB : ∀ x u, |I x u| ≤ B)
    (hint : Integrable (fun x => I x (t * lam ^ (2 / (q : ℝ)))) μ) :
    |(∫ x, lam ^ (-(2 / (q : ℝ))) * I x (t * lam ^ (2 / (q : ℝ)))
          ∂(μ.withDensity (S.indicator (fun _ => ENNReal.ofReal lam)))) -
        lam ^ (1 - 2 / (q : ℝ)) *
          (∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ)| ≤
      lam ^ (1 - 2 / (q : ℝ)) * B * μ.real Sᶜ := by
  rw [retainedPressure_indicator_scale μ hS I t hlam]
  have hb : |(∫ x in S, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) -
      (∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ)| ≤ B * μ.real Sᶜ :=
    retainedCore_boundaryLoss (μ := μ) (S := S) hS
      (f := fun x => I x (t * lam ^ (2 / (q : ℝ))))
      (fun x => hB x (t * lam ^ (2 / (q : ℝ)))) hint
  have hfac : (0 : ℝ) ≤ lam ^ (1 - 2 / (q : ℝ)) := Real.rpow_nonneg hlam.le _
  have hrewrite : lam ^ (1 - 2 / (q : ℝ)) *
        (∫ x in S, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) -
      lam ^ (1 - 2 / (q : ℝ)) *
        (∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) =
      lam ^ (1 - 2 / (q : ℝ)) *
        ((∫ x in S, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) -
          (∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ)) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg hfac]
  calc lam ^ (1 - 2 / (q : ℝ)) *
        |(∫ x in S, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) -
          (∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ)|
      ≤ lam ^ (1 - 2 / (q : ℝ)) * (B * μ.real Sᶜ) :=
        mul_le_mul_of_nonneg_left hb hfac
    _ = lam ^ (1 - 2 / (q : ℝ)) * B * μ.real Sᶜ := by ring

end OTSelector.Reconstruction
