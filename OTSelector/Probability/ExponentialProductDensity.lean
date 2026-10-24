import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import OTSelector.MeasureTheory.FiniteProductDensity
import OTSelector.MeasureTheory.SimplexCoordinateVolume
import OTSelector.MeasureTheory.SimplexMassCoordinates
import OTSelector.Probability.GammaSimplexDensity

/-!
Conditions: Actual independent mean-one exponential coordinates and measurable nonnegative finite-dimensional tests.

Objects: The genuine product density exp(−Σx_i) on the positive orthant and its total-mass/simplex integral formula.

Proof detail: Apply the finite-product density theorem, multiply the exponential coordinate densities, and use the actual volume-preserving total-mass shear.

References: Günter Last and Mathew Penrose: Section 1.4, equations (1.23), (1.27)–(1.28), p. 6; Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163.
Relation: The independent exponential density and coordinate disintegration are proved explicitly. No independence of normalized weights and total mass is assumed here.
-/


/-!
# Independent exponentials in total-mass coordinates

The genuine finite product of mean-one exponential laws has density
`exp(-sum x)` on the positive orthant. The measure-preserving mass-coordinate
map expresses its integral as an integral over positive totals and simplices.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

theorem pi_expMeasure_one_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ expMeasure 1) =
      volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i, exponentialPDF 1 (x i)) := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hmeasure : volume.withDensity (exponentialPDF 1) = expMeasure 1 := by
    rfl
  let : SigmaFinite (volume.withDensity (exponentialPDF 1)) :=
    hmeasure.symm ▸ (inferInstance : SigmaFinite (expMeasure 1))
  rw [← hmeasure]
  exact finPi_withDensity n (fun _ ↦ exponentialPDF 1)
    (fun _ ↦ (measurable_exponentialPDFReal 1).ennreal_ofReal)

theorem ae_pos_pi_expMeasure_one (n : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n ↦ expMeasure 1), x ∈ positiveCoordinateOrthant n := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  apply ae_all_iff.mpr
  intro i
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ expMeasure 1) i).ae
    (ae_pos_gammaMeasure 1 1)

theorem prod_exponentialPDF_one_of_pos (n : ℕ) {x : Fin n → ℝ}
    (hx : x ∈ positiveCoordinateOrthant n) :
    (∏ i, exponentialPDF 1 (x i)) = ENNReal.ofReal (Real.exp (-(∑ i, x i))) := by
  have hi (i : Fin n) : exponentialPDF 1 (x i) =
      ENNReal.ofReal (Real.exp (-(x i))) := by
    rw [exponentialPDF_of_nonneg (hx i).le]
    simp
  simp_rw [hi]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_pos (-(x i))).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]

/-- Integrating the actual independent exponentials by their total mass. -/
theorem lintegral_pi_expMeasure_one_massCoordinates (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1)) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s)) *
        ∫⁻ q in openSimplexCoordinates n s, f (massCoordinateVector n (s, q)) := by
  have hD := measurableSet_positiveCoordinateOrthant (n + 1)
  have hpdf : Measurable (fun x : Fin (n + 1) → ℝ ↦
      ∏ i, exponentialPDF 1 (x i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (measurable_exponentialPDFReal 1).ennreal_ofReal.comp (measurable_pi_apply i)
  conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem (ae_pos_pi_expMeasure_one (n + 1))]
  rw [pi_expMeasure_one_eq_withDensity, restrict_withDensity hD,
    lintegral_withDensity_eq_lintegral_mul _ hpdf hf]
  simp only [Pi.mul_apply]
  calc
    _ = ∫⁻ x in positiveCoordinateOrthant (n + 1),
        ENNReal.ofReal (Real.exp (-(∑ i, x i))) * f x := by
      apply setLIntegral_congr_fun hD
      intro x hx
      dsimp only
      rw [prod_exponentialPDF_one_of_pos (n + 1) hx]
    _ = _ := by
      rw [lintegral_positiveOrthant_massCoordinates n _ (by fun_prop)]
      simp_rw [sum_massCoordinateVector,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end OTSelector.Probability
