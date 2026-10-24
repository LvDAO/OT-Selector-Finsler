import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import OTSelector.MeasureTheory.SimplexCoordinateVolume
import OTSelector.MeasureTheory.SimplexMassCoordinates
import OTSelector.Probability.DirichletReference
import OTSelector.Probability.ExponentialProductDensity
import OTSelector.Probability.GammaSimplexDensity
import OTSelector.Probability.SimplexBarycentricCoordinates

/-!
Conditions: An independent Gamma(n+1,1) total mass and the actual Dirichlet(1,…,1) vector, including the one-coordinate case.

Objects: The scaled vector’s whole pushforward law equals the genuine product of n+1 mean-one exponential laws.

Proof detail: Insert the proved Dirichlet coordinate density, rescale its simplex by the positive total, and cancel the integer gamma factorial density against the simplex normalization and Jacobian.

References: Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163; Günter Last and Mathew Penrose: Section 1.4, equations (1.23), (1.27)–(1.28), p. 6.
Relation: The classical gamma/Dirichlet factorization is proved as equality of measures. Independence is part of the stated input product experiment, while the exponential-coordinate product law is the conclusion.
-/


/-!
# Scaling a Dirichlet vector by an independent gamma total

The uniform simplex density and its scalar change of variables identify the
scaled vector with the genuine product of mean-one exponential laws. This is
an equality of measures, including the zero-dimensional simplex.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- Restore the total mass of a normalized vector. -/
def scaleSimplex (n : ℕ) (z : ℝ × (Fin (n + 1) → ℝ)) : Fin (n + 1) → ℝ :=
  z.1 • z.2

theorem measurable_scaleSimplex (n : ℕ) : Measurable (scaleSimplex n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_fst.mul ((measurable_pi_apply i).comp measurable_snd)

theorem scaleSimplex_barycentric (n : ℕ) (s : ℝ) (q : Fin n → ℝ) :
    scaleSimplex n (s, simplexBarycentric n q) = massCoordinateVector n (s, s • q) := by
  exact smul_simplexBarycentric n s q

/-- The gamma density cancels the simplex dilation factor exactly. -/
theorem lintegral_gamma_dirichlet_scale (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (scaleSimplex n z)
      ∂(gammaMeasure ((n : ℝ) + 1) 1).prod (dirichletOne n)) =
      ∫⁻ x, f x ∂Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1) := by
  have hscale : Measurable (fun z ↦ f (scaleSimplex n z)) :=
    hf.comp (measurable_scaleSimplex n)
  have hmass : Measurable (fun z ↦ f (massCoordinateVector n z)) :=
    hf.comp (volume_preserving_massCoordinateVector n).measurable
  rw [lintegral_prod _ hscale.aemeasurable,
    lintegral_gammaMeasure_Ioi _ _ _ hscale.lintegral_prod_right]
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-s)) *
          ∫⁻ q in openSimplexCoordinates n s, f (massCoordinateVector n (s, q)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      dsimp only
      rw [lintegral_dirichletOne_barycentric n (fun p ↦ f (scaleSimplex n (s, p)))
        (hscale.comp measurable_prodMk_left)]
      rw [← mul_assoc, gammaPDF_nat_succ_one_mul_factorial n hs.le]
      simp_rw [scaleSimplex_barycentric]
      rw [mul_comm (ENNReal.ofReal (s ^ n)), mul_assoc]
      rw [mul_lintegral_smul_openSimplexCoordinates n hs
        (fun q ↦ f (massCoordinateVector n (s, q)))
        (hmass.comp measurable_prodMk_left)]
    _ = _ := (lintegral_pi_expMeasure_one_massCoordinates n f hf).symm

/-- Independent gamma scaling of the reference simplex law produces independent
mean-one exponentials. -/
theorem map_gamma_dirichlet_scale_eq_pi_exp (n : ℕ) :
    ((gammaMeasure ((n : ℝ) + 1) 1).prod (dirichletOne n)).map (scaleSimplex n) =
      Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_scaleSimplex n)]
  exact lintegral_gamma_dirichlet_scale n f hf

end OTSelector.Probability
