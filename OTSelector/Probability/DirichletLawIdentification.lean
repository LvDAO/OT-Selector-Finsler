import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import OTSelector.MeasureTheory.CompactMixedMomentDetermination
import OTSelector.Probability.DirichletReference
import OTSelector.Probability.DirichletReferenceMoments

/-!
Conditions: A finite measure or measurable random vector supported a.e. on the compact simplex, with every actual natural mixed moment equal to the factorial Dirichlet value.

Objects: Equality of the whole original measure/pushforward law with the constructed Dirichlet reference probability.

Proof detail: Use the previously proved reference moments and compact polynomial moment determinacy to compare the two supported measures; the exponent-zero identity also fixes total mass.

References: Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163; D. H. Fremlin: Section 281E, Stone–Weierstrass theorem for a point-separating unital algebra.
Relation: A local compact moment-identification corollary. It uses all mixed moments and actual simplex support; matching only a mean or covariance would not meet its hypotheses.
-/


/-!
# Identifying an actual law from the Dirichlet mixed moments

The explicit reference probability has the factorial mixed moments. Compact
simplex moment determinacy therefore identifies an original random vector's
whole law once its actual moments have been computed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- The factorial mixed moments determine the standard Dirichlet reference law
among finite measures carried by the simplex. -/
theorem measure_eq_dirichletOne_of_mixed_moments (n : ℕ)
    (μ : Measure (Fin (n + 1) → ℝ)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ p ∂μ, p ∈ stdSimplex ℝ (Fin (n + 1)))
    (hmom : ∀ r : Fin (n + 1) → ℕ,
      (∫⁻ p, ∏ j, ENNReal.ofReal (p j) ^ r j ∂μ) =
        ENNReal.ofReal ((n.factorial : ℝ) * (∏ j, (r j).factorial : ℝ) /
          (n + ∑ j, r j).factorial)) : μ = dirichletOne n := by
  apply measure_eq_of_mixed_moments_of_isCompact μ (dirichletOne n)
    (isCompact_stdSimplex ℝ (Fin (n + 1))) hμ (ae_mem_stdSimplex_dirichletOne n)
  intro r
  have hconvert (η : Measure (Fin (n + 1) → ℝ))
      (hη : ∀ᵐ p ∂η, p ∈ stdSimplex ℝ (Fin (n + 1))) :
      (∫ p, ∏ j, p j ^ r j ∂η) =
        (∫⁻ p, ∏ j, ENNReal.ofReal (p j) ^ r j ∂η).toReal := by
    have hnonneg : ∀ᵐ p ∂η, 0 ≤ ∏ j, p j ^ r j :=
      hη.mono fun p hp ↦ Finset.prod_nonneg fun j _ ↦ pow_nonneg (hp.1 j) _
    have hm : Measurable (fun p : Fin (n + 1) → ℝ ↦ ∏ j, p j ^ r j) := by fun_prop
    rw [integral_eq_lintegral_of_nonneg_ae hnonneg hm.aestronglyMeasurable]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hη] with p hp
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ pow_nonneg (hp.1 j) _)]
    exact Finset.prod_congr rfl fun j _ ↦ ENNReal.ofReal_pow (hp.1 j) _
  rw [hconvert μ hμ, hconvert (dirichletOne n) (ae_mem_stdSimplex_dirichletOne n),
    hmom r, lintegral_dirichletOne_nat_powers n r]

/-- A measurable original random simplex vector with the factorial mixed
moments has the explicit Dirichlet law on its original probability space. -/
theorem map_eq_dirichletOne_of_mixed_moments {W : Type*} [MeasurableSpace W]
    (n : ℕ) (P : Measure W) [IsFiniteMeasure P]
    (p : W → Fin (n + 1) → ℝ) (hp : Measurable p)
    (hsimplex : ∀ᵐ w ∂P, p w ∈ stdSimplex ℝ (Fin (n + 1)))
    (hmom : ∀ r : Fin (n + 1) → ℕ,
      (∫⁻ w, ∏ j, ENNReal.ofReal (p w j) ^ r j ∂P) =
        ENNReal.ofReal ((n.factorial : ℝ) * (∏ j, (r j).factorial : ℝ) /
          (n + ∑ j, r j).factorial)) : P.map p = dirichletOne n := by
  apply measure_eq_dirichletOne_of_mixed_moments n (P.map p)
    ((ae_map_iff hp.aemeasurable (isClosed_stdSimplex ℝ (Fin (n + 1))).measurableSet).mpr
      hsimplex)
  intro r
  rw [lintegral_map (by fun_prop) hp]
  exact hmom r

end OTSelector.Probability
