import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import OTSelector.MeasureTheory.SimplexCoordinateVolume
import OTSelector.Probability.DirichletCoordinateDensity
import OTSelector.Probability.DirichletLawIdentification
import OTSelector.Probability.DirichletReference
import OTSelector.Probability.DirichletReferenceMoments

/-!
Conditions: The constructed Dirichlet(1,…,1) law and an arbitrary permutation or omitted simplex coordinate.

Objects: Permutation invariance and the uniform coordinate-simplex density after omitting any selected coordinate.

Proof detail: Permuting the monomial exponents preserves the factorial moments, so compact moment determinacy gives the law equality. Compose with the known last-coordinate projection density.

References: Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163; Thomas P. Minka: Section 1, equations (1)–(3), p. 1; equations (19)–(20), p. 2.
Relation: Exchangeability follows from the symmetric Dirichlet density, but Lean derives the exact pushforward through actual moments and compact determinacy rather than assuming exchangeability of its recursive construction.
-/


/-!
# Symmetry and arbitrary simplex coordinate gauges

The explicit beta construction is invariant under every permutation of target
labels. Consequently any one mass coordinate can be omitted in the uniform
simplex density formula, as needed when a target serves as the price root.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- The standard Dirichlet reference probability is invariant under all target
label permutations. -/
theorem map_dirichletOne_permutation (n : ℕ) (e : Equiv.Perm (Fin (n + 1))) :
    (dirichletOne n).map (fun p j ↦ p (e j)) = dirichletOne n := by
  have hm : Measurable (fun p : Fin (n + 1) → ℝ ↦ fun j ↦ p (e j)) :=
    measurable_pi_lambda _ fun j ↦ measurable_pi_apply (e j)
  apply map_eq_dirichletOne_of_mixed_moments n _ _ hm
  · filter_upwards [ae_mem_stdSimplex_dirichletOne n] with p hp
    exact ⟨fun j ↦ hp.1 (e j), (Equiv.sum_comp e p).trans hp.2⟩
  · intro r
    have hprod (p : Fin (n + 1) → ℝ) :
        (∏ j, ENNReal.ofReal (p (e j)) ^ r j) =
          ∏ j, ENNReal.ofReal (p j) ^ r (e.symm j) := by
      simpa only [Equiv.symm_apply_apply] using
        Equiv.prod_comp e (fun j ↦ ENNReal.ofReal (p j) ^ r (e.symm j))
    simp_rw [hprod]
    rw [lintegral_dirichletOne_nat_powers n (fun j ↦ r (e.symm j)),
      Equiv.sum_comp e.symm r, Equiv.prod_comp e.symm (fun j ↦ ((r j).factorial : ℝ))]

/-- Deleting any designated mass coordinate gives the same constant density in
the remaining coordinates, ordered by `Fin.succAbove`. -/
theorem map_succAbove_dirichletOne (n : ℕ) (k : Fin (n + 1)) :
    (dirichletOne n).map (fun p j ↦ p (k.succAbove j)) =
      (n.factorial : ℝ≥0∞) • volume.restrict (openSimplexCoordinates n 1) := by
  let e : Equiv.Perm (Fin (n + 1)) :=
    (finSuccEquiv' (Fin.last n)).trans (finSuccEquiv' k).symm
  have he (j : Fin n) : e j.castSucc = k.succAbove j := by
    simp only [e, Equiv.trans_apply, finSuccEquiv'_last_apply_castSucc,
      finSuccEquiv'_symm_some]
  have hfun : (fun p : Fin (n + 1) → ℝ ↦ fun j ↦ p (k.succAbove j)) =
      simplexCoordinates n ∘ (fun p j ↦ p (e j)) := by
    funext p j
    exact congrArg p (he j).symm
  rw [hfun, ← Measure.map_map (measurable_simplexCoordinates n)
    (measurable_pi_lambda _ fun j ↦ measurable_pi_apply (e j)),
    map_dirichletOne_permutation, map_simplexCoordinates_dirichletOne]

end OTSelector.Probability
