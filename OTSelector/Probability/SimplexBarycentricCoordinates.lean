import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import OTSelector.MeasureTheory.SimplexCoordinateVolume
import OTSelector.Probability.DirichletCoordinateDensity
import OTSelector.Probability.DirichletReference

/-!
Conditions: Finite simplex coordinate spaces; the inverse reconstruction only requires the displayed sum-to-one identity, and integral formulas use measurable nonnegative tests.

Objects: The complementary last-coordinate barycentric map, its exact inverse identities, the full-vector Dirichlet integral and its scalar rescaling.

Proof detail: Append 1−Σq, verify the two finite-coordinate identities and transfer the proved coordinate density back through the actual inverse on the reference support.

References: Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163; D. H. Fremlin: Section 235G, integration along an inverse-measure-preserving map.
Relation: Elementary coordinate inversion for the same normalized simplex law. The omitted coordinate is reconstructed algebraically, without a new distributional premise.
-/


/-!
# Recovering the full Dirichlet vector from independent coordinates

Appending the complementary mass inverts the coordinate projection on the
simplex. This supplies the full-vector integral formula needed for the
independent exponential representation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- Append the mass left after the independent coordinates. -/
def simplexBarycentric (n : ℕ) (q : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc q (1 - ∑ i, q i)

theorem measurable_simplexBarycentric (n : ℕ) : Measurable (simplexBarycentric n) := by
  apply measurable_pi_lambda
  intro j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [simplexBarycentric, Fin.snoc_last]
    fun_prop
  · simpa only [simplexBarycentric, Fin.snoc_castSucc] using measurable_pi_apply i

theorem simplexCoordinates_barycentric (n : ℕ) (q : Fin n → ℝ) :
    simplexCoordinates n (simplexBarycentric n q) = q := by
  ext i
  simp [simplexCoordinates, simplexBarycentric]

theorem simplexBarycentric_coordinates {n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : ∑ i, p i = 1) : simplexBarycentric n (simplexCoordinates n p) = p := by
  have hlast : 1 - ∑ i : Fin n, p i.castSucc = p (Fin.last n) := by
    rw [Fin.sum_univ_castSucc] at hp
    linarith
  change Fin.snoc (Fin.init p) (1 - ∑ i : Fin n, p i.castSucc) = p
  rw [hlast, Fin.snoc_init_self]

/-- Integrals of the full reference vector can be computed in the independent
coordinates with the exact uniform density. -/
theorem lintegral_dirichletOne_barycentric (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂dirichletOne n) =
      (n.factorial : ℝ≥0∞) *
        ∫⁻ q in openSimplexCoordinates n 1, f (simplexBarycentric n q) := by
  calc
    _ = ∫⁻ p, f (simplexBarycentric n (simplexCoordinates n p)) ∂dirichletOne n := by
      apply lintegral_congr_ae
      filter_upwards [ae_mem_stdSimplex_dirichletOne n] with p hp
      rw [simplexBarycentric_coordinates hp.2]
    _ = _ := lintegral_dirichletOne_simplexCoordinates n _
      (hf.comp (measurable_simplexBarycentric n))

/-- Rescaling the simplex multiplies the first coordinates and leaves their
complement equal to the total mass minus their sum. -/
theorem smul_simplexBarycentric (n : ℕ) (s : ℝ) (q : Fin n → ℝ) :
    s • simplexBarycentric n q = Fin.snoc (s • q) (s - ∑ i, s * q i) := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Pi.smul_apply, smul_eq_mul, simplexBarycentric, Fin.snoc_last,
      ← Finset.mul_sum]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul, simplexBarycentric, Fin.snoc_castSucc]

end OTSelector.Probability
