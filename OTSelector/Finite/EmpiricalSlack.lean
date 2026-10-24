import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.EmpiricalFractional
import OTSelector.Finite.FractionalGauge
import OTSelector.Finite.FractionalOptimal
import OTSelector.Finite.PerturbedValue
import OTSelector.Probability.EmpiricalMeasure
import OTSelector.Transport.Coupling.CostEquivalence

/-!
# Finite.EmpiricalSlack

**Conditions:** Positive sample sizes/scales and empirical distance-optimal couplings; the limit statement assumes pressure convergence and scale divergence.

**Objects:** The common integrated distance slack and the normalized zero-tilt assignment pressure.

**Proof detail:** Represent the coupling by its fractional matrix, use the gauge identity at zero tilt, and solve the exact scaling identity; convergence of a finite numerator divided by a diverging positive scale yields zero slack.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean), Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Exact empirical slack and its pressure normalization

Every original empirical distance optimum has the same integrated potential slack. Its scaled
value is exactly the actual zero-tilt finite assignment pressure, including fractional couplings
and repeated sample points. Consequently, finite convergence of that pressure and divergence of
the positive scale imply vanishing integrated slack. The potential may be arbitrary for these
identities; its one-Lipschitz property is used separately for calibration and population optimality.
-/

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace OTSelector

variable {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M] [PseudoMetricSpace M]

/-- The actual zero-tilt pressure is the scaled slack integral of every empirical optimum.
The probe is arbitrary because its coefficient is zero. No distinct-sample assumption is needed. -/
theorem perturbedDistanceSlackValue_zero_eq_integral
    {n : ℕ} [NeZero n] (X Y : Fin n → M) (φ : M → ℝ) (probe : M × M → ℝ)
    (k : ℝ) (hk : 0 < k) (γ : Measure (M × M))
    (hγ : IsOptimalCoupling edist (empiricalMeasure X) (empiricalMeasure Y) γ) :
    perturbedAssignmentValue (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
        (fun i j ↦ probe (X i, Y j)) 0 / (n : ℝ) =
      k * ∫ z, (dist z.1 z.2 - φ z.2 + φ z.1) ∂γ := by
  have hdist : (edist : M → M → ℝ≥0∞) = fun x y ↦ ENNReal.ofReal (dist x y) :=
    funext fun x ↦ funext fun y ↦ edist_dist x y
  rw [hdist] at hγ
  obtain ⟨P, hP, rfl⟩ :=
    (isOptimalCoupling_empirical_iff_exists_optimalFractional X Y dist
      (fun _ _ ↦ dist_nonneg) γ).mp hγ
  rw [integral_fractionalEmpiricalMeasure_of_singletons X Y P hP.1]
  let cost : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ k * distanceSlackEdgeCost X Y φ i j
  let test : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ probe (X i, Y j)
  have hscaled : OptimalFractionalAssignment cost P :=
    (optimalFractionalAssignment_distanceSlack_iff X Y φ P k hk).mpr hP
  have heq := perturbedEdgeCost_zero cost test
  have hPzero : OptimalFractionalAssignment (perturbedEdgeCost cost test 0) P :=
    Eq.mpr (congrArg (fun c ↦ OptimalFractionalAssignment c P) heq) hscaled
  have hzero : perturbedAssignmentValue cost test 0 = fractionalAssignmentCost cost P :=
    (perturbedAssignmentValue_eq_of_optimalFractional cost test P 0 hPzero).trans
      (congrArg (fun c ↦ fractionalAssignmentCost c P) heq)
  have hscale : fractionalAssignmentCost cost P =
      k * fractionalAssignmentCost (distanceSlackEdgeCost X Y φ) P := by
    simp only [cost, fractionalAssignmentCost, Finset.mul_sum, mul_left_comm]
  exact (congrArg (fun v ↦ v / (n : ℝ)) (hzero.trans hscale)).trans
    (mul_div_assoc k _ (n : ℝ))

/-- Dividing the normalized zero-tilt pressure by its scale recovers the unscaled slack exactly. -/
theorem integral_distanceSlack_eq_value_div
    {n : ℕ} [NeZero n] (X Y : Fin n → M) (φ : M → ℝ) (probe : M × M → ℝ)
    (k : ℝ) (hk : 0 < k) (γ : Measure (M × M))
    (hγ : IsOptimalCoupling edist (empiricalMeasure X) (empiricalMeasure Y) γ) :
    (∫ z, (dist z.1 z.2 - φ z.2 + φ z.1) ∂γ) =
      (perturbedAssignmentValue (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
        (fun i j ↦ probe (X i, Y j)) 0 / (n : ℝ)) / k := by
  rw [perturbedDistanceSlackValue_zero_eq_integral X Y φ probe k hk γ hγ]
  exact (mul_div_cancel_left₀ _ hk.ne').symm

/-- Finite pressure convergence and a diverging positive scale force vanishing calibration slack
for any family of original empirical optima. No measure-valued limit is assumed here. -/
theorem tendsto_integral_distanceSlack_of_pressure
    {ι : Type*} {l : Filter ι} (n : ι → ℕ) [∀ i, NeZero (n i)]
    (X Y : ∀ i, Fin (n i) → M) (φ : M → ℝ) (probe : M × M → ℝ)
    (k : ι → ℝ) (hk : ∀ i, 0 < k i) (γ : ι → Measure (M × M))
    (hγ : ∀ i, IsOptimalCoupling edist (empiricalMeasure (X i)) (empiricalMeasure (Y i)) (γ i))
    {p : ℝ} (hpressure : Tendsto (fun i ↦
      perturbedAssignmentValue (fun a b ↦ k i * distanceSlackEdgeCost (X i) (Y i) φ a b)
        (fun a b ↦ probe (X i a, Y i b)) 0 / (n i : ℝ)) l (𝓝 p))
    (hscale : Tendsto k l atTop) :
    Tendsto (fun i ↦ ∫ z, (dist z.1 z.2 - φ z.2 + φ z.1) ∂γ i) l (𝓝 0) := by
  have h := hpressure.div_atTop hscale
  apply h.congr
  intro i
  exact (integral_distanceSlack_eq_value_div (X i) (Y i) φ probe (k i) (hk i) (γ i) (hγ i)).symm

end OTSelector
