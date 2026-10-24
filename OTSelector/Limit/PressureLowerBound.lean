import OTSelector.Limit.SupportedEmpiricalSelector
import OTSelector.Finite.FractionalGauge

/-!
# A uniform lower bound for the supported empirical pressure

Every tilted empirical assignment value is bounded below by `-|t| ‖f‖`, because
the base slack cost is nonnegative and the probe is bounded.  This supplies the
pointwise lower bound used by the abstract mean-convergence engine.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

noncomputable section
namespace OTSelector.Pressure
open Probability

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
/-- The supported empirical pressure is bounded below by `-|t| ‖f‖`. -/
theorem supportedDistancePressure_ge_neg_abs_mul
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (hn : 0 < n) (X Y : Fin n → M) (φ : M → ℝ) (hφ : LipschitzWith 1 φ)
    (k : ℝ) (hk : 0 ≤ k) (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    -(|t| * (‖f‖₊ : ℝ)) ≤
      supportedDistancePressure μ ν K hK hμ hν X Y φ k f t := by
  classical
  let probe : Fin n → Fin n → ℝ := fun i j ↦
    f (supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j))
  let cost : Fin n → Fin n → ℝ := fun i j ↦ k * distanceSlackEdgeCost X Y φ i j
  have hedge (i j : Fin n) : -(|t| * (‖f‖₊ : ℝ)) ≤ cost i j + t * probe i j := by
    have h1 : 0 ≤ cost i j :=
      mul_nonneg hk (distanceSlackEdgeCost_nonneg X Y φ hφ i j)
    have hb := BoundedContinuousFunction.nnnorm_coe_le_nnnorm f
      (supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j))
    have hb' : |probe i j| ≤ (‖f‖₊ : ℝ) := by
      have h' : ((‖f (supportProjection μ K hK hμ (X i),
          supportProjection ν K hK hν (Y j))‖₊ : ℝ) ≤ (‖f‖₊ : ℝ)) :=
        NNReal.coe_le_coe.mpr hb
      simpa only [probe, coe_nnnorm, Real.norm_eq_abs] using h'
    have h2 : -(|t| * (‖f‖₊ : ℝ)) ≤ t * probe i j := by
      have hmul : |t * probe i j| ≤ |t| * (‖f‖₊ : ℝ) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hb' (abs_nonneg t)
      exact (abs_le.mp hmul).1
    linarith
  have hsum : -((n : ℝ) * (|t| * (‖f‖₊ : ℝ))) ≤
      assignmentCost (perturbedEdgeCost cost probe t) (optimalAssignment (perturbedEdgeCost cost probe t)) := by
    have hconst : (∑ _i : Fin n, -(|t| * (‖f‖₊ : ℝ))) =
        -((n : ℝ) * (|t| * (‖f‖₊ : ℝ))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    calc
      -((n : ℝ) * (|t| * (‖f‖₊ : ℝ)))
          = ∑ _i : Fin n, -(|t| * (‖f‖₊ : ℝ)) := hconst.symm
      _ ≤ ∑ i, (cost i ((optimalAssignment (perturbedEdgeCost cost probe t)) i) +
            t * probe i ((optimalAssignment (perturbedEdgeCost cost probe t)) i)) :=
          Finset.sum_le_sum fun i _ ↦ hedge i _
      _ = assignmentCost (perturbedEdgeCost cost probe t)
            (optimalAssignment (perturbedEdgeCost cost probe t)) := by
          simp only [assignmentCost, perturbedEdgeCost]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold supportedDistancePressure perturbedAssignmentValue
  rw [le_div_iff₀ hnR]
  have hsum' : -(|t| * (‖f‖₊ : ℝ)) * (n : ℝ) ≤
      assignmentCost (perturbedEdgeCost cost probe t)
        (optimalAssignment (perturbedEdgeCost cost probe t)) := by
    linarith
  simpa only [cost, probe, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hsum'

end OTSelector.Pressure
