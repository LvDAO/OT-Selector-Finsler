import OTSelector.Probability.MarkedDePoissonization
import OTSelector.Finite.MaxCardValueAssignment

/-!
# The fixed marked-cube value is the physical assignment value

`markedFixedValue` is the least cost over maximum-cardinality matchings of the
`n × n` tilted matrix of marked-cube edge costs.  On an `n × n` matrix the
maximum-cardinality matchings are exactly the graphs of permutations, so the
marked value coincides with the Dirichlet semidiscrete assignment value
`perturbedAssignmentValue` used by the physical pressure.

This is the exact bridge between the marked-cube Poisson/tile pressure machinery
and the physical semidiscrete mean.
-/

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The physical assignment value of the marked cube at sample size `n`. -/
theorem markedFixedValue_eq_perturbedAssignmentValue
    (q : ℕ) (r t : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (n : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    markedFixedValue q r t kin g n ω =
      perturbedAssignmentValue
        (fun i j : Fin n => mKineticCost q r kin ω (i : ℕ) (j : ℕ))
        (fun i j : Fin n => mProbe g ω (i : ℕ) (j : ℕ)) t := by
  unfold markedFixedValue
  rw [show (fun i : Fin n => fun j : Fin n =>
      mKineticCost q r kin ω (i : ℕ) (j : ℕ) + t * mProbe g ω (i : ℕ) (j : ℕ)) =
      perturbedEdgeCost
        (fun i j : Fin n => mKineticCost q r kin ω (i : ℕ) (j : ℕ))
        (fun i j : Fin n => mProbe g ω (i : ℕ) (j : ℕ)) t from rfl]
  exact PartialMatching.maxCardValue_eq_perturbedAssignmentValue _ _ _

end OTSelector.Probability
