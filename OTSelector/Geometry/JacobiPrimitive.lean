import OTSelector.Geometry.Jacobi.HamiltonianSecondSolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual Jacobi compliance primitive

The compliance primitive is the matrix-valued interval integral of
`J⁻¹ * C * J⁻¹ᵀ`, based at an interior time. Its derivative follows from the
fundamental theorem of calculus, using differentiability of `J`, continuity of `C`,
and nonsingularity of `J` only on the open interval. Combining this primitive with
the Hamiltonian system and one initial Wronskian identity constructs a second solution.
No value, inverse, or limit of `J` at an endpoint is required. Continuation of the
second solution through the endpoints and its identification with Finsler Jacobi data
are separate geometric and ODE steps.
-/

open Matrix Set MeasureTheory
open scoped Matrix.Norms.Operator Interval

noncomputable section

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Reconcile the operator-norm instances with the entrywise matrix topology.
local instance : ENormedAddMonoid (Matrix n n ℝ) := by
  exact_mod_cast (NormedAddGroup.toENormedAddMonoid (F := Matrix n n ℝ))

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix n n ℝ) := by
  exact_mod_cast (PseudoEMetricSpace.pseudoMetrizableSpace (α := Matrix n n ℝ))

/-- The compliance primitive based at `c`, defined by the actual matrix interval integral. -/
noncomputable def jacobiCompliancePrimitive (J C : ℝ → Matrix n n ℝ) (c t : ℝ) :
    Matrix n n ℝ :=
  ∫ s in c..t, (J s)⁻¹ * C s * (J s)⁻¹ᵀ

/-- Interior nonsingularity makes the compliance integrand continuous on the open interval. -/
theorem continuousOn_jacobiComplianceIntegrand {J C : ℝ → Matrix n n ℝ} {a b : ℝ}
    (hJ : DifferentiableOn ℝ J (Ioo a b)) (hC : ContinuousOn C (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) :
    ContinuousOn (fun t ↦ (J t)⁻¹ * C t * (J t)⁻¹ᵀ) (Ioo a b) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have hJi := hasDerivAt_matrix_inverse
    ((hJ t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt (hd t ht)
  have hCi : ContinuousAt C t := (hC t ht).continuousAt (isOpen_Ioo.mem_nhds ht)
  exact (hJi.continuousAt.mul hCi).mul
    (hasDerivAt_matrix_transpose hJi).continuousAt

/-- Every integration segment between two interior times stays away from the endpoints. -/
theorem intervalIntegrable_jacobiComplianceIntegrand {J C : ℝ → Matrix n n ℝ}
    {a b c t : ℝ} (hJ : DifferentiableOn ℝ J (Ioo a b))
    (hC : ContinuousOn C (Ioo a b)) (hd : ∀ s ∈ Ioo a b, (J s).det ≠ 0)
    (hc : c ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    IntervalIntegrable (fun s ↦ (J s)⁻¹ * C s * (J s)⁻¹ᵀ) volume c t := by
  simpa using! ((continuousOn_jacobiComplianceIntegrand hJ hC hd).mono
    (ordConnected_Ioo.uIcc_subset hc ht)).intervalIntegrable (μ := volume)

/-- The derivative of the actual integral, with no endpoint nonsingularity hypothesis. -/
theorem hasDerivAt_jacobiCompliancePrimitive {J C : ℝ → Matrix n n ℝ}
    {a b c t : ℝ} (hJ : DifferentiableOn ℝ J (Ioo a b))
    (hC : ContinuousOn C (Ioo a b)) (hd : ∀ s ∈ Ioo a b, (J s).det ≠ 0)
    (hc : c ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    HasDerivAt (jacobiCompliancePrimitive J C c) ((J t)⁻¹ * C t * (J t)⁻¹ᵀ) t := by
  have hf := continuousOn_jacobiComplianceIntegrand hJ hC hd
  apply intervalIntegral.integral_hasDerivAt_right
  · simpa using! intervalIntegrable_jacobiComplianceIntegrand hJ hC hd hc ht
  · simpa using! hf.stronglyMeasurableAtFilter isOpen_Ioo t ht
  · exact (hf t ht).continuousAt (isOpen_Ioo.mem_nhds ht)

/-- The primitive vanishes at its base time without any regularity hypotheses. -/
@[simp] theorem jacobiCompliancePrimitive_self (J C : ℝ → Matrix n n ℝ) (c : ℝ) :
    jacobiCompliancePrimitive J C c c = 0 := by
  simp [jacobiCompliancePrimitive]

/-- The actual integral constructs a second Hamiltonian solution throughout the interior.
The Wronskian identity is assumed at only the base time and propagated by the system. -/
theorem hasDerivAt_integral_second_jacobi_solution
    {J P A B C : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hC : ContinuousOn C (Ioo a b)) (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0)
    (hc : c ∈ Ioo a b) (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s ↦ J s * jacobiCompliancePrimitive J C c s)
        (B t * (J t * jacobiCompliancePrimitive J C c t) +
          C t * (P t * jacobiCompliancePrimitive J C c t + (J t)⁻¹ᵀ)) t ∧
      HasDerivAt (fun s ↦ P s * jacobiCompliancePrimitive J C c s + (J s)⁻¹ᵀ)
        (-A t * (J t * jacobiCompliancePrimitive J C c t) -
          (B t)ᵀ * (P t * jacobiCompliancePrimitive J C c t + (J t)⁻¹ᵀ)) t := by
  have hJdiff : DifferentiableOn ℝ J (Ioo a b) :=
    fun s hs ↦ (hJ s hs).differentiableAt.differentiableWithinAt
  exact hasDerivAt_second_jacobi_solution (hJ t ht) (hP t ht)
    (hasDerivAt_jacobiCompliancePrimitive hJdiff hC hd hc ht) (hd t ht) (hCsym t ht)
    (wronskian_identity_on_Ioo hJ hP hA hCsym hc hinit t ht)

/-- The integral construction has the canonical initial position and momentum. -/
theorem integral_second_jacobi_solution_initial (J P C : ℝ → Matrix n n ℝ) (c : ℝ) :
    J c * jacobiCompliancePrimitive J C c c = 0 ∧
      P c * jacobiCompliancePrimitive J C c c + (J c)⁻¹ᵀ = (J c)⁻¹ᵀ := by
  simp

end OTSelector.Geometry
