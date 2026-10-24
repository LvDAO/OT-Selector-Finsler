import OTSelector.Geometry.FocalConditionalPowerMomentsGlobal
import OTSelector.Geometry.FocalConditionalMomentsPositive

/-!
# Conditional moments from one closed actual Hamiltonian system

The closed-system package records the data produced by an actual smooth graph
phase. Focal endpoints are permitted: only the joint position-momentum map has
full rank there. The consumer derives the endpoint crossing and both kinds of
conditional moment, without separate endpoint assumptions.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator MatrixOrder ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The fixed-frame Hamiltonian data on a closed interval, with finite focal ends allowed. -/
structure ClosedHamiltonianJacobiSystem
    (J P A B C : ℝ → Matrix n n ℝ) (a b : ℝ) : Prop where
  position_derivative : ∀ t ∈ Icc a b, HasDerivAt J (B t * J t + C t * P t) t
  momentum_derivative : ∀ t ∈ Icc a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t
  continuous_A : ContinuousOn A (Icc a b)
  continuous_B : ContinuousOn B (Icc a b)
  continuous_C : ContinuousOn C (Icc a b)
  symmetric_A : ∀ t ∈ Icc a b, (A t)ᵀ = A t
  symmetric_C : ∀ t ∈ Icc a b, (C t)ᵀ = C t
  positive_C : ∀ t ∈ Icc a b, (C t).PosDef
  wronskian : ∀ t ∈ Icc a b, (J t)ᵀ * P t = (P t)ᵀ * J t
  phase_rank : ∀ t ∈ Icc a b, ∀ v, J t *ᵥ v = 0 → P t *ᵥ v = 0 → v = 0

/-- A single actual closed system supplies both the spectral determinant moment
and every positive power moment below two under the same finite conditional law. -/
theorem ClosedHamiltonianJacobiSystem.conditional_moments
    {J P A B C : ℝ → Matrix n n ℝ} {a b c θ : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ = (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|))) :
    Integrable (fun t ↦ (1 + CFC.abs (jacobiCompliancePrimitive J C c t)).det) μ ∧
      ∀ r : ℝ, 0 < r → r < 2 →
        Integrable (fun t ↦ ‖jacobiCompliancePrimitive J C c t‖ ^ r) μ := by
  have hab : a ≤ b := (hc.1.trans hc.2).le
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hJ := fun t (ht : t ∈ Ioo a b) ↦ H.position_derivative t (Ioo_subset_Icc_self ht)
  have hP := fun t (ht : t ∈ Ioo a b) ↦ H.momentum_derivative t (Ioo_subset_Icc_self ht)
  have hA := fun t (ht : t ∈ Ioo a b) ↦ H.symmetric_A t (Ioo_subset_Icc_self ht)
  have hC := fun t (ht : t ∈ Ioo a b) ↦ H.symmetric_C t (Ioo_subset_Icc_self ht)
  have hinit := H.wronskian c (Ioo_subset_Icc_self hc)
  refine ⟨integrable_abs_jacobi_determinant_of_conditional_density
    hJ hP H.continuous_A H.continuous_B H.continuous_C hA
    (fun t ht ↦ (H.positive_C t (Ioo_subset_Icc_self ht)).posSemidef)
    hd hc hinit hρ hw hρ0 hρR hw0 hθ hμ, ?_⟩
  intro r hr0 hr
  exact integrable_jacobiCompliance_rpow_of_hamiltonian_endpoints
    hJ hP H.continuous_A H.continuous_B H.continuous_C hA hC hd hc hinit
    (H.position_derivative a ha).hasDerivWithinAt
    (H.position_derivative b hb).hasDerivWithinAt
    (H.wronskian a ha) (H.wronskian b hb) (H.phase_rank a ha) (H.phase_rank b hb)
    (H.positive_C a ha) (H.positive_C b hb) hρ hw hρ0 hρR hw0 hθ hμ hr0 hr

end OTSelector.Reconstruction
