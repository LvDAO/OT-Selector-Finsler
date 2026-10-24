import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import OTSelector.Analysis.InnerProductSpace.GradientRepresentation
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalMeasureWeakNeumannFlux.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalMeasureWeakNeumannFlux`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite endpoint/reference measures and an actual discrepancy functional bounded by C times the physical-gradient L2 norm on the stated smooth test space.

Objects: A genuine minimum-energy weak Neumann flux with the exact original test pairings and energy at most C².

Proof detail: Factor the discrepancy through the gradient range, extend to its Hilbert closure and apply Riesz; orthogonal projection gives minimum norm.

Sources: Terence Tao, Section 1.4, Theorem 1.4.13, p. 53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=62); Terence Tao, Section 1.5.2, Theorem 1.5.6, p. 63 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=72); Terence Tao, Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=61).
Relation: Hilbert representation applied to a gradient seminorm. It constructs a weak flux, without claiming additional elliptic regularity or a boundary trace.
-/

/-!
# Weak Neumann flux for the actual residual measures

The discrepancy below is the literal difference of the two original residual
measure integrals. The Hilbert representative satisfies the original physical
coordinate gradient pairing and has bounded actual integrated square norm.
-/
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual residual discrepancy on the original smooth tests. -/
def originalMeasureDiscrepancy (K : Compacts (ι → ℝ))
    (ν₀ ν₁ : Measure (ι → ℝ)) [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] :
    𝓓_{K}(ι → ℝ, ℝ) →ₗ[ℝ] ℝ where
  toFun φ := (∫ x, φ x ∂ν₀) - ∫ x, φ x ∂ν₁
  map_add' φ ψ := by
    have hi (ν : Measure (ι → ℝ)) [IsFiniteMeasure ν] (f : 𝓓_{K}(ι → ℝ, ℝ)) :
        Integrable f ν :=
      BoundedContinuousFunction.integrable ν
        (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ f)
    simp only [FunLike.coe_add, Pi.add_apply,
      integral_add (hi ν₀ φ) (hi ν₀ ψ), integral_add (hi ν₁ φ) (hi ν₁ ψ)]
    ring
  map_smul' a φ := by
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      integral_const_mul, RingHom.id_apply]
    ring

omit [DecidableEq ι] in
@[simp]
theorem originalMeasureDiscrepancy_apply (K : Compacts (ι → ℝ))
    (ν₀ ν₁ : Measure (ι → ℝ)) [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    (φ : 𝓓_{K}(ι → ℝ, ℝ)) :
    originalMeasureDiscrepancy K ν₀ ν₁ φ = (∫ x, φ x ∂ν₀) - ∫ x, φ x ∂ν₁ := rfl

/-- A bound for the literal discrepancy against the actual physical gradient
constructs a weak Neumann flux. Its energy is an actual physical integral, and
it has minimum energy among fluxes with those same original test pairings. -/
theorem exists_originalMeasure_weakNeumannFlux
    (K : Compacts (ι → ℝ)) (μ ν₀ ν₁ : Measure (ι → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x ∂ν₀) - ∫ x, φ x ∂ν₁‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μ φ‖) :
    ∃ j : Lp (EuclideanSpace ℝ ι) 2 μ,
      (∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
        ∫ x, inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ φ x)) ∂μ =
          (∫ x, φ x ∂ν₀) - ∫ x, φ x ∂ν₁) ∧
      Integrable (fun x ↦ ‖j x‖ ^ 2) μ ∧
      (∫ x, ‖j x‖ ^ 2 ∂μ) ≤ C ^ 2 ∧
      ∀ other : Lp (EuclideanSpace ℝ ι) 2 μ,
        (∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
          ∫ x, inner ℝ (other x) (physicalCoordinateGradient ι (fderiv ℝ φ x)) ∂μ =
            (∫ x, φ x ∂ν₀) - ∫ x, φ x ∂ν₁) →
        (∫ x, ‖j x‖ ^ 2 ∂μ) ≤ ∫ x, ‖other x‖ ^ 2 ∂μ := by
  obtain ⟨j, hj, hjnorm, hjmin⟩ := exists_weakFlux_of_gradient_bound
    (smoothPhysicalGradientLtwo K μ) (originalMeasureDiscrepancy K ν₀ ν₁) hC hbound
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · intro φ
    rw [← inner_smoothPhysicalGradientLtwo]
    exact hj φ
  · exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable j)).mp (Lp.memLp j)
  · rw [← physicalFlux_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg j) hjnorm 2
  · intro other hother
    rw [← physicalFlux_norm_sq, ← physicalFlux_norm_sq]
    apply pow_le_pow_left₀ (norm_nonneg j) (hjmin other ?_) 2
    intro φ
    rw [inner_smoothPhysicalGradientLtwo]
    exact hother φ

end OTSelector.Reconstruction

end
end
