import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import OTSelector.Analysis.Sobolev.MeasureWeakNeumannFlux
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
import OTSelector.Transport.PositiveDensityInterpolationAction
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalDensityNeumannInterpolation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalDensityNeumannInterpolation`; the selected original proof blocks follow. -/
section

/-!
Conditions: Integrable endpoint densities have a common strictly positive lower bound, and their actual smooth-test discrepancy is bounded by the gradient L2 norm.

Objects: A weak affine density interpolation with the exact continuity pairings and bounded space-time action.

Proof detail: Construct the Hilbert flux, differentiate the affine density test integral and dominate inverse interpolated density by the positive lower bound.

Sources: Terence Tao, Section 1.4, Theorem 1.4.13, p. 53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=62); D. H. Fremlin, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40 (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27); Gabriel Peyré, Section 7.1, equations (7.1)–(7.5), pp. 112–113 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=116).
Relation: Locally proved weak interpolation/action estimate. This module does not itself extract an endpoint coupling.
-/

/-!
# A genuine weak interpolation of the original positive residual densities

The endpoint measures, weak continuity equation and bounded space-time action
are all constructed from the same two densities and the actual gradient bound.
This is the weak analytic part of the repair; extraction of an endpoint transport
coupling remains a separate construction.
-/
open Set MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The original test times an integrable original density is integrable. -/
theorem smoothTest_mul_density_integrable
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ))
    (φ : 𝓓_{K}(ι → ℝ, ℝ)) {f : (ι → ℝ) → ℝ} (hf : Integrable f μ) :
    Integrable (fun x ↦ φ x * f x) μ :=
  hf.mul_of_top_right
    (BoundedContinuousFunction.memLp_top
      (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ φ))

omit [DecidableEq ι] in
/-- The positive original density defines exactly the intended test integral. -/
theorem originalDensity_test_integral
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ))
    (φ : 𝓓_{K}(ι → ℝ, ℝ)) {f : (ι → ℝ) → ℝ}
    (hf : AEMeasurable f μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫ x, φ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
      ∫ x, φ x * f x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hf.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hpos] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

omit [DecidableEq ι] in
/-- The literal interpolated density has the exact affine smooth-test mean. -/
theorem residualDensityInterpolation_test_integral
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ))
    (φ : 𝓓_{K}(ι → ℝ, ℝ)) {f g : (ι → ℝ) → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (τ : ℝ) :
    (∫ x, φ x * residualDensityInterpolation f g τ x ∂μ) =
      (1 - τ) * (∫ x, φ x * f x ∂μ) + τ * ∫ x, φ x * g x ∂μ := by
  have hfi := smoothTest_mul_density_integrable K μ φ hf
  have hgi := smoothTest_mul_density_integrable K μ φ hg
  have heq (x : ι → ℝ) :
      φ x * residualDensityInterpolation f g τ x =
        (1 - τ) * (φ x * f x) + τ * (φ x * g x) := by
    dsimp only [residualDensityInterpolation]
    ring
  simp_rw [heq]
  rw [integral_add (hfi.const_mul _) (hgi.const_mul _), integral_const_mul,
    integral_const_mul]

omit [DecidableEq ι] in
/-- The time derivative of every actual smooth-test mean is the difference of
its original endpoint density means. -/
theorem hasDerivAt_residualDensityInterpolation_test
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ))
    (φ : 𝓓_{K}(ι → ℝ, ℝ)) {f g : (ι → ℝ) → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (τ : ℝ) :
    HasDerivAt (fun σ ↦ ∫ x, φ x * residualDensityInterpolation f g σ x ∂μ)
      ((∫ x, φ x * g x ∂μ) - ∫ x, φ x * f x ∂μ) τ := by
  simp_rw [residualDensityInterpolation_test_integral K μ φ hf hg]
  have hlin : HasDerivAt
      (fun σ : ℝ ↦ (1 - σ) * (∫ x, φ x * f x ∂μ) + σ * ∫ x, φ x * g x ∂μ)
      ((0 - 1) * (∫ x, φ x * f x ∂μ) + 1 * ∫ x, φ x * g x ∂μ) τ :=
    (((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id τ)).mul_const
      (∫ x, φ x * f x ∂μ)).add
        ((hasDerivAt_id τ).mul_const (∫ x, φ x * g x ∂μ))
  convert hlin using 1
  ring

/-- Construct the same-density weak continuity equation and its actual
unit-time action estimate from the original residual gradient bound. -/
theorem exists_originalDensity_weakNeumannInterpolation
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (f g : (ι → ℝ) → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hfl : ∀ᵐ x ∂μ, ρ ≤ f x) (hgl : ∀ᵐ x ∂μ, ρ ≤ g x)
    (hbound : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x * f x ∂μ) - ∫ x, φ x * g x ∂μ‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μ φ‖) :
    ∃ j : Lp (EuclideanSpace ℝ ι) 2 μ,
      Integrable (fun x ↦ ‖j x‖ ^ 2) μ ∧ (∫ x, ‖j x‖ ^ 2 ∂μ) ≤ C ^ 2 ∧
      (∀ (φ : 𝓓_{K}(ι → ℝ, ℝ)) (τ : ℝ),
        HasDerivAt (fun σ ↦ ∫ x, φ x * residualDensityInterpolation f g σ x ∂μ)
          (-(∫ x, inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ φ x)) ∂μ)) τ) ∧
      Integrable (residualInterpolationAction j f g)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod μ) ∧
      (∫ z, residualInterpolationAction j f g z
        ∂(volume.restrict (Icc (0 : ℝ) 1)).prod μ) ≤ ρ⁻¹ * C ^ 2 := by
  have hfp := hfl.mono fun _ hx ↦ hρ.le.trans hx
  have hgp := hgl.mono fun _ hx ↦ hρ.le.trans hx
  have : IsFiniteMeasure (μ.withDensity fun x ↦ ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  have : IsFiniteMeasure (μ.withDensity fun x ↦ ENNReal.ofReal (g x)) :=
    isFiniteMeasure_withDensity_ofReal hg.2
  obtain ⟨j, hj, hjI, hjE, _⟩ := exists_originalMeasure_weakNeumannFlux K μ
    (μ.withDensity fun x ↦ ENNReal.ofReal (f x))
    (μ.withDensity fun x ↦ ENNReal.ofReal (g x)) hC (by
      intro φ
      simpa only [originalDensity_test_integral K μ φ hf.aemeasurable hfp,
        originalDensity_test_integral K μ φ hg.aemeasurable hgp] using hbound φ)
  have hjtest (φ : 𝓓_{K}(ι → ℝ, ℝ)) :
      (∫ x, inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ φ x)) ∂μ) =
        (∫ x, φ x * f x ∂μ) - ∫ x, φ x * g x ∂μ := by
    simpa only [originalDensity_test_integral K μ φ hf.aemeasurable hfp,
      originalDensity_test_integral K μ φ hg.aemeasurable hgp] using hj φ
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hν : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  have hτ : ∀ᵐ τ ∂ν, τ ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  obtain ⟨hactI, hactE⟩ := residualInterpolationAction_integrable_and_integral_le
    μ ν j (Lp.memLp j) f g hf.aemeasurable hg.aemeasurable hρ hτ hfl hgl
  refine ⟨j, hjI, hjE, ?_, hactI, hactE.trans ?_⟩
  · intro φ τ
    convert hasDerivAt_residualDensityInterpolation_test K μ φ hf hg τ using 1
    rw [hjtest]
    ring
  · exact mul_le_mul_of_nonneg_left hjE (inv_nonneg.mpr hρ.le)

end OTSelector.Reconstruction

end
end
