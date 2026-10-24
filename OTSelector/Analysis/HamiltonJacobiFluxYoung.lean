import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Analysis.HamiltonJacobiFluxYoung

Conditions: A positive scalar density, a Hamilton–Jacobi quadratic subsolution, and a current/covector pair; the integral version includes its explicit integrability assumptions.

Objects: A pointwise and integrated quadratic flux upper bound.

Proof detail: Apply the quadratic Fenchel–Young inequality after scaling by the density and combine it with the Hamilton–Jacobi upper bound. Integrate by order.

## Mathematical sources

- [Stephen Boyd, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108): Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94.
- [Rick Durrett, Probability](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.3 (Hölder), p. 29.

Source relation: Quadratic Fenchel–Young corollary in a real inner-product space; no PDE existence assertion is involved.
-/

/-!
# The actual Hamilton-Jacobi and weak-flux action inequality

The flux and gradient in this estimate are the same vectors as in the weak
continuity equation. No independence or newly chosen test derivative is used.
-/
open MeasureTheory
open scoped RealInnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The true Hamilton-Jacobi inequality and the quadratic Young inequality
give the pointwise bound for the same flux and gradient. -/
theorem hamiltonJacobi_flux_young (j p : V) {d r : ℝ} (hr : 0 < r)
    (hHJ : d + ‖p‖ ^ 2 / 2 ≤ 0) :
    d * r - inner ℝ j p ≤ ‖j‖ ^ 2 / r / 2 := by
  have hinner : -inner ℝ j p ≤ ‖j‖ * ‖p‖ :=
    (neg_le_abs _).trans (by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) j p)
  have hweighted := mul_le_mul_of_nonneg_right hHJ hr.le
  apply (le_of_mul_le_mul_right ?_ hr)
  rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hr.ne']
  nlinarith [sq_nonneg (‖j‖ - r * ‖p‖)]

/-- The actual integrated weak-continuity-equation rate is controlled by half
the literal action. The integrability premises are those of these same readouts. -/
theorem integral_hamiltonJacobi_flux_le
    [MeasurableSpace X] (μ : Measure X)
    (j p : X → V) (d r : X → ℝ)
    (hdr : Integrable (fun x ↦ d x * r x) μ)
    (hjp : Integrable (fun x ↦ inner ℝ (j x) (p x)) μ)
    (hact : Integrable (fun x ↦ ‖j x‖ ^ 2 / r x) μ)
    (hr : ∀ᵐ x ∂μ, 0 < r x)
    (hHJ : ∀ᵐ x ∂μ, d x + ‖p x‖ ^ 2 / 2 ≤ 0) :
    (∫ x, d x * r x ∂μ) - (∫ x, inner ℝ (j x) (p x) ∂μ) ≤
      (∫ x, ‖j x‖ ^ 2 / r x ∂μ) / 2 := by
  rw [← integral_sub hdr hjp, ← integral_div]
  apply integral_mono_ae (hdr.sub hjp) (hact.div_const 2)
  filter_upwards [hr, hHJ] with x hx hHx
  exact hamiltonJacobi_flux_young (j x) (p x) hx hHx

end OTSelector.Reconstruction
