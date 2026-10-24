import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
## Lemma skeleton

* **Conditions:** A finite real coordinate type, compactly supported smooth real tests on the original product-norm space, and a finite measure for the L2 embedding.
* **Objects:** Coordinate gradient, bounded-continuous gradient and its Euclidean-valued L2 representative; inner-product and norm-square readout identities.
* **Proof detail:** Apply the Frechet derivative to coordinate basis vectors, pack the values into Euclidean space, use compact support to bound the gradient, and apply standard L2 representative formulas.

## Mathematical sources

* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 8A, Theorem 8.11, p. 218; Example 8.14, p. 219 (L2 Cauchy–Schwarz).
  https://measure.axler.net/MIRA.pdf#page=233
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).
  https://measure.axler.net/MIRA.pdf#page=211

**Relationship to the sources:** Concrete coordinate/representation implementation combining the derivative API with finite-dimensional L2. The input coordinate norm is not changed to a Euclidean norm.
-/

/-!
# Actual smooth-test gradients in the physical-coordinate L² space

Physical coordinates keep their original product norm. Only the gradient values
are packed into Euclidean space, so the flux Hilbert norm is the sum of the
squares of the original coordinate components.
-/
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Pack the original coordinate evaluations of a physical covector into the
Euclidean gradient, without changing the physical coordinate domain. -/
def physicalCoordinateGradient : ((ι → ℝ) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1))

@[simp]
theorem physicalCoordinateGradient_apply (L : (ι → ℝ) →L[ℝ] ℝ) (i : ι) :
    physicalCoordinateGradient ι L i = L (Pi.single i 1) := rfl

variable {ι}

/-- The actual gradient of an original compactly supported smooth test function
as a bounded continuous vector field in the same physical coordinates. -/
def smoothPhysicalGradient (K : Compacts (ι → ℝ)) :
    𝓓_{K}(ι → ℝ, ℝ) →ₗ[ℝ] ((ι → ℝ) →ᵇ EuclideanSpace ℝ ι) :=
  (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ).comp
    ((ContDiffMapSupportedIn.postcompLM (physicalCoordinateGradient ι)).comp
      (ContDiffMapSupportedIn.fderivLM ℝ ⊤ 0))

@[simp]
theorem smoothPhysicalGradient_apply (K : Compacts (ι → ℝ))
    (φ : 𝓓_{K}(ι → ℝ, ℝ)) (x : ι → ℝ) (i : ι) :
    smoothPhysicalGradient K φ x i = fderiv ℝ φ x (Pi.single i 1) := by
  simp [smoothPhysicalGradient, ContDiffMapSupportedIn.fderivLM_apply]

/-- Embed the actual smooth gradient into the Hilbert space for the original
physical measure. In particular this applies to Haar measure restricted to a cube. -/
def smoothPhysicalGradientLtwo (K : Compacts (ι → ℝ))
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] :
    𝓓_{K}(ι → ℝ, ℝ) →ₗ[ℝ] Lp (EuclideanSpace ℝ ι) 2 μ :=
  (BoundedContinuousFunction.toLp 2 μ ℝ).toLinearMap.comp (smoothPhysicalGradient K)

/-- The Hilbert-space gradient is represented by the genuine original derivative,
not by an abstract or independent vector field. -/
theorem smoothPhysicalGradientLtwo_ae (K : Compacts (ι → ℝ))
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (φ : 𝓓_{K}(ι → ℝ, ℝ)) :
    smoothPhysicalGradientLtwo K μ φ =ᵐ[μ]
      fun x ↦ physicalCoordinateGradient ι (fderiv ℝ φ x) := by
  have h := BoundedContinuousFunction.coeFn_toLp
    (p := 2) (μ := μ) (𝕜 := ℝ) (smoothPhysicalGradient K φ)
  refine h.mono fun x hx ↦ hx.trans ?_
  ext i
  exact smoothPhysicalGradient_apply K φ x i

/-- The weak Hilbert pairing is exactly the integral against the original
coordinate gradient. -/
theorem inner_smoothPhysicalGradientLtwo (K : Compacts (ι → ℝ))
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (j : Lp (EuclideanSpace ℝ ι) 2 μ) (φ : 𝓓_{K}(ι → ℝ, ℝ)) :
    inner ℝ j (smoothPhysicalGradientLtwo K μ φ) =
      ∫ x, inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ φ x)) ∂μ := by
  rw [L2.inner_def]
  exact integral_congr_ae ((smoothPhysicalGradientLtwo_ae K μ φ).mono fun x hx ↦
    congrArg (fun v ↦ inner ℝ (j x) v) hx)

omit [DecidableEq ι] in
/-- The norm of the actual flux is its literal physical L² energy. -/
theorem physicalFlux_norm_sq (μ : Measure (ι → ℝ))
    (j : Lp (EuclideanSpace ℝ ι) 2 μ) :
    ‖j‖ ^ 2 = ∫ x, ‖j x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

end OTSelector.Reconstruction
