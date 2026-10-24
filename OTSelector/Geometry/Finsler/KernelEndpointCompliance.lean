import OTSelector.Analysis.Calculus.Variational.EndpointJacobiCompliance
import OTSelector.Analysis.Calculus.Variational.KernelEndpointCompliance
import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.EndpointCompliance
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthMomentumVariation
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.LinearAlgebra.Dual.CovectorKernel

/-!
# Geometry.Finsler.KernelEndpointCompliance

* **Conditions:** The original unit-speed curve and fixed actual momentum kernel, with the stated calibrated constant-velocity/flat-base conditions for comparing full compliance.
* **Objects:** The genuine restricted length-Hessian inverse integral and its positive inverse form, identified with the full endpoint compliance on that kernel.
* **Proof detail:** Compress the actual inverse energy Hessian, use unit-speed kernel Hessian equality, commute fixed compression with integration and compare inverse pairings.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46): Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition prop:rough-ray-quadratic, lines 1188–1205; equation eq:rough-ray-quadratic, integral inverse-Hessian coefficient.

Source relation (derived): The inverse-integral transverse coefficient is a project derivation from actual Finsler Hessians; no unrelated distance Hessian is supplied as input.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerKernelEndpointCompliance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerKernelEndpointCompliance`; the selected original proof blocks follow. -/
section

/-!
# The original length-Hessian integral on the fixed momentum kernel

The compressed inverse original energy Hessian is the inverse actual restricted length
Hessian at unit speed. Integration preserves this identification. The full endpoint
compliance inverse, paired on the fixed momentum kernel, therefore equals the inverse
integral of these genuine restricted length-Hessian inverses along the same curve.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual original fiber length Hessian restricted to a specified covector kernel. -/
def chartLengthKernelHessian (F : ContinuousFinslerNorm E M) (old : M)
    (p : E →L[ℝ] ℝ) (z : E × E) : p.ker →L[ℝ] (p.ker →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ p.ker E ℝ).flip p.ker.subtypeL).comp
    ((fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (z.1, v) : ℝ))) z.2).comp
      p.ker.subtypeL)

/-- Integrate the actual restricted length-Hessian inverses along the original curve. -/
def chartLengthKernelCompliance (F : ContinuousFinslerNorm E M) (old : M)
    (p : E →L[ℝ] ℝ) (c : ℝ → M) (a b : ℝ) : (p.ker →L[ℝ] ℝ) →L[ℝ] p.ker :=
  endpointCompliance (fun t ↦ (F.chartLengthKernelHessian old p
    ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t)).inverse) a b

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- At original unit speed, compression of the original inverse energy Hessian is
exactly the inverse actual length Hessian restricted to the actual momentum kernel. -/
theorem chartEnergy_inverseHessian_kernelCompression_eq
    (hF : F.IsSmoothStronglyConvex) (old : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain old) (p : E →L[ℝ] ℝ) (hp : p z.2 ≠ 0)
    (hmomentum : fiberLegendre (F.chartEnergy old) z = p)
    (hunit : (F.chartLength old z : ℝ) = 1) :
    covectorKernelCompression p z.2 hp (verticalEnergyHessian (F.chartEnergy old) z).inverse =
      (F.chartLengthKernelHessian old p z).inverse := by
  let H := verticalEnergyHessian (F.chartEnergy old) z
  have hH : H.IsInvertible :=
    ⟨positive_dualMap_equiv H (fun _ hu ↦ hF.chartEnergy_hessian_pos old hz hu), rfl⟩
  have hrad : H z.2 = p := (hF.chartEnergy_hessian_radial old hz).trans hmomentum
  have hsym : ∀ u w, H u w = H w u := hF.chartEnergy_verticalHessian_symm old hz
  have hHC : ∀ q, H (H.inverse q) = q := hH.self_apply_inverse
  have hpos : ∀ w : p.ker, w ≠ 0 → 0 < F.chartLengthKernelHessian old p z w w := by
    intro w hw
    apply hF.chartLength_hessian_pos_on_momentum_ker old hz
      (fun he ↦ hw (Subtype.ext he))
    rw [hmomentum]
    exact w.property
  let d := positive_dualMap_equiv (F.chartLengthKernelHessian old p z) hpos
  rw [show (F.chartLengthKernelHessian old p z).inverse = d.symm.toContinuousLinearMap from
    ContinuousLinearMap.inverse_equiv d]
  apply ContinuousLinearMap.ext
  intro η
  apply d.injective
  change d (covectorKernelCompression p z.2 hp H.inverse η) = d (d.symm η)
  rw [d.apply_symm_apply]
  apply ContinuousLinearMap.ext
  intro w
  change fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength old (z.1, v) : ℝ))) z.2
    (covectorKernelCompression p z.2 hp H.inverse η : E) (w : E) = η w
  rw [hF.chartLength_hessian_on_momentum_ker_of_unit old hz hunit _ _
    (by rw [hmomentum]; exact (covectorKernelCompression p z.2 hp H.inverse η).property)]
  exact covectorKernelCompression_inverse p z.2 hp hsym hrad hHC η w

/-- Along the same actual unit-speed, fixed-momentum family curve, the integral of
restricted length-Hessian inverses is the compressed original energy compliance. -/
theorem chartLengthKernelCompliance_eq_compression
    (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (old : M) {a b : ℝ} (hab : a ≤ b)
    (hx : ∀ t ∈ Icc a b, Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (p : E →L[ℝ] ℝ) (v₀ : E) (hp : p v₀ ≠ 0)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t = v₀)
    (hmomentum : ∀ t ∈ Icc a b, (F.chartMomentumFamily old Γ (w₀, t)).2 = p)
    (hunit : ∀ t ∈ Icc a b, (F.chartLength old
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t) : ℝ) = 1) :
    F.chartLengthKernelCompliance old p (Γ w₀) a b =
      covectorKernelCompression p v₀ hp (F.chartEndpointCompliance old (Γ w₀) a b) := by
  have hC : ContinuousOn (F.chartInverseEnergyHessian old (Γ w₀)) (Icc a b) :=
    fun t ht ↦ (hF.continuousAt_chartInverseEnergyHessian hB hEL hG hw old t
      (hx t ht)).continuousWithinAt
  rw [chartEndpointCompliance, ← endpointCompliance_kernelCompression_eq p v₀ hp hab hC]
  apply endpointCompliance_congr_on hab
  intro t ht'
  have hz := (hF.chartTangent_of_isEulerLagrangeAt (hEL w₀ hw t (mem_univ _)) old (hx t ht')).2
  have hp' : p (deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t) ≠ 0 := by
    rw [hvelocity t ht']; exact hp
  have heq := hF.chartEnergy_inverseHessian_kernelCompression_eq old hz p hp'
    (hmomentum t ht') (hunit t ht')
  simpa only [chartInverseEnergyHessian, hvelocity t ht'] using heq.symm

/-- The actual endpoint compliance restricted to the momentum kernel is the inverse
integral of actual restricted length-Hessian inverses, for the same intrinsic curve. -/
theorem chartEndpointCompliance_inverse_on_kernel
    (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (old : M) {a b : ℝ} (hab : a < b)
    (hx : ∀ t ∈ Icc a b, Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (p : E →L[ℝ] ℝ) (v₀ : E) (hp : p v₀ ≠ 0)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t = v₀)
    (hmomentum : ∀ t ∈ Icc a b, (F.chartMomentumFamily old Γ (w₀, t)).2 = p)
    (hunit : ∀ t ∈ Icc a b, (F.chartLength old
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t) : ℝ) = 1) (u w : p.ker) :
    (F.chartEndpointCompliance old (Γ w₀) a b).inverse (u : E) (w : E) =
      (F.chartLengthKernelCompliance old p (Γ w₀) a b).inverse u w := by
  have hC : ContinuousOn (F.chartInverseEnergyHessian old (Γ w₀)) (Icc a b) :=
    fun t ht ↦ (hF.continuousAt_chartInverseEnergyHessian hB hEL hG hw old t
      (hx t ht)).continuousWithinAt
  have hpos (t : ℝ) (ht : t ∈ Icc a b) (q : E →L[ℝ] ℝ) (hq : q ≠ 0) :
      0 < q (F.chartInverseEnergyHessian old (Γ w₀) t q) :=
    hF.chartInverseEnergyHessian_pos old (hEL w₀ hw t (mem_univ _)) (hx t ht) hq
  have hrad (t : ℝ) (ht : t ∈ Icc a b) (q : E →L[ℝ] ℝ) :
      p (F.chartInverseEnergyHessian old (Γ w₀) t q) = q v₀ := by
    have hz := (hF.chartTangent_of_isEulerLagrangeAt (hEL w₀ hw t (mem_univ _)) old (hx t ht)).2
    have h := hF.chartEnergy_inverseHessian_radial_pairing old hz q
    change (F.chartMomentumFamily old Γ (w₀, t)).2
      (F.chartInverseEnergyHessian old (Γ w₀) t q) =
        q (deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t) at h
    simpa only [hmomentum t ht, hvelocity t ht] using h
  rw [hF.chartLengthKernelCompliance_eq_compression hB hEL hG hw old hab.le hx
    p v₀ hp hvelocity hmomentum hunit, chartEndpointCompliance,
    ← endpointCompliance_kernelCompression_eq p v₀ hp hab.le hC]
  exact endpointCompliance_inverse_on_kernel p v₀ hp hab hC hpos hrad u w

/-- The inverse integral of the original restricted length Hessians is strictly
positive on every nonzero vector in the fixed momentum kernel. -/
theorem chartLengthKernelCompliance_inverse_pos
    (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (old : M) {a b : ℝ} (hab : a < b)
    (hx : ∀ t ∈ Icc a b, Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (p : E →L[ℝ] ℝ) (v₀ : E) (hp : p v₀ ≠ 0)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t = v₀)
    (hmomentum : ∀ t ∈ Icc a b, (F.chartMomentumFamily old Γ (w₀, t)).2 = p)
    (hunit : ∀ t ∈ Icc a b, (F.chartLength old
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t) : ℝ) = 1) {u : p.ker} (hu : u ≠ 0) :
    0 < (F.chartLengthKernelCompliance old p (Γ w₀) a b).inverse u u := by
  rw [← hF.chartEndpointCompliance_inverse_on_kernel hB hEL hG hw old hab hx
    p v₀ hp hvelocity hmomentum hunit u u]
  apply endpointCompliance_inverse_pos hab
    (fun t ht ↦ (hF.continuousAt_chartInverseEnergyHessian hB hEL hG hw old t
      (hx t ht)).continuousWithinAt)
    (fun t ht q hq ↦ hF.chartInverseEnergyHessian_pos old
      (hEL w₀ hw t (mem_univ _)) (hx t ht) hq)
  exact fun he ↦ hu (Subtype.ext he)

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
