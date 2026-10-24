import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthProjection
import OTSelector.LinearAlgebra.Dual.CovectorKernel
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerNormalHamiltonian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerNormalHamiltonian`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Hamiltonian.Normal

* **Conditions:** A genuine local inverse Legendre branch and an actual slit Finsler phase.
* **Objects:** The compressed normal momentum block, symmetric positivity and its inverse relationship to speed times the actual length Hessian.
* **Proof detail:** Compress the inverse energy Hessian using velocity projection and covector extension, then identify its inverse on the momentum kernel.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): A pointwise normal-block identity. Time-dependent frames and their derivative terms are not supplied by this statement.
-/

/-!
# The actual Hamiltonian momentum block on the Finsler normal space

Projection along the actual velocity and dual extension identify the normal compression
of the genuine inverse-Legendre momentum block. It is symmetric and positive, and the
original speed times the fiber length Hessian inverts it on the actual momentum kernel.
At unit speed the two are inverse forms. No auxiliary inner product or supplied normal
Hessian is used. This is a pointwise statement; time-dependent frames and the reduced
Jacobi coefficients still require their derivative terms.
-/

open Set Manifold
open scoped ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The actual momentum block compresses to a symmetric positive map, inverted by
speed times the true length Hessian on the actual momentum kernel. -/
theorem chartHamiltonian_normal_block (x₀ : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsub : e.source ⊆ chartEnergyDomain x₀) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {z : E × E} (hzs : z ∈ e.source) :
    let p := fiberLegendre (F.chartEnergy x₀) z
    let C := localHamiltonianBlockC (F.chartEnergy x₀) e (e z)
    let CK := covectorKernelCompression p z.2 (hF.chartMomentum_self_pos x₀ (hsub hzs)).ne' C
    (∀ η : p.ker →L[ℝ] ℝ, η ≠ 0 → 0 < η (CK η)) ∧
    (∀ η ξ : p.ker →L[ℝ] ℝ, ξ (CK η) = η (CK ξ)) ∧
    ∀ (η : p.ker →L[ℝ] ℝ) (w : p.ker),
      (F.chartLength x₀ z : ℝ) *
        fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2
          (CK η : E) (w : E) = η w := by
  let L := F.chartEnergy x₀
  let p := fiberLegendre L z
  let H := verticalEnergyHessian L z
  let C := localHamiltonianBlockC L e (e z)
  have hz := hsub hzs
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy x₀).mono hsub
  have hzt : e z ∈ e.target := e.map_source hzs
  have hi : e.symm (e z) = z := e.left_inv hzs
  have hpos : ∀ w : E, w ≠ 0 → 0 < verticalEnergyHessian L (e.symm (e z)) w w := by
    intro w hw
    simpa only [hi, verticalEnergyHessian, L] using hF.chartEnergy_hessian_pos x₀ hz hw
  have hCpos : ∀ q : E →L[ℝ] ℝ, q ≠ 0 → 0 < q (C q) :=
    fun q hq ↦ localHamiltonianBlockC_pos he hL hG hzt hpos hq
  have hCsym : ∀ q r : E →L[ℝ] ℝ, r (C q) = q (C r) :=
    localHamiltonianBlockC_symm he hL hG hzt
  have hHC (q : E →L[ℝ] ℝ) : H (C q) = q := by
    dsimp only [C]
    rw [localHamiltonianBlockC_eq_inverseLegendreMomentumDerivative hL hG hzt]
    simpa only [hi] using verticalEnergyHessian_inverseLegendreMomentumDerivative he hzt
      (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hzt)))
      ((hG.contDiffAt (e.open_target.mem_nhds hzt)).differentiableAt (by simp)) q
  have hHsym (u w : E) : H u w = H w u := by
    have hc : ContDiffAt ℝ ∞ (fun v ↦ L (z.1, v)) z.2 := by
      have h := (hF.contDiffOn_chartEnergy x₀).contDiffAt
        ((isOpen_chartEnergyDomain x₀).mem_nhds hz)
      simpa only [Function.comp_def] using!
        h.comp z.2 (contDiffAt_const.prodMk (contDiffAt_id (x := z.2)))
    exact hc.isSymmSndFDerivAt (by simp) u w
  have hrad : H z.2 = p := hF.chartEnergy_hessian_radial x₀ hz
  dsimp only
  refine ⟨fun _ hη ↦ covectorKernelCompression_pos p z.2 _ hCpos hη,
    covectorKernelCompression_symm p z.2 _ hCsym, ?_⟩
  intro η w
  rw [hF.chartLength_hessian_on_momentum_ker x₀ hz _ _
    (covectorKernelCompression p z.2 _ C η).property]
  exact covectorKernelCompression_inverse p z.2 _ hHsym hrad hHC η w

/-- The normal momentum block is the inverse length-Hessian equivalence divided by speed. -/
theorem exists_chartHamiltonian_normal_inverse [FiniteDimensional ℝ E] (x₀ : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsub : e.source ⊆ chartEnergyDomain x₀) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {z : E × E} (hzs : z ∈ e.source) :
    let p := fiberLegendre (F.chartEnergy x₀) z
    let CK := covectorKernelCompression p z.2 (hF.chartMomentum_self_pos x₀ (hsub hzs)).ne'
      (localHamiltonianBlockC (F.chartEnergy x₀) e (e z))
    ∃ d : p.ker ≃L[ℝ] (p.ker →L[ℝ] ℝ),
      (∀ u w : p.ker, d u w = fderiv ℝ (fderiv ℝ
        (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 (u : E) (w : E)) ∧
      ∀ η : p.ker →L[ℝ] ℝ, CK η = (F.chartLength x₀ z : ℝ)⁻¹ • d.symm η := by
  dsimp only
  obtain ⟨d, hd⟩ := hF.exists_chartLength_kernelHessian_equiv x₀ (hsub hzs)
  refine ⟨d, hd, ?_⟩
  intro η
  apply d.injective
  ext w
  rw [_root_.map_smul, smul_apply, d.apply_symm_apply, smul_eq_mul, hd]
  have h := (hF.chartHamiltonian_normal_block x₀ he hsub hG hzs).2.2 η w
  have hs : (F.chartLength x₀ z : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (F.chartLength_pos x₀ (hsub hzs))).ne'
  rw [← h]
  field_simp

/-- Original smooth strongly convex Finsler data construct a genuine Legendre chart whose
normal momentum block is the inverse original length Hessian divided by speed. -/
theorem exists_chartHamiltonian_normal_blocks [FiniteDimensional ℝ E] (x₀ : M)
    {z : E × E} (hz : z ∈ chartEnergyDomain x₀) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀) ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      let p := fiberLegendre (F.chartEnergy x₀) z
      let CK := covectorKernelCompression p z.2 (hF.chartMomentum_self_pos x₀ hz).ne'
        (localHamiltonianBlockC (F.chartEnergy x₀) e (e z))
      (∀ η : p.ker →L[ℝ] ℝ, η ≠ 0 → 0 < η (CK η)) ∧
      (∀ η ξ : p.ker →L[ℝ] ℝ, ξ (CK η) = η (CK ξ)) ∧
      ∃ d : p.ker ≃L[ℝ] (p.ker →L[ℝ] ℝ),
        (∀ u w : p.ker, d u w = fderiv ℝ (fderiv ℝ
          (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 (u : E) (w : E)) ∧
        ∀ η : p.ker →L[ℝ] ℝ, CK η = (F.chartLength x₀ z : ℝ)⁻¹ • d.symm η := by
  obtain ⟨e, he, hzs, _, hsub, _, hG, _, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse x₀ hz
  have hblock := hF.chartHamiltonian_normal_block x₀ he hsub hG hzs
  exact ⟨e, he, hzs, hsub, hG, hblock.1, hblock.2.1,
    hF.exists_chartHamiltonian_normal_inverse x₀ he hsub hG hzs⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
