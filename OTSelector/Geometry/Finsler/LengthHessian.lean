import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLengthHessian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLengthHessian`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.LengthHessian

* **Conditions:** A smooth strongly convex original Finsler norm and a nonzero actual chart velocity; finite dimension is needed for the Hessian–dual equivalence.
* **Objects:** The true length differential/Hessian, radial annihilation, positivity on the momentum kernel and its dual equivalence.
* **Proof detail:** Differentiate F²/2 twice, use positive speed and momentum-kernel annihilation to identify the restricted energy/length Hessians, and apply finite-dimensional positivity.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Shen supplies homogeneity and the fundamental energy tensor; the explicit kernel restriction and normed dual equivalence are derived, without identifying an endpoint-distance Hessian.
-/

/-!
# The actual Finsler length Hessian on the momentum kernel

The original chart length is smooth away from zero velocity because it is the positive
square root of twice the original energy. Differentiating the squared-length identity
identifies its true first and second fiber derivatives. On the kernel of actual momentum,
the energy Hessian is the original speed times the length Hessian; hence the restricted
length Hessian is positive and, in finite dimensions, gives an equivalence with the dual.
The actual length Hessian is symmetric and annihilates the radial velocity.

These statements use the original smooth strongly convex Finsler data. No inner product,
chosen normal frame or independent Hessian is supplied. This is the fiber length Hessian;
identifying a two-endpoint distance Hessian still requires the variational boundary problem.
-/

open Set Manifold Filter
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem fderiv_half_sq {f : E → ℝ} {v : E} (hf : DifferentiableAt ℝ f v) :
    fderiv ℝ (fun w ↦ f w ^ 2 / 2) v = f v • fderiv ℝ f v := by
  have hh := (hf.hasFDerivAt.pow 2).const_smul (1 / 2 : ℝ)
  convert! hh.fderiv using 1
  · congr 1
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · ext w
    simp
    ring

private theorem fderiv2_half_sq {f : E → ℝ} {v : E} (hf : ContDiffAt ℝ 2 f v)
    (u w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f y ^ 2 / 2)) v u w =
      f v * fderiv ℝ (fderiv ℝ f) v u w + fderiv ℝ f v u * fderiv ℝ f v w := by
  have he : fderiv ℝ (fun y ↦ f y ^ 2 / 2) =ᶠ[𝓝 v]
      (fun y ↦ f y • fderiv ℝ f y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact fderiv_half_sq (hy.differentiableAt (by norm_num))
  rw [he.fderiv_eq, fderiv_fun_smul (hf.differentiableAt (by norm_num))
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one)]
  simp

namespace ContinuousFinslerNorm
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Original chart length is the positive square root of twice the actual chart energy. -/
theorem chartLength_eq_sqrt_energy (F : ContinuousFinslerNorm E M) (x₀ : M) (z : E × E) :
    (F.chartLength x₀ z : ℝ) = Real.sqrt (2 * F.chartEnergy x₀ z) := by
  rw [F.chartEnergy_eq_chartLength_sq]
  rw [show 2 * ((F.chartLength x₀ z : ℝ) ^ 2 / 2) = (F.chartLength x₀ z : ℝ) ^ 2
    by ring, Real.sqrt_sq (NNReal.coe_nonneg _)]

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The original length is jointly smooth in chart position and nonzero velocity. -/
theorem contDiffOn_chartLength (x₀ : M) :
    ContDiffOn ℝ ∞ (fun z ↦ (F.chartLength x₀ z : ℝ)) (chartEnergyDomain x₀) := by
  have hc : ContDiffOn ℝ ∞ (fun z ↦ (2 : ℝ) * F.chartEnergy x₀ z)
      (chartEnergyDomain x₀) := contDiffOn_const.mul (hF.contDiffOn_chartEnergy x₀)
  have hs := hc.sqrt (fun z hz ↦ show 2 * F.chartEnergy x₀ z ≠ 0 by
    rw [F.chartEnergy_eq_chartLength_sq]
    have hp : 0 < (F.chartLength x₀ z : ℝ) := NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)
    nlinarith [sq_pos_of_pos hp])
  simpa only [← F.chartLength_eq_sqrt_energy] using hs

/-- At an actual nonzero chart state, length is smooth as a function of velocity. -/
theorem contDiffAt_chartFiberLength (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) :
    ContDiffAt ℝ ∞ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ)) z.2 := by
  have hc := (hF.contDiffOn_chartLength x₀).contDiffAt
    ((isOpen_chartEnergyDomain x₀).mem_nhds hz)
  have hp : ContDiffAt ℝ ∞ (fun v : E ↦ (z.1, v)) z.2 :=
    contDiffAt_const.prodMk contDiffAt_id
  simpa only [Function.comp_def] using! hc.comp z.2 hp

/-- Actual momentum is original speed times the true fiber differential of length. -/
theorem chartLegendre_eq_length_smul_fderiv (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) :
    fiberLegendre (F.chartEnergy x₀) z = (F.chartLength x₀ z : ℝ) •
      fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ)) z.2 := by
  change fderiv ℝ (fun v ↦ F.chartEnergy x₀ (z.1, v)) z.2 = _
  simp only [F.chartEnergy_eq_chartLength_sq]
  exact fderiv_half_sq ((hF.contDiffAt_chartFiberLength x₀ hz).differentiableAt
    (by simp))

/-- The actual fiber energy Hessian decomposes into length Hessian and first-derivative product. -/
theorem chartEnergy_hessian_eq_length (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (u w : E) :
    fderiv ℝ (fderiv ℝ (fun v ↦ F.chartEnergy x₀ (z.1, v))) z.2 u w =
      (F.chartLength x₀ z : ℝ) *
        fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 u w +
      fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ)) z.2 u *
        fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ)) z.2 w := by
  simp only [F.chartEnergy_eq_chartLength_sq]
  exact fderiv2_half_sq ((hF.contDiffAt_chartFiberLength x₀ hz).of_le (by simp)) u w

/-- Actual momentum and the actual fiber length differential annihilate the same vectors. -/
theorem chartLength_fderiv_eq_zero_iff (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (w : E) :
    fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ)) z.2 w = 0 ↔
      fiberLegendre (F.chartEnergy x₀) z w = 0 := by
  rw [hF.chartLegendre_eq_length_smul_fderiv x₀ hz]
  simp only [smul_apply, smul_eq_mul,
    mul_eq_zero, (NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)).ne', false_or]

/-- On the momentum kernel, speed times the actual length Hessian equals the energy Hessian. -/
theorem chartLength_hessian_on_momentum_ker (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (u w : E)
    (hu : fiberLegendre (F.chartEnergy x₀) z u = 0) :
    (F.chartLength x₀ z : ℝ) *
        fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 u w =
      fderiv ℝ (fderiv ℝ (fun v ↦ F.chartEnergy x₀ (z.1, v))) z.2 u w := by
  rw [hF.chartEnergy_hessian_eq_length x₀ hz,
    (hF.chartLength_fderiv_eq_zero_iff x₀ hz u).mpr hu, zero_mul, add_zero]

/-- At unit original speed the two actual Hessians agree on the momentum kernel. -/
theorem chartLength_hessian_on_momentum_ker_of_unit (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (hs : (F.chartLength x₀ z : ℝ) = 1) (u w : E)
    (hu : fiberLegendre (F.chartEnergy x₀) z u = 0) :
    fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 u w =
      fderiv ℝ (fderiv ℝ (fun v ↦ F.chartEnergy x₀ (z.1, v))) z.2 u w := by
  simpa only [hs, one_mul] using hF.chartLength_hessian_on_momentum_ker x₀ hz u w hu

/-- The original length Hessian is strictly positive on nonzero vectors in the momentum kernel. -/
theorem chartLength_hessian_pos_on_momentum_ker (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) {w : E} (hw : w ≠ 0)
    (hp : fiberLegendre (F.chartEnergy x₀) z w = 0) :
    0 < fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 w w := by
  have he := hF.chartLength_hessian_on_momentum_ker x₀ hz w w hp
  have hs : 0 < (F.chartLength x₀ z : ℝ) := NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)
  have hpos := hF.chartEnergy_hessian_pos x₀ hz hw
  rw [← he] at hpos
  exact (mul_pos_iff_of_pos_left hs).mp hpos

/-- The true length derivative evaluated on its own velocity is the original speed. -/
theorem chartLength_fderiv_self (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) :
    fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ)) z.2 z.2 =
      (F.chartLength x₀ z : ℝ) := by
  have he := congrArg (fun p : E →L[ℝ] ℝ ↦ p z.2)
    (hF.chartLegendre_eq_length_smul_fderiv x₀ hz)
  rw [hF.chartLegendre_self_eq_chartLength_sq x₀ hz] at he
  simp only [smul_apply, smul_eq_mul] at he
  have hs : 0 < (F.chartLength x₀ z : ℝ) := NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)
  nlinarith

/-- The actual chart energy Hessian sends the radial velocity to the actual momentum. -/
theorem chartEnergy_hessian_radial (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) :
    fderiv ℝ (fderiv ℝ (fun v ↦ F.chartEnergy x₀ (z.1, v))) z.2 z.2 =
      fiberLegendre (F.chartEnergy x₀) z := by
  have hc (v : E) (hv : v ≠ 0) :
      ContDiffAt ℝ ∞ (fun w ↦ F.chartEnergy x₀ (z.1, w)) v := by
    have h := (hF.contDiffOn_chartEnergy x₀).contDiffAt
      ((isOpen_chartEnergyDomain x₀).mem_nhds (show (z.1, v) ∈ chartEnergyDomain x₀
        from ⟨hz.1, hv⟩))
    simpa only [Function.comp_def] using!
      h.comp v (contDiffAt_const.prodMk (contDiffAt_id (x := v)))
  exact twoHomogeneous_fderiv2_radial
    (fun r _ v ↦ F.chartEnergy_smul x₀ hz.1 r v)
    (fun v hv ↦ (hc v hv).differentiableAt (by simp)) hz.2
    (((hc z.2 hz.2).fderiv_right (m := 1) (by simp)).differentiableAt_one)

/-- The actual length Hessian annihilates the radial velocity. -/
theorem chartLength_hessian_radial (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) :
    fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 z.2 = 0 := by
  ext w
  have he := hF.chartEnergy_hessian_eq_length x₀ hz z.2 w
  rw [hF.chartEnergy_hessian_radial x₀ hz,
    hF.chartLength_fderiv_self x₀ hz, hF.chartLegendre_eq_length_smul_fderiv x₀ hz] at he
  simp only [smul_apply, smul_eq_mul] at he
  have hs : 0 < (F.chartLength x₀ z : ℝ) := NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)
  change _ = 0
  nlinarith

/-- Smoothness gives symmetry of the original fiber length Hessian. -/
theorem chartLength_hessian_symm (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (u w : E) :
    fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 u w =
      fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 w u :=
  (hF.contDiffAt_chartFiberLength x₀ hz).isSymmSndFDerivAt (by simp) u w

/-- In finite dimensions the true length Hessian restricts to an equivalence from the
actual momentum kernel to its continuous dual. -/
theorem exists_chartLength_kernelHessian_equiv [FiniteDimensional ℝ E]
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) :
    let K := (fiberLegendre (F.chartEnergy x₀) z).ker
    ∃ e : K ≃L[ℝ] (K →L[ℝ] ℝ), ∀ u w : K,
      e u w = fderiv ℝ (fderiv ℝ
        (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2 (u : E) (w : E) := by
  dsimp only
  let K := (fiberLegendre (F.chartEnergy x₀) z).ker
  let i := K.subtypeL
  let H := fderiv ℝ (fderiv ℝ (fun v ↦ (F.chartLength x₀ (z.1, v) : ℝ))) z.2
  let HK : K →L[ℝ] (K →L[ℝ] ℝ) :=
    ((ContinuousLinearMap.compL ℝ K E ℝ).flip i).comp (H.comp i)
  have hpos : ∀ w : K, w ≠ 0 → 0 < HK w w := by
    intro w hw
    exact hF.chartLength_hessian_pos_on_momentum_ker x₀ hz
      (fun he ↦ hw (Subtype.ext he)) w.property
  exact ⟨positive_dualMap_equiv HK hpos, fun _ _ ↦ rfl⟩

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry

end
end
