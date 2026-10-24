import OTSelector.Analysis.Calculus.Variational.CalibratedEnergyIdentities
import OTSelector.Analysis.Calculus.Variational.HamiltonianFlatBase
import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.LengthHessian

/-!
# Geometry.Finsler.LengthMomentumVariation

* **Conditions:** An actual differentiable phase family with unit original speed at the base point; a fixed calibrated velocity for the radial coefficient identity.
* **Objects:** The true length-momentum variation as energy-momentum variation minus its radial covector correction.
* **Proof detail:** Differentiate energy momentum=speed·length momentum, use the actual radial Hessian identity and differentiate calibration at the fixed velocity.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLengthMomentumVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLengthMomentumVariation`; the selected original proof blocks follow. -/
section

/-!
# Variation of the original length momentum

The original energy momentum equals speed times original length momentum. Its actual
parameter differential at unit speed therefore differs from the length momentum
variation by one radial covector. Calibration of a fixed unit velocity identifies that
coefficient with the energy momentum variation evaluated on the same velocity.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Differentiating an actual scalar normalization at unit value gives its exact
covector correction, without prescribing either differential. -/
theorem fderiv_normalized_covector_of_unit {g : W → ℝ} {P Q : W → E →L[ℝ] ℝ}
    {w₀ : W} (hg : DifferentiableAt ℝ g w₀) (hQ : DifferentiableAt ℝ Q w₀)
    (heq : P =ᶠ[𝓝 w₀] fun w ↦ g w • Q w) (hunit : g w₀ = 1) (u : W) :
    fderiv ℝ Q w₀ u = fderiv ℝ P w₀ u - (fderiv ℝ g w₀ u) • P w₀ := by
  have hp : P w₀ = Q w₀ := by simpa only [hunit, one_smul] using heq.self_of_nhds
  have h := congrArg (fun D : W →L[ℝ] (E →L[ℝ] ℝ) ↦ D u)
    (hg.hasFDerivAt.smul hQ.hasFDerivAt).fderiv
  change fderiv ℝ (fun w ↦ g w • Q w) w₀ u = _ at h
  rw [← heq.fderiv_eq] at h
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, hunit, one_smul] at h
  rw [h, hp]
  abel

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}
  (hF : F.IsSmoothStronglyConvex)
include hF

/-- The actual length momentum variation is the original energy momentum variation
minus the speed variation times the central momentum, at unit original speed. -/
theorem chartLengthMomentum_parameter_fderiv_of_unit (old : M)
    {Z : W → E × E} {w₀ : W} (hZ : DifferentiableAt ℝ Z w₀)
    (hz : Z w₀ ∈ chartEnergyDomain old) (hs : (F.chartLength old (Z w₀) : ℝ) = 1)
    (u : W) :
    fderiv ℝ (fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) ∘ Z) w₀ u =
      fderiv ℝ (fiberLegendre (F.chartEnergy old) ∘ Z) w₀ u -
        (fderiv ℝ ((fun z ↦ (F.chartLength old z : ℝ)) ∘ Z) w₀ u) •
          fiberLegendre (F.chartEnergy old) (Z w₀) := by
  have hL := (hF.contDiffOn_chartLength old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hz)
  apply fderiv_normalized_covector_of_unit
    ((hL.differentiableAt (by simp)).comp w₀ hZ)
    (((contDiffAt_fiberLegendre hL).differentiableAt (by simp)).comp w₀ hZ) _ hs
  filter_upwards [hZ.continuousAt.preimage_mem_nhds
    ((isOpen_chartEnergyDomain old).mem_nhds hz)] with w hw
  exact hF.chartLegendre_eq_length_smul_fderiv old hw

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The true vertical energy Hessian is symmetric. -/
theorem chartEnergy_verticalHessian_symm (old : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain old) (u v : E) :
    verticalEnergyHessian (F.chartEnergy old) z u v =
      verticalEnergyHessian (F.chartEnergy old) z v u := by
  have hL := (hF.contDiffOn_chartEnergy old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hz)
  have hf : ContDiffAt ℝ ∞ (fun w ↦ F.chartEnergy old (z.1, w)) z.2 :=
    by simpa only [Function.comp_def] using!
      hL.comp z.2 (contDiffAt_const.prodMk (contDiffAt_id (x := z.2)))
  exact hf.isSymmSndFDerivAt (by simp) u v

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The original inverse energy Hessian pairs with radial momentum by evaluation on
the actual velocity. This uses only strong convexity and true energy homogeneity. -/
theorem chartEnergy_inverseHessian_radial_pairing [FiniteDimensional ℝ E]
    (old : M) {z : E × E} (hz : z ∈ chartEnergyDomain old) (q : E →L[ℝ] ℝ) :
    fiberLegendre (F.chartEnergy old) z
      (ContinuousLinearMap.inverse (verticalEnergyHessian (F.chartEnergy old) z) q) =
        q z.2 := by
  let d := positive_dualMap_equiv (verticalEnergyHessian (F.chartEnergy old) z)
    (fun _ hw ↦ hF.chartEnergy_hessian_pos old hz hw)
  rw [show ContinuousLinearMap.inverse (verticalEnergyHessian (F.chartEnergy old) z) =
    d.symm.toContinuousLinearMap from ContinuousLinearMap.inverse_equiv d]
  rw [← hF.chartEnergy_hessian_radial old hz]
  change verticalEnergyHessian (F.chartEnergy old) z z.2 (d.symm q) = q z.2
  rw [hF.chartEnergy_verticalHessian_symm old hz]
  exact congrArg (fun p : E →L[ℝ] ℝ ↦ p z.2) (d.apply_symm_apply q)

/-- In a calibrated unit tube the actual speed variation equals the actual energy
momentum variation evaluated on its fixed central velocity. -/
theorem chartSpeed_parameter_fderiv_eq_momentum_radial (old : M) {U : Set E}
    (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, (F.chartLength old (x, v₀) : ℝ) = 1)
    (hbound : ∀ x ∈ U, ∀ v : E, p v ≤ (F.chartLength old (x, v) : ℝ))
    {Z : W → E × E} {w₀ : W} (hZ : DifferentiableAt ℝ Z w₀)
    (hx : (Z w₀).1 ∈ U) (hv : (Z w₀).2 = v₀) (u : W) :
    fderiv ℝ ((fun z ↦ (F.chartLength old z : ℝ)) ∘ Z) w₀ u =
      fderiv ℝ (fiberLegendre (F.chartEnergy old) ∘ Z) w₀ u v₀ := by
  have hv₀ : v₀ ≠ 0 := by intro h; rw [h, _root_.map_zero] at hp; norm_num at hp
  have hz : Z w₀ ∈ chartEnergyDomain old := ⟨hsub hx, hv ▸ hv₀⟩
  have hident := hF.chartEnergy_calibrated_identities old hU hsub p hp
    (fun x hx ↦ NNReal.coe_injective (by simpa using hunit x hx)) hbound hx
  have hzeq : Z w₀ = ((Z w₀).1, v₀) := Prod.ext rfl hv
  have hL := (hF.contDiffOn_chartEnergy old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hz)
  have hG := (hF.contDiffOn_chartLength old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hz)
  have hP := (contDiffAt_fiberLegendre hL).differentiableAt (by simp)
  have hsplit := energy_partials_zero_of_hessian_base_zero
    (isOpen_chartEnergyDomain old) (hF.contDiffOn_chartEnergy old) hz
    (by rw [hzeq]; exact hident.2.2.2.2.2.2.1)
  have hmomentum : fiberLegendre (F.chartEnergy old) (Z w₀) = p := by
    rw [hzeq]; exact hident.2.2.1
  have hfirst : fderiv ℝ (F.chartEnergy old) (Z w₀) =
      p.comp (ContinuousLinearMap.snd ℝ E E) := by
    rw [hzeq]; exact hident.2.2.2.2.2.1
  have hs : (F.chartLength old (Z w₀) : ℝ) = 1 := by
    rw [hzeq]; exact hunit _ hx
  have hspeed : fderiv ℝ (fun z ↦ (F.chartLength old z : ℝ)) (Z w₀) =
      p.comp (ContinuousLinearMap.snd ℝ E E) := by
    have h := congrArg (fun D : (E × E) →L[ℝ] ℝ ↦ D)
      (((hG.differentiableAt (by simp)).hasFDerivAt.pow 2).const_smul (1 / 2 : ℝ)).fderiv
    have heq : (fun z ↦ (1 / 2 : ℝ) • (F.chartLength old z : ℝ) ^ 2) =
        F.chartEnergy old := by
      funext z; rw [F.chartEnergy_eq_chartLength_sq]; simp only [smul_eq_mul]; ring
    change fderiv ℝ (fun z ↦ (1 / 2 : ℝ) • (F.chartLength old z : ℝ) ^ 2)
      (Z w₀) = _ at h
    rw [heq, hfirst] at h
    norm_num [hs, smul_smul] at h
    exact h.symm
  have hrad (d : E × E) :
      fderiv ℝ (fiberLegendre (F.chartEnergy old)) (Z w₀) d v₀ = p d.2 := by
    have hdecomp : d = (d.1, 0) + (0, d.2) := by ext <;> simp
    rw [hdecomp, map_add, hsplit.2, zero_add]
    have hvertical := congrArg (fun A ↦ A d.2)
      (fiberLegendre_fderiv_vertical hL)
    change fderiv ℝ (fiberLegendre (F.chartEnergy old)) (Z w₀) (0, d.2) =
      verticalEnergyHessian (F.chartEnergy old) (Z w₀) d.2 at hvertical
    rw [hvertical, ← hv, hF.chartEnergy_verticalHessian_symm old hz]
    change fderiv ℝ (fderiv ℝ (fun v ↦ F.chartEnergy old ((Z w₀).1, v)))
      (Z w₀).2 (Z w₀).2 d.2 = _
    rw [hF.chartEnergy_hessian_radial old hz, hmomentum]
    simp only [Prod.snd_add, zero_add]
  rw [fderiv_comp w₀ (hG.differentiableAt (by simp)) hZ,
    fderiv_comp w₀ hP hZ]
  exact (congrArg (fun A ↦ A (fderiv ℝ Z w₀ u)) hspeed).trans
    (hrad (fderiv ℝ Z w₀ u)).symm

/-- Calibration makes the radial correction to the actual length momentum variation
an evaluation of the actual energy momentum variation, with no supplied speed derivative. -/
theorem chartLengthMomentum_parameter_fderiv_of_calibrated (old : M) {U : Set E}
    (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, (F.chartLength old (x, v₀) : ℝ) = 1)
    (hbound : ∀ x ∈ U, ∀ v : E, p v ≤ (F.chartLength old (x, v) : ℝ))
    {Z : W → E × E} {w₀ : W} (hZ : DifferentiableAt ℝ Z w₀)
    (hx : (Z w₀).1 ∈ U) (hv : (Z w₀).2 = v₀) (u : W) :
    fderiv ℝ (fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) ∘ Z) w₀ u =
      fderiv ℝ (fiberLegendre (F.chartEnergy old) ∘ Z) w₀ u -
        (fderiv ℝ (fiberLegendre (F.chartEnergy old) ∘ Z) w₀ u v₀) • p := by
  have hv₀ : v₀ ≠ 0 := by intro h; rw [h, _root_.map_zero] at hp; norm_num at hp
  have hz : Z w₀ ∈ chartEnergyDomain old := ⟨hsub hx, hv ▸ hv₀⟩
  have hzeq : Z w₀ = ((Z w₀).1, v₀) := Prod.ext rfl hv
  have hs : (F.chartLength old (Z w₀) : ℝ) = 1 := by
    rw [hzeq]; exact hunit _ hx
  have hmomentum : fiberLegendre (F.chartEnergy old) (Z w₀) = p := by
    rw [hzeq]
    exact (hF.chartEnergy_calibrated_identities old hU hsub p hp
    (fun x hx ↦ NNReal.coe_injective (by simpa using hunit x hx)) hbound hx).2.2.1
  rw [hF.chartLengthMomentum_parameter_fderiv_of_unit old hZ hz hs u,
    hF.chartSpeed_parameter_fderiv_eq_momentum_radial old hU hsub p hp hunit hbound
      hZ hx hv u, hmomentum]

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
