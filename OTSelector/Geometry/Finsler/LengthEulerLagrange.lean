import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeEnergy
import OTSelector.Geometry.Finsler.LengthHessian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLengthEulerLagrange.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLengthEulerLagrange`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.LengthEulerLagrange

* **Conditions:** An actual C2 nonzero-velocity energy Euler–Lagrange curve on a connected open interval.
* **Objects:** The true base-energy/length differential identity and the actual length Euler–Lagrange equation.
* **Proof detail:** Differentiate F²/2, prove positive constant speed by energy conservation, and divide the actual momentum equation by that constant.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Actual length Euler--Lagrange equations from original energy equations

Differentiating the squared original length identifies the true base energy differential.
An actual C2 slit energy Euler--Lagrange curve has constant positive original speed.
Dividing its actual momentum equation by this constant gives the length equation, with
no assumed length stationarity or supplied constant speed.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}
  (hF : F.IsSmoothStronglyConvex)
include hF

/-- The original base energy differential is speed times the true base length differential. -/
theorem chartBaseEnergy_eq_length_smul_baseLength (x₀ : M) {z : E × E}
    (hz : z ∈ ContinuousFinslerNorm.chartEnergyDomain x₀) :
    baseEnergyDifferential (F.chartEnergy x₀) z = (F.chartLength x₀ z : ℝ) •
      baseEnergyDifferential (fun z ↦ (F.chartLength x₀ z : ℝ)) z := by
  have hd := ((hF.contDiffOn_chartLength x₀).contDiffAt
    ((ContinuousFinslerNorm.isOpen_chartEnergyDomain x₀).mem_nhds hz)).differentiableAt
      (by simp)
  have hi : DifferentiableAt ℝ (fun x : E ↦ (x, z.2)) z.1 :=
    differentiableAt_id.prodMk (differentiableAt_const z.2)
  have hb : DifferentiableAt ℝ (fun x ↦ (F.chartLength x₀ (x, z.2) : ℝ)) z.1 := by
    simpa only [Function.comp_def] using! hd.comp z.1 hi
  have hh := (hb.hasFDerivAt.pow 2).const_smul (1 / 2 : ℝ)
  change fderiv ℝ (fun x ↦ F.chartEnergy x₀ (x, z.2)) z.1 = _
  simp only [F.chartEnergy_eq_chartLength_sq]
  convert! hh.fderiv using 1
  · congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · ext w
    simp [baseEnergyDifferential]
    ring

/-- Every actual C2 slit energy Euler--Lagrange curve satisfies the true length equation. -/
theorem chartLength_eulerLagrange_of_chartEnergy (x₀ : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ t ∈ I, (x t, deriv x t) ∈ ContinuousFinslerNorm.chartEnergyDomain x₀)
    (hEL : ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
      (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t) :
    ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ)) (x s, deriv x s))
      (baseEnergyDifferential (fun z ↦ (F.chartLength x₀ z : ℝ)) (x t, deriv x t)) t := by
  intro t ht
  let S : ℝ := F.chartLength x₀ (x t, deriv x t)
  have hS : S ≠ 0 := (NNReal.coe_pos.mpr (F.chartLength_pos x₀ (hphase t ht))).ne'
  have hd : HasDerivAt
      (fun s ↦ S⁻¹ • fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
      (baseEnergyDifferential (fun z ↦ (F.chartLength x₀ z : ℝ)) (x t, deriv x t)) t := by
    convert! (hEL t ht).const_smul S⁻¹ using 1
    rw [hF.chartBaseEnergy_eq_length_smul_baseLength x₀ (hphase t ht)]
    change _ = S⁻¹ • (S • _)
    simp [smul_smul, hS]
  apply hd.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hs
  rw [hF.chartLegendre_eq_length_smul_fderiv x₀ (hphase s hs),
    hF.chartLength_eq_of_eulerLagrange x₀ hI hconn hx hphase hEL hs ht]
  change _ = S⁻¹ • (S • _)
  simp [smul_smul, hS, fiberLegendre]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
