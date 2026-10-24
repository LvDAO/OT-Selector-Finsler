import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Coordinates.NormalFlow
import OTSelector.Geometry.Finsler.Coordinates.TimePotential
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.GaussLemma

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional smooth strongly convex Finsler data, one nonzero chart state and initial time.
* **Objects:** An actual C2 local position chart and scalar potential u given by the inverse time coordinate times the original speed; du is bounded by the original tangent length and saturates on actual flow velocity.
* **Proof detail:** Build the equal-energy normal position flow. First variation supplies spatial Gauss pairing, while Euler homogeneity supplies time pairing. Differentiate the true inverse coordinate identity to identify du with normalized momentum, then apply the actual Finsler fundamental inequality.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, p. 238, equations (8.33)–(8.36); Problem 8.7, p. 241.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* David Bao; Shiing-Shen Chern; Zhongmin Shen, *An Introduction to Riemann–Finsler Geometry (Springer, 2000)*, Section 5.1, pp. 111–118 (first variation); Section 5.4, pp. 129–134 (Jacobi fields); Section 6.1, pp. 139–144 (Gauss lemma).
  https://link.springer.com/content/pdf/bfm:978-1-4612-1268-3/1
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1, Proposition 1.1, p. 3; Section 1.1, Definition 1.2 and Remarks 1.3(4), pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=3
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006 author manuscript)*, Section 1.1, Definition 1.2, Remarks 1.3 and Propositions 1.4–1.5, pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=4
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
  https://www.jirka.org/ra/realanal2.pdf#page=38

**Relationship to the sources:** This is a local derived calibration combining conormal Gauss identity, inverse-coordinate calculus and the fundamental inequality. None of the references is claimed to state this packaged existence theorem; its chart, potential and bound are constructed from original Finsler data.
-/

/-!
# A calibration constructed from the original Finsler flow

Starting with only the actual smooth strongly convex Finsler structure and a nonzero
coordinate state, construct the scalar inverse time-coordinate potential. The actual
constant-energy position flow satisfies the spatial Gauss identity by first variation;
Euler homogeneity gives the time pairing. Differentiating the true inverse coordinate
identity therefore identifies the potential differential with normalized original momentum.

The actual Finsler fundamental inequality then proves its bound in every tangent direction,
including zero, and equality on the actual flow velocity. The local coordinates, constant
energy, Gauss pairing, inverse derivative and calibration are all conclusions, with no
extra foliation, frame, curvature, topology or prescribed-calibration assumption.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- Construct genuine local coordinate calibration, bounded in every original Finsler
direction and saturated on the actual constant-energy Euler--Lagrange position flow. -/
theorem exists_chartFlowCalibration (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) (t₀ : ℝ) :
    let L := F.chartEnergy x₀
    let p := fiberLegendre L z
    ∃ (g : OpenPartialHomeomorph (p.ker × ℝ) E) (ρ τ : ℝ) (u : E → ℝ),
      0 < ρ ∧ 0 < τ ∧
      g.source = ball (0 : p.ker) ρ ×ˢ Ioo (t₀ - τ) (t₀ + τ) ∧
      g (0, t₀) = z.1 ∧ z.1 ∈ g.target ∧
      ContDiffOn ℝ 2 g g.source ∧ ContDiffOn ℝ 2 u g.target ∧
      g.target ⊆ (extChartAt 𝓘(ℝ, E) x₀).target ∧
      positionMapPhase g (0, t₀) = z ∧
      (∀ q ∈ g.source, positionMapPhase g q ∈ chartEnergyDomain x₀ ∧
        F.chartLength x₀ (positionMapPhase g q) = F.chartLength x₀ z) ∧
      (∀ q ∈ g.source, u (g q) = (F.chartLength x₀ z : ℝ) * (q.2 - t₀)) ∧
      (∀ q ∈ g.source, HasDerivAt
        (fun t ↦ fiberLegendre L (positionMapPhase g (q.1, t)))
        (baseEnergyDifferential L (positionMapPhase g q)) q.2) ∧
      (∀ y ∈ g.target, ∀ w : E,
        fderiv ℝ u y w ≤ (F.chartLength x₀ (y, w) : ℝ)) ∧
      ∀ q ∈ g.source, fderiv ℝ u (g q) (positionMapPhase g q).2 =
        (F.chartLength x₀ (positionMapPhase g q) : ℝ) := by
  let L := F.chartEnergy x₀
  let p := fiberLegendre L z
  obtain ⟨g, ρ, τ, a, hρ, hτ, hsource, hc, hct, hcval, hci, hg, hi,
      htarget, hcenter, hphase, hinitial, hEL⟩ :=
    hF.exists_chartNormalPositionFlow x₀ hz t₀
  let D := ball (0 : p.ker) ρ ×ˢ Ioo (t₀ - τ) (t₀ + τ)
  have hDs : D = g.source := hsource.symm
  have hspace := fiberLegendre_positionMapPhase_fderiv_eq_zero
    (p := p) (g := (g : p.ker × ℝ → E)) (ρ := ρ) (t₀ := t₀) (T := τ)
    (C := L z) (x₀ := z.1) (a := a)
    (isOpen_chartEnergyDomain x₀) ((hF.contDiffOn_chartEnergy x₀).of_le (by norm_num)) hτ
    (hg.mono (fun _ hq ↦ hDs ▸ hq))
    (fun q hq ↦ (hphase q (hDs ▸ hq)).1)
    (fun q hq ↦ hEL q (hDs ▸ hq))
    (fun q hq ↦ (hphase q (hDs ▸ hq)).2) hinitial
  let s : ℝ := F.chartLength x₀ z
  let u : E → ℝ := flowTimePotential g s t₀
  have hs : 0 < s := NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)
  have hk : 2 * L z ≠ 0 := ne_of_gt (mul_pos (by norm_num) (F.chartEnergy_pos x₀ hz))
  have hratio : s / (2 * L z) = 1 / s := by
    have hL : L z = s ^ 2 / 2 := F.chartEnergy_eq_chartLength_sq x₀ z
    rw [hL]
    field_simp
  have hspeed : ∀ q ∈ g.source, (F.chartLength x₀ (positionMapPhase g q) : ℝ) = s := by
    intro q hq
    exact congrArg (fun r : ℝ≥0 ↦ (r : ℝ))
      (F.chartLength_eq_of_chartEnergy_eq x₀ (hphase q hq).2)
  have hdu : ∀ q ∈ g.source,
      fderiv ℝ u (g q) = (1 / s) • fiberLegendre L (positionMapPhase g q) := by
    intro q hq
    have hd := (hg.contDiffAt (g.open_source.mem_nhds hq)).differentiableAt (by norm_num)
    have hdi := (hi.contDiffAt (g.open_target.mem_nhds (g.map_source hq))).differentiableAt
      (by norm_num)
    have hqD : q ∈ D := hDs.symm ▸ hq
    have htime := positionMapPhase_snd_eq_fderiv hd
    have hzt := hF.chartEnergy_euler x₀ (hphase q hq).1
    change fiberLegendre L (positionMapPhase g q) (positionMapPhase g q).2 =
      2 * L (positionMapPhase g q) at hzt
    have henergy : L (positionMapPhase g q) = L z := (hphase q hq).2
    rw [henergy, htime] at hzt
    have hpair : ∀ d : p.ker × ℝ,
        fiberLegendre L (positionMapPhase g q) (fderiv ℝ g q d) = (2 * L z) * d.2 :=
      linearMap_pairing_of_spatial_time (fderiv ℝ g q)
        (fiberLegendre L (positionMapPhase g q)) (hspace q.1 hqD.1 q.2 hqD.2) hzt
    simpa only [u, hratio] using
      fderiv_flowTimePotential_of_pairing g hq hd hdi
        (fiberLegendre L (positionMapPhase g q)) hk hpair s t₀
  have hu : ContDiffOn ℝ 2 u g.target := contDiffOn_flowTimePotential g hi s t₀
  refine ⟨g, ρ, τ, u, hρ, hτ, hsource, hcval, hct, hg, hu, htarget,
    hcenter, ?_, ?_, hEL, ?_, ?_⟩
  · intro q hq
    exact ⟨(hphase q hq).1, F.chartLength_eq_of_chartEnergy_eq x₀ (hphase q hq).2⟩
  · intro q hq
    exact flowTimePotential_apply g s t₀ hq
  · intro y hy w
    have hq := g.map_target hy
    have h := hF.chartLegendre_div_le_chartLength x₀ (hphase (g.symm y) hq).1
      (hspeed (g.symm y) hq) w
    have hd := hdu (g.symm y) hq
    rw [g.right_inv hy] at hd
    rw [hd]
    change (1 / s) * fiberLegendre L (positionMapPhase g (g.symm y)) w ≤ _
    rw [one_div, ← div_eq_inv_mul]
    have hb : (positionMapPhase g (g.symm y)).1 = y := g.right_inv hy
    change fiberLegendre L (positionMapPhase g (g.symm y)) w / s ≤
      (F.chartLength x₀ ((positionMapPhase g (g.symm y)).1, w) : ℝ) at h
    rwa [hb] at h
  · intro q hq
    rw [hdu q hq]
    change (1 / s) * fiberLegendre L (positionMapPhase g q) (positionMapPhase g q).2 = _
    rw [one_div, ← div_eq_inv_mul]
    exact hF.chartLegendre_div_self_eq_chartLength x₀ (hphase q hq).1 (hspeed q hq)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
