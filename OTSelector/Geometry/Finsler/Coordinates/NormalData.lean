import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional smooth strongly convex Finsler data and a prescribed nonzero chart position/velocity state; positivity and scaling helpers use their explicitly weaker hypotheses.
* **Objects:** A smooth local velocity field with the original constant energy, and a positive scalar field making its momentum proportional to the central momentum.
* **Proof detail:** Fix the central momentum and use the true joint Legendre inverse to obtain a smooth velocity field. Multiply by the positive square root of the energy ratio; degree-two energy and degree-one Legendre scaling enforce the energy and conormal identities.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8).
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1, Proposition 1.1, p. 3; Section 1.1, Definition 1.2 and Remarks 1.3(4), pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=3
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 2, p. 308, derivative Legendre map and inverse, equation (2–12).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
  https://www.jirka.org/ra/realanal2.pdf#page=38

**Relationship to the sources:** This is a derived constant-energy conormal initialization from Legendre inversion and homogeneous energy, designed for the local Gauss construction. No normal field, minimizing property or Riemannian normal-coordinate theorem is assumed.
-/

/-!
# Smooth constant-energy normal data from an actual Finsler state

At any nonzero chart state, the actual smooth Legendre inverse gives a local velocity
field with constant momentum. Positive square-root rescaling keeps the original energy
constant while making the new momentum a positive scalar multiple of that same covector.
The resulting field equals the original velocity at the center. In particular its
momentum annihilates the kernel of the original covector, without an additional
geometric condition. This constructs initial data for a local calibration argument;
it does not assert that a calibration or minimizing curve has already been constructed.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

namespace ContinuousFinslerNorm

/-- Actual Finsler coordinate energy is positive at every slit chart state. -/
theorem chartEnergy_pos (F : ContinuousFinslerNorm E M) (x₀ : M)
    {z : E × E} (hz : z ∈ chartEnergyDomain x₀) : 0 < F.chartEnergy x₀ z := by
  rw [show z = (z.1, z.2) from rfl, F.chartEnergy_eq_fiberEnergyModel x₀ hz.1]
  apply F.fiberEnergyModel_pos
  exact fun h ↦ hz.2 ((chartFiberEquiv x₀ hz.1).injective
    (h.trans (_root_.map_zero (chartFiberEquiv x₀ hz.1)).symm))

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M}

/-- The genuine coordinate momentum scales linearly under positive velocity scaling. -/
theorem chartLegendre_pos_smul (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {x v : E} (hx : x ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (hv : v ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    fiberLegendre (F.chartEnergy x₀) (x, r • v) =
      r • fiberLegendre (F.chartEnergy x₀) (x, v) := by
  apply twoHomogeneous_fderiv_pos_smul (fun a _ w ↦ F.chartEnergy_smul x₀ hx a w)
    ?_ hv hr
  intro w hw
  have hzw : (x, w) ∈ chartEnergyDomain x₀ := ⟨hx, hw⟩
  have h := ((hF.contDiffOn_chartEnergy x₀).contDiffAt
    ((isOpen_chartEnergyDomain x₀).mem_nhds hzw)).differentiableAt (by simp)
  exact h.comp w ((differentiableAt_const x).prodMk differentiableAt_id)

/-- Every slit chart state extends to a smooth constant-energy velocity field whose
momenta are positive multiples of the original momentum. All local data are constructed. -/
theorem exists_constantEnergy_normalData [FiniteDimensional ℝ E]
    (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {z : E × E} (hz : z ∈ chartEnergyDomain x₀) :
    ∃ (U : Set E) (v : E → E) (a : E → ℝ),
      IsOpen U ∧ z.1 ∈ U ∧ ContDiffOn ℝ ∞ v U ∧ ContDiffOn ℝ ∞ a U ∧
      v z.1 = z.2 ∧ a z.1 = 1 ∧
      0 < fiberLegendre (F.chartEnergy x₀) z z.2 ∧
      ∀ x ∈ U, (x, v x) ∈ chartEnergyDomain x₀ ∧ 0 < a x ∧
        F.chartEnergy x₀ (x, v x) = F.chartEnergy x₀ z ∧
        fiberLegendre (F.chartEnergy x₀) (x, v x) =
          a x • fiberLegendre (F.chartEnergy x₀) z := by
  let L := F.chartEnergy x₀
  let p := fiberLegendre L z
  obtain ⟨e, he, hzs, hzt, hsub, hG, _, _, _⟩ :=
    hF.exists_smooth_chartHamiltonian x₀ hz
  let U : Set E := {x | (x, p) ∈ e.target}
  let w : E → E := fun x ↦ (e.symm (x, p)).2
  have hU : IsOpen U := e.open_target.preimage (continuous_id.prodMk continuous_const)
  have hzU : z.1 ∈ U := hzt
  have hmem (x : E) (hx : x ∈ U) : (x, w x) ∈ chartEnergyDomain x₀ := by
    have hb := (parametricLegendre_inverse_components he hx).1
    have h := hsub (e.map_target hx)
    have heq : e.symm (x, p) = (x, w x) := Prod.ext hb rfl
    rwa [heq] at h
  have hw : ContDiffOn ℝ ∞ w U :=
    (hG.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ hx)).snd
  have hw₀ : w z.1 = z.2 := by
    change (e.symm (parametricLegendre L z)).2 = z.2
    rw [← he, e.left_inv hzs]
  have hmomentum (x : E) (hx : x ∈ U) : fiberLegendre L (x, w x) = p := by
    have h := parametricLegendre_inverse_components he hx
    have heq : e.symm (x, p) = (x, w x) := Prod.ext h.1 rfl
    simpa only [heq] using h.2
  have henergy : ContDiffOn ℝ ∞ (fun x ↦ L (x, w x)) U :=
    (hF.contDiffOn_chartEnergy x₀).comp (contDiffOn_id.prodMk hw) hmem
  have hpositive (x : E) (hx : x ∈ U) : 0 < L (x, w x) :=
    F.chartEnergy_pos x₀ (hmem x hx)
  have hzpos : 0 < L z := F.chartEnergy_pos x₀ hz
  let a : E → ℝ := fun x ↦ Real.sqrt (L z / L (x, w x))
  have ha : ContDiffOn ℝ ∞ a U :=
    (contDiffOn_const.div henergy (fun x hx ↦ (hpositive x hx).ne')).sqrt
      (fun x hx ↦ (div_pos hzpos (hpositive x hx)).ne')
  have ha_pos (x : E) (hx : x ∈ U) : 0 < a x :=
    Real.sqrt_pos.2 (div_pos hzpos (hpositive x hx))
  have ha₀ : a z.1 = 1 := by
    dsimp only [a]
    rw [hw₀, show (z.1, z.2) = z from rfl, div_self hzpos.ne', Real.sqrt_one]
  refine ⟨U, fun x ↦ a x • w x, a, hU, hzU, ha.smul hw, ha, ?_, ha₀, ?_, ?_⟩
  · change a z.1 • w z.1 = z.2
    rw [ha₀, one_smul, hw₀]
  · rw [hF.chartEnergy_euler x₀ hz]
    exact mul_pos (by norm_num) hzpos
  · intro x hx
    have hm := hmem x hx
    have hap := ha_pos x hx
    refine ⟨⟨hm.1, smul_ne_zero hap.ne' hm.2⟩, hap, ?_, ?_⟩
    · rw [F.chartEnergy_smul x₀ hm.1]
      change (Real.sqrt (L z / L (x, w x))) ^ 2 * L (x, w x) = L z
      rw [Real.sq_sqrt (div_pos hzpos (hpositive x hx)).le]
      exact div_mul_cancel₀ _ (hpositive x hx).ne'
    · rw [hF.chartLegendre_pos_smul x₀ hm.1 hm.2 hap, hmomentum x hx]

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry
