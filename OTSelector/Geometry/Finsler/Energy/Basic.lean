import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.HomogeneousEnergy
import OTSelector.Analysis.Convex.Legendre.LocalInverse
import OTSelector.Geometry.Finsler.Basic

/-!
## Lemma skeleton

* **Conditions:** A continuous positive absolutely homogeneous tangent length. Smooth slit energy and positivity of its actual fiber Hessian are separate fields of IsSmoothStronglyConvex; local inverse conclusions require finite dimension.
* **Objects:** The original energy F²/2 on the genuine tangent bundle, fixed-fiber energy and its model representation; the smooth strong-convexity predicate and actual local fiber Legendre inverse.
* **Proof detail:** Use square-length identities for continuity, positivity and degree-two homogeneity. Smooth fiber inclusion transfers total-bundle smoothness to each fiber; homogeneous-energy lemmas and the inverse function theorem supply the Legendre conclusions.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 2, pp. 304–305, smooth slit energy and positive fundamental tensor.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1, Proposition 1.1, p. 3; Section 1.1, Definition 1.2 and Remarks 1.3(4), pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=3
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8).
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 2, p. 308, derivative Legendre map and inverse, equation (2–12).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6

**Relationship to the sources:** The energy and added smooth strongly convex predicate match the usual Finsler setup, under the project reversible-length convention. Early lemmas require only the weaker length carrier. Tangent model equivalences are Lean bundle adapters; no norm instance substitutes the original length.
-/

/-!
# The actual Finsler energy on the tangent bundle

This module uses the original tangent length to define energy as one half its square.
Smoothness away from the zero section and positivity of its actual vertical Hessian
are the usual smooth strong-convex Finsler data. Fiber differentiability is derived
from smoothness on the total tangent bundle, using smooth fiber inclusion. The resulting
Legendre inverse is local within each fixed fiber; smooth base dependence and geodesic
flow are not asserted here. No global tangent norm instance is introduced.
-/

open Bundle Set Manifold
open scoped ContDiff Topology

noncomputable section

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

namespace ContinuousFinslerNorm

/-- The kinetic energy of the original tangent length, without a metric replacement. -/
def energy (F : ContinuousFinslerNorm E M) (p : TangentBundle 𝓘(ℝ, E) M) : ℝ :=
  (F.toFun p : ℝ) ^ 2 / 2

/-- The energy restricted to one genuine tangent fiber. -/
def fiberEnergy (F : ContinuousFinslerNorm E M) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) : ℝ := F.energy ⟨x, v⟩

variable (F : ContinuousFinslerNorm E M)

/-- The actual energy is continuous on the whole tangent bundle, including its zero section. -/
theorem continuous_energy : Continuous F.energy :=
  (NNReal.continuous_coe.comp F.continuous_toFun).pow 2 |>.div_const 2

/-- Energy is nonnegative on every tangent fiber. -/
theorem fiberEnergy_nonneg (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    0 ≤ F.fiberEnergy x v := div_nonneg (sq_nonneg _) (by norm_num)

/-- The energy vanishes on the zero section. -/
@[simp] theorem fiberEnergy_zero (x : M) : F.fiberEnergy x 0 = 0 := by
  simp [fiberEnergy, energy]

/-- Every nonzero tangent vector has strictly positive energy. -/
theorem fiberEnergy_pos (x : M) {v : TangentSpace 𝓘(ℝ, E) x} (hv : v ≠ 0) :
    0 < F.fiberEnergy x v := by
  exact div_pos (sq_pos_of_pos (NNReal.coe_pos.mpr (F.pos x v hv))) (by norm_num)

/-- Absolute homogeneity of length gives exact degree-two homogeneity of its energy. -/
theorem fiberEnergy_smul (x : M) (r : ℝ) (v : TangentSpace 𝓘(ℝ, E) x) :
    F.fiberEnergy x (r • v) = r ^ 2 * F.fiberEnergy x v := by
  simp only [fiberEnergy, energy, F.map_smul, NNReal.coe_mul, coe_nnnorm,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

include F in
/-- The slit tangent bundle is open, directly from positivity and continuity of length. -/
theorem isOpen_slitTangent : IsOpen {p : TangentBundle 𝓘(ℝ, E) M | p.2 ≠ 0} := by
  have heq : {p : TangentBundle 𝓘(ℝ, E) M | p.2 ≠ 0} = F.toFun ⁻¹' Ioi 0 := by
    ext ⟨x, v⟩
    simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
    constructor
    · exact F.pos x v
    · intro hp hz
      have hzero : F.toFun ⟨x, v⟩ = 0 := by
        change v = 0 at hz
        rw [hz]
        exact F.map_zero x
      exact (ne_of_gt hp) hzero
  rw [heq]
  exact isOpen_Ioi.preimage F.continuous_toFun

end ContinuousFinslerNorm

/-- The model representation identifies a vector with the corresponding vector in one fiber.
This reference norm is used only for differentiation; lengths are always evaluated by `F`. -/
def tangentFiberModelEquiv (x : M) : E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) x where
  toLinearEquiv := LinearEquiv.refl ℝ E
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- Inclusion of a fixed tangent fiber is smooth for its actual bundle chart structure. -/
theorem contMDiff_tangentFiber_inclusion (x : M) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun v : E ↦ (⟨x, tangentFiberModelEquiv x v⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
  intro v
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const, ?_⟩
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  convert ((e.continuousLinearMapAt ℝ x).comp
    (tangentFiberModelEquiv x).toContinuousLinearMap).contMDiffAt (n := ∞) using 1
  funext w
  exact (e.continuousLinearMapAt_apply_of_mem ℝ hx _).symm

namespace ContinuousFinslerNorm

/-- The actual energy in the fixed linear representation of a tangent fiber. -/
def fiberEnergyModel (F : ContinuousFinslerNorm E M) (x : M) (v : E) : ℝ :=
  F.fiberEnergy x (tangentFiberModelEquiv x v)

/-- The model representation preserves the exact energy homogeneity. -/
theorem fiberEnergyModel_smul (F : ContinuousFinslerNorm E M) (x : M) (r : ℝ) (v : E) :
    F.fiberEnergyModel x (r • v) = r ^ 2 * F.fiberEnergyModel x v := by
  simp only [fiberEnergyModel, _root_.map_smul, F.fiberEnergy_smul]

/-- Nonzero vectors have positive energy in the model representation. -/
theorem fiberEnergyModel_pos (F : ContinuousFinslerNorm E M) (x : M) {v : E}
    (hv : v ≠ 0) : 0 < F.fiberEnergyModel x v := by
  apply F.fiberEnergy_pos
  exact fun hz ↦ hv ((tangentFiberModelEquiv x).injective
    (hz.trans (_root_.map_zero (tangentFiberModelEquiv x)).symm))

/-- Standard smooth strongly convex data for the given length. The Hessian is the
actual second derivative of one half the squared length, not an auxiliary bilinear form. -/
structure IsSmoothStronglyConvex (F : ContinuousFinslerNorm E M) : Prop where
  contMDiffOn_energy : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
    F.energy {p : TangentBundle 𝓘(ℝ, E) M | p.2 ≠ 0}
  hessian_pos : ∀ (x : M) (v : E), v ≠ 0 → ∀ w : E, w ≠ 0 →
    0 < fderiv ℝ (fderiv ℝ (F.fiberEnergyModel x)) v w w

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)

include hF

/-- Fiber smoothness follows from total-bundle smoothness and smooth fiber inclusion. -/
theorem contDiffAt_fiberEnergyModel (x : M) {v : E} (hv : v ≠ 0) :
    ContDiffAt ℝ ∞ (F.fiberEnergyModel x) v := by
  have hv' : tangentFiberModelEquiv x v ≠ 0 :=
    fun hz ↦ hv ((tangentFiberModelEquiv x).injective
      (hz.trans (_root_.map_zero (tangentFiberModelEquiv x)).symm))
  have hmem : (⟨x, tangentFiberModelEquiv x v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈
      {p : TangentBundle 𝓘(ℝ, E) M | p.2 ≠ 0} := hv'
  have he := hF.contMDiffOn_energy.contMDiffAt (F.isOpen_slitTangent.mem_nhds hmem)
  exact (he.comp v (contMDiff_tangentFiber_inclusion x v)).contDiffAt

/-- Smoothness on the nonzero part of each actual fiber in its linear representation. -/
theorem contDiffOn_fiberEnergyModel (x : M) :
    ContDiffOn ℝ ∞ (F.fiberEnergyModel x) {v : E | v ≠ 0} :=
  fun _ hv ↦ (hF.contDiffAt_fiberEnergyModel x hv).contDiffWithinAt

/-- The actual fiber energy is differentiable at every nonzero vector. -/
theorem differentiableAt_fiberEnergyModel (x : M) {v : E} (hv : v ≠ 0) :
    DifferentiableAt ℝ (F.fiberEnergyModel x) v :=
  (hF.contDiffAt_fiberEnergyModel x hv).differentiableAt (by simp)

/-- The actual Legendre map is differentiable at every nonzero vector. -/
theorem differentiableAt_legendre (x : M) {v : E} (hv : v ≠ 0) :
    DifferentiableAt ℝ (fderiv ℝ (F.fiberEnergyModel x)) v :=
  ((hF.contDiffAt_fiberEnergyModel x hv).fderiv_right (m := 1) (by simp)).differentiableAt
    (by norm_num)

/-- Euler's identity for the original Finsler energy. -/
theorem fiberEnergy_euler (x : M) {v : E} (hv : v ≠ 0) :
    fderiv ℝ (F.fiberEnergyModel x) v v = 2 * F.fiberEnergyModel x v :=
  twoHomogeneous_fderiv_euler (fun r _ ↦ F.fiberEnergyModel_smul x r v)
    (hF.differentiableAt_fiberEnergyModel x hv)

/-- A nonzero velocity has a nonzero Legendre covector for the original energy. -/
theorem legendre_ne_zero (x : M) {v : E} (hv : v ≠ 0) :
    fderiv ℝ (F.fiberEnergyModel x) v ≠ 0 := by
  intro hz
  have he := hF.fiberEnergy_euler x hv
  rw [hz, zero_apply] at he
  have hp := F.fiberEnergyModel_pos x hv
  linarith

/-- The original energy's radial Hessian equals its Legendre covector. -/
theorem fiberEnergy_hessian_radial (x : M) {v : E} (hv : v ≠ 0) :
    fderiv ℝ (fderiv ℝ (F.fiberEnergyModel x)) v v =
      fderiv ℝ (F.fiberEnergyModel x) v :=
  twoHomogeneous_fderiv2_radial (fun r _ w ↦ F.fiberEnergyModel_smul x r w)
    (fun _ hw ↦ hF.differentiableAt_fiberEnergyModel x hw) hv
    (hF.differentiableAt_legendre x hv)

/-- Strong convexity makes the actual Legendre differential a continuous linear equivalence. -/
theorem exists_legendreDifferential_equiv [FiniteDimensional ℝ E] (x : M)
    {v : E} (hv : v ≠ 0) :
    ∃ e : E ≃L[ℝ] (E →L[ℝ] ℝ),
      HasFDerivAt (fderiv ℝ (F.fiberEnergyModel x)) e.toContinuousLinearMap v :=
  OTSelector.Geometry.exists_legendreDifferential_equiv
    (hF.differentiableAt_legendre x hv) (hF.hessian_pos x v hv)

/-- The original Finsler energy has a smooth local Legendre inverse between nonzero
velocities and covectors. Its derivative is the inverse of the actual energy Hessian. -/
theorem exists_smooth_legendre_local_inverse [FiniteDimensional ℝ E] (x : M)
    {v : E} (hv : v ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (E →L[ℝ] ℝ),
      (e : E → (E →L[ℝ] ℝ)) = fderiv ℝ (F.fiberEnergyModel x) ∧
      v ∈ e.source ∧ fderiv ℝ (F.fiberEnergyModel x) v ∈ e.target ∧
      e.source ⊆ {w : E | w ≠ 0} ∧ e.target ⊆ {p : E →L[ℝ] ℝ | p ≠ 0} ∧
      ContDiffOn ℝ ∞ (fderiv ℝ (F.fiberEnergyModel x)) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ ∀ p ∈ e.target,
        HasFDerivAt e.symm (ContinuousLinearMap.inverse
          (fderiv ℝ (fderiv ℝ (F.fiberEnergyModel x)) (e.symm p))) p :=
  OTSelector.Geometry.exists_smooth_legendre_local_inverse_slit
    (hF.contDiffOn_fiberEnergyModel x) (fun r _ w ↦ F.fiberEnergyModel_smul x r w)
    (hF.hessian_pos x) hv

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry
