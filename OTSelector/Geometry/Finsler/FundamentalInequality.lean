import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Convex.Deriv
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
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic

/-!
## Lemma skeleton

* **Conditions:** Nonnegative two-homogeneous energy, C2 away from zero, with nonnegative Hessian; smooth strongly convex Finsler energy for the fiber specialization.
* **Objects:** Global convexity and the supporting Legendre covector bound dL(v)w≤F(v)F(w).
* **Proof detail:** Prove convexity on lines, treating a line through zero via homogeneity; apply the first-order supporting inequality after positive rescaling and Euler identity.

## Mathematical sources

* Stephen Boyd; Lieven Vandenberghe, *Convex Optimization (2004)*, Sections 3.1.3–3.1.4, pp. 69–71, first-order support inequality (3.2) and positive-semidefinite Hessian criterion.
  https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006 author manuscript)*, Section 1.1, Definition 1.2, Remarks 1.3 and Propositions 1.4–1.5, pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=4

**Relationship to the sources:** The slit-C2-to-global-convexity step is supplied locally. The final fiber inequality is the classical Finsler fundamental inequality; generic support/Hessian lemmas also work in normed spaces.
-/

/-!
# The fundamental inequality of the actual Finsler norm

The original fiber energy is proved convex from its actual Hessian and its degree-two
homogeneity. On an affine line avoiding zero, the true second derivative is a nonnegative
Hessian evaluation. On a line passing through zero, absolute homogeneity identifies the
entire energy restriction with a nonnegative quadratic polynomial. This handles the zero
vector and opposite directions without assuming differentiability of energy at zero.

A supporting differential inequality follows from convexity. Applying it to the positive
rescaling `F(v) / F(w) • w` and using the already proved Euler identity yields
`D(½ F²)(v)[w] ≤ F(v) F(w)`. The zero comparison vector is handled directly.

The final geometric theorem uses only the given `ContinuousFinslerNorm` and its
`IsSmoothStronglyConvex` data. Convexity and the supporting inequality are proved here;
no triangle inequality, auxiliary metric, or inner product is assumed. The existing
length structure is reversible (absolutely homogeneous). These results also hold in an
infinite-dimensional real normed model and do not assert length minimization by themselves.
-/

open Set Filter AffineMap
open scoped Topology ContDiff Manifold

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- A reversible degree-two energy with nonnegative actual Hessian away from zero
is convex on every affine line, including lines through the origin. -/
theorem convexOn_twoHomogeneous_line
    {L : E → ℝ} (hhom : ∀ r : ℝ, ∀ v : E, L (r • v) = r ^ 2 * L v)
    (hnonneg : ∀ v, 0 ≤ L v)
    (hL : ∀ v : E, v ≠ 0 → ContDiffAt ℝ 2 L v)
    (hH : ∀ v : E, v ≠ 0 → ∀ w : E,
      0 ≤ fderiv ℝ (fderiv ℝ L) v w w) (x w : E) :
    ConvexOn ℝ univ (fun t : ℝ ↦ L (x + t • w)) := by
  by_cases hz : ∃ t : ℝ, x + t • w = 0
  · obtain ⟨t₀, ht₀⟩ := hz
    have heq : ∀ t : ℝ, L (x + t • w) = (t - t₀) ^ 2 * L w := by
      intro t
      have hx : x = -(t₀ • w) := eq_neg_of_add_eq_zero_left ht₀
      rw [hx]
      have hv : -(t₀ • w) + t • w = (t - t₀) • w := by module
      rw [hv, hhom]
    simp_rw [heq]
    refine ⟨convex_univ, ?_⟩
    intro u _ v _ a b ha hb hab
    simp only [smul_eq_mul]
    have hLw := hnonneg w
    have hprod : 0 ≤ a * b * (u - v) ^ 2 * L w := by positivity
    have hid : a * ((u - t₀) ^ 2 * L w) + b * ((v - t₀) ^ 2 * L w) -
        ((a * u + b * v - t₀) ^ 2 * L w) = a * b * (u - v) ^ 2 * L w := by
      have hb' : b = 1 - a := by linarith
      rw [hb']
      ring
    linarith
  · push Not at hz
    have hg : ContDiff ℝ 2 (fun t : ℝ ↦ L (x + t • w)) := by
      rw [contDiff_iff_contDiffAt]
      intro t
      exact (hL _ (hz t)).comp t (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
    have hderiv : ∀ t : ℝ, deriv (fun r : ℝ ↦ L (x + r • w)) t =
        fderiv ℝ L (x + t • w) w := by
      intro t
      have hp : HasDerivAt (fun r : ℝ ↦ x + r • w) w t := by
        simpa only [Pi.add_apply, zero_add, id_eq, one_smul] using
        (hasDerivAt_const t x).fun_add ((hasDerivAt_id t).smul_const w)
      exact (((hL _ (hz t)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
        t hp).deriv
    apply convexOn_univ_of_deriv2_nonneg
      (hg.differentiable (by norm_num)) (hg.differentiable_deriv_two)
    intro t
    have hp : HasDerivAt (fun r : ℝ ↦ x + r • w) w t := by
      simpa only [Pi.add_apply, zero_add, id_eq, one_smul] using
        (hasDerivAt_const t x).fun_add ((hasDerivAt_id t).smul_const w)
    have hD := ((hL _ (hz t)).fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
    have hcomp := hD.comp_hasDerivAt t hp
    have hh := hcomp.clm_apply (hasDerivAt_const t w)
    simp only [map_zero, add_zero, Function.comp_def] at hh
    have he : deriv (fun r : ℝ ↦ L (x + r • w)) =
        (fun r ↦ fderiv ℝ L (x + r • w) w) := funext hderiv
    change 0 ≤ deriv (deriv (fun r : ℝ ↦ L (x + r • w))) t
    rw [he, hh.deriv]
    exact hH _ (hz t) w

/-- Actual Hessian nonnegativity and degree-two homogeneity imply global fiber convexity. -/
theorem convexOn_twoHomogeneous
    {L : E → ℝ} (hhom : ∀ r : ℝ, ∀ v : E, L (r • v) = r ^ 2 * L v)
    (hnonneg : ∀ v, 0 ≤ L v)
    (hL : ∀ v : E, v ≠ 0 → ContDiffAt ℝ 2 L v)
    (hH : ∀ v : E, v ≠ 0 → ∀ w : E,
      0 ≤ fderiv ℝ (fderiv ℝ L) v w w) : ConvexOn ℝ univ L := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := (convexOn_twoHomogeneous_line hhom hnonneg hL hH x (y - x)).2
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero,
    one_smul, add_sub_cancel] at h
  have hv : x + b • (y - x) = a • x + b • y := by
    have ha' : a = 1 - b := by linarith
    rw [ha']
    module
  rwa [hv] at h

/-- A differentiable convex energy lies above its tangent functional. -/
theorem support_of_convexOn_univ {L : E → ℝ} (hconv : ConvexOn ℝ univ L)
    {v : E} (hv : DifferentiableAt ℝ L v) (w : E) :
    fderiv ℝ L v (w - v) ≤ L w - L v := by
  have hc : ConvexOn ℝ univ (L ∘ (lineMap v w : ℝ →ᵃ[ℝ] E)) := by
    simpa using hconv.comp_affineMap (lineMap v w)
  have hv' : HasFDerivAt L (fderiv ℝ L v) (lineMap v w (0 : ℝ)) := by
    simpa using hv.hasFDerivAt
  have hd := hv'.comp_hasDerivAt 0 (hasDerivAt_lineMap (a := v) (b := w) (x := (0 : ℝ)))
  have hs := hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hd
  simpa [slope_def_field] using hs

/-- The positive-value branch of the fundamental inequality, given convexity and Euler's identity. -/
theorem fundamentalInequality_of_convex_positive {L F : E → ℝ}
    (hconv : ConvexOn ℝ univ L) {v w : E} (hv : DifferentiableAt ℝ L v)
    (hFv : 0 < F v) (hFw : 0 < F w)
    (hLv : L v = (F v) ^ 2 / 2) (hLw : L w = (F w) ^ 2 / 2)
    (heuler : fderiv ℝ L v v = 2 * L v)
    (hhom : ∀ r : ℝ, 0 < r → L (r • w) = r ^ 2 * L w) :
    fderiv ℝ L v w ≤ F v * F w := by
  have ht : 0 < F v / F w := div_pos hFv hFw
  have hs := support_of_convexOn_univ hconv hv ((F v / F w) • w)
  rw [map_sub, map_smul, smul_eq_mul, heuler, hhom _ ht, hLv, hLw] at hs
  have hcancel : (F v / F w) ^ 2 * ((F w) ^ 2 / 2) = (F v) ^ 2 / 2 := by
    field_simp
  rw [hcancel] at hs
  have hscaled : F v / F w * fderiv ℝ L v w ≤ F v / F w * (F v * F w) := by
    have hc : F v / F w * (F v * F w) = (F v) ^ 2 := by
      field_simp
    rw [hc]
    linarith
  exact (mul_le_mul_iff_right₀ ht).mp hscaled

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] {F : ContinuousFinslerNorm E M}

/-- The actual Finsler fiber energy is convex, including across its zero vector. -/
theorem convexOn_fiberEnergyModel (hF : F.IsSmoothStronglyConvex) (x : M) :
    ConvexOn ℝ univ (F.fiberEnergyModel x) := by
  apply convexOn_twoHomogeneous (F.fiberEnergyModel_smul x)
    (fun v ↦ F.fiberEnergy_nonneg x (tangentFiberModelEquiv x v))
    (fun v hv ↦ (hF.contDiffAt_fiberEnergyModel x hv).of_le (by simp))
  intro v hv w
  by_cases hw : w = 0
  · subst w
    simp
  · exact (hF.hessian_pos x v hv w hw).le

/-- Fundamental inequality for the original Finsler norm and its actual energy derivative.
The comparison vector can be zero or point in any direction. -/
theorem fiber_fundamental_inequality (hF : F.IsSmoothStronglyConvex) (x : M)
    {v : E} (hv : v ≠ 0) (w : E) :
    fderiv ℝ (F.fiberEnergyModel x) v w ≤
      (F.toFun ⟨x, tangentFiberModelEquiv x v⟩ : ℝ) *
        (F.toFun ⟨x, tangentFiberModelEquiv x w⟩ : ℝ) := by
  by_cases hw : w = 0
  · subst w
    simp
  · let G : E → ℝ := fun u ↦ (F.toFun ⟨x, tangentFiberModelEquiv x u⟩ : ℝ)
    have hG (u : E) (hu : u ≠ 0) : 0 < G u := by
      apply NNReal.coe_pos.mpr
      apply F.pos
      exact fun hz ↦ hu ((tangentFiberModelEquiv x).injective
        (hz.trans (_root_.map_zero (tangentFiberModelEquiv x)).symm))
    exact fundamentalInequality_of_convex_positive (F := G)
      (hF.convexOn_fiberEnergyModel x) (hF.differentiableAt_fiberEnergyModel x hv)
      (hG v hv) (hG w hw) rfl rfl (hF.fiberEnergy_euler x hv)
      (fun r _ ↦ F.fiberEnergyModel_smul x r w)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
