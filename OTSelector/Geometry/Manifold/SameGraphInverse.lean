import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.SameGraphInverse.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.SameGraphInverse`; the selected original proof blocks follow. -/
section

/-!
Conditions: A given partial homeomorphism has the stated actual differentiable graph map at a point and nonzero longitudinal speed.

Objects: Differentiability and the explicit differential of that same inverse.

Proof detail: Show the actual differential is a block equivalence and apply the inverse-derivative theorem to the existing partial homeomorphism.

Sources: Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55).
Relation: Pointwise inverse-derivative consequence; it adds no C1 neighborhood hypothesis.
-/

/-!
# Regularity of the same actual graph inverse

A nonzero longitudinal derivative makes the genuine derivative of the given graph
coordinate map invertible. The inverse-function derivative theorem applies directly
to that same open partial homeomorphism, without selecting another local inverse.
-/

open Set
open scoped ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A given genuine graph inverse is differentiable at every longitudinally regular point. -/
theorem differentiableAt_curveGraphInverse_of_regular {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q))
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) :
    DifferentiableAt ℝ e.symm q := by
  let z := e.symm q
  let K := (ContinuousLinearMap.fst ℝ ℝ V).comp (fderiv ℝ γ z)
  let T := (ContinuousLinearMap.fst ℝ W ℝ).prod K
  have hD : HasFDerivAt e T z := by
    rw [he]
    exact hasFDerivAt_fst.prodMk hγ.hasFDerivAt.fst
  let d := ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 (fderiv ℝ γ z (0, 1)).1 hv)
  have hK (s : ℝ) : K (0, s) = d s := by
    have hs : ((0 : W), s) = s • (0, 1) := by ext <;> simp
    dsimp [K]
    rw [hs, map_smul]
    simp [d, ContinuousLinearEquiv.unitsEquivAut_apply]
  have hbij : Function.Bijective T := base_preserving_block_bijective K d hK
  let A := (LinearEquiv.ofBijective T.toLinearMap hbij).toContinuousLinearEquiv
  have hDA : HasFDerivAt e A.toContinuousLinearMap (e.symm q) := hD
  exact (e.hasFDerivAt_symm hq hDA).differentiableAt

/-- The actual derivative of that same inverse has the true old-time correction. -/
theorem curveGraph_inverse_fderiv_of_regular {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q))
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) (w : W) (s : ℝ) :
    fderiv ℝ e.symm q (w, s) =
      (w, (s - (fderiv ℝ γ (e.symm q) (w, 0)).1) /
        (fderiv ℝ γ (e.symm q) (0, 1)).1) :=
  curveGraph_inverse_fderiv_apply he hq hγ
    (differentiableAt_curveGraphInverse_of_regular he hq hγ hv) hv w s

end OTSelector.Geometry

end
end
