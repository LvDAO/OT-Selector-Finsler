import Mathlib.Analysis.Calculus.Deriv.Prod
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CurveGraphTime.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CurveGraphTime`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual graph inverse at nonzero longitudinal speed and the specified position/time differentiability.

Objects: Reciprocal clock derivative, recovered-time position identity and actual graph velocity.

Proof detail: Differentiate the inverse relation and compose the original position curve with the recovered time.

Sources: Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55).
Relation: Direct derivative calculation for the same actual inverse.
-/

/-!
# Actual time changes recovered from graph coordinates

The same graph-coordinate inverse retains the family label and supplies a scalar
change of time. Its derivative is the inverse longitudinal velocity of the original
curve. The position slice is the original curve at precisely this recovered time.
-/

open Set Filter
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual recovered old time has derivative equal to inverse longitudinal velocity. -/
theorem curveGraphTime_hasDerivAt {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) :
    HasDerivAt (fun s ↦ (e.symm (q.1, s)).2)
      (fderiv ℝ γ (e.symm q) (0, 1)).1⁻¹ q.2 := by
  have hd := hi.hasFDerivAt.snd.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  have heq := curveGraph_inverse_fderiv_apply he hq hγ hi hv (0 : W) 1
  have hz : fderiv ℝ γ (e.symm q) ((0 : W), (0 : ℝ)) = 0 := map_zero _
  rw [hz] at heq
  simpa [heq] using! hd

omit [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The graph position uses the same original family member at the recovered time. -/
theorem curveGraphPosition_eq_slice {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target) :
    curveGraphPosition γ e q = γ (q.1, (e.symm q).2) := by
  change γ (e.symm q) = _
  congr 1
  exact Prod.ext (curveGraph_inverse_components he hq).1 rfl

/-- At a fixed family label, the graph position has the actual rescaled old velocity. -/
theorem curveGraphPosition_slice_hasDerivAt {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q : W × ℝ} (hq : q ∈ e.target)
    (hγ : DifferentiableAt ℝ γ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ γ (e.symm q) (0, 1)).1 ≠ 0) :
    HasDerivAt (fun s ↦ curveGraphPosition γ e (q.1, s))
      ((fderiv ℝ γ (e.symm q) (0, 1)).1⁻¹ • fderiv ℝ γ (e.symm q) (0, 1)) q.2 := by
  have hd : DifferentiableAt ℝ (curveGraphPosition γ e) q := hγ.comp q hi
  have ht := hd.hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  simpa only [Function.comp_def, id_eq,
    curveGraphPosition_time_fderiv he hq hγ hi hv] using! ht

end OTSelector.Geometry

end
end
