import Mathlib.Analysis.Normed.Operator.Prod
import OTSelector.Analysis.Calculus.AffineEndpointVariation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.AffineEndpointParameter.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.AffineEndpointParameter`; the selected original proof blocks follow. -/
section

/-!
Conditions: A nontrivial compact time interval and normed endpoint phase parameter spaces.

Objects: Explicit affine endpoint perturbation and operator bound 1+1/(b−a), smooth in time.

Proof detail: Write the affine interpolation and constant velocity correction as continuous linear maps; estimate their norms by interval ordering.

Sources: Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Elementary explicit interpolation construction, independent of any chosen path regularity.
-/

/-!
# Linear endpoint derivative of the actual affine phase

The endpoint parameter enters the original position and its computed time velocity through
one continuous linear map. Its norm is uniformly bounded on the time interval, and the map
itself depends smoothly on time. These facts require no regularity of the central path.
-/

open Set
open scoped ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual endpoint derivative of position and velocity at time `t`. -/
def affineEndpointParameterMap (a b t : ℝ) : E →L[ℝ] E × E :=
  (((t - a) / (b - a)) • ContinuousLinearMap.id ℝ E).prod
    ((b - a)⁻¹ • ContinuousLinearMap.id ℝ E)

/-- The endpoint derivative acts by the two affine time coefficients. -/
@[simp] theorem affineEndpointParameterMap_apply (a b t : ℝ) (v : E) :
    affineEndpointParameterMap a b t v =
      (((t - a) / (b - a)) • v, (b - a)⁻¹ • v) := rfl

/-- The full endpoint phase displacement is exactly its linear parameter increment. -/
theorem affineEndpointPhase_sub_center (x : ℝ → E) (a b t : ℝ) (z : E) :
    affineEndpointPhase x a b (z, t) - (x t, deriv x t) =
      affineEndpointParameterMap a b t (z - x b) := by
  simp [affineEndpointPhase, affineEndpointVariation, Prod.sub_def]

/-- Differentiation in the endpoint parameter yields the actual fixed linear map, even for
an arbitrary central path and without a nondegenerate time-interval assumption. -/
theorem hasFDerivAt_affineEndpointPhase_parameter (x : ℝ → E) (a b t : ℝ) (z : E) :
    HasFDerivAt (fun w ↦ affineEndpointPhase x a b (w, t))
      (affineEndpointParameterMap a b t) z := by
  have hsub := (hasFDerivAt_id (𝕜 := ℝ) z).sub_const (x b)
  simpa only [affineEndpointPhase, affineEndpointVariation, affineEndpointParameterMap,
    Pi.smul_apply, id_eq] using
    ((hsub.const_smul ((t - a) / (b - a))).const_add (x t)).prodMk
      ((hsub.const_smul ((b - a)⁻¹)).const_add (deriv x t))

/-- On an increasing closed interval the endpoint derivative has a uniform norm bound. -/
theorem norm_affineEndpointParameterMap_le {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) :
    ‖affineEndpointParameterMap (E := E) a b t‖ ≤ 1 + (b - a)⁻¹ := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hi : 0 ≤ (b - a)⁻¹ := inv_nonneg.mpr hd.le
  have hc : 0 ≤ (t - a) / (b - a) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hc1 : (t - a) / (b - a) ≤ 1 := (div_le_one hd).mpr (by linarith [ht.2])
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [affineEndpointParameterMap_apply, Prod.norm_def, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hi, max_le_iff]
  constructor
  · nlinarith [norm_nonneg v, mul_le_mul_of_nonneg_right hc1 (norm_nonneg v)]
  · nlinarith [norm_nonneg v]

/-- The actual endpoint derivative is globally smooth in time, for any fixed endpoints. -/
theorem contDiff_affineEndpointParameterMap (a b : ℝ) :
    ContDiff ℝ ∞ (affineEndpointParameterMap (E := E) a b) := by
  let L : ((E →L[ℝ] E) × (E →L[ℝ] E)) →L[ℝ] (E →L[ℝ] E × E) :=
    (ContinuousLinearMap.prodₗᵢ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hleft : ContDiff ℝ ∞ (fun t : ℝ ↦
      ((t - a) / (b - a)) • ContinuousLinearMap.id ℝ E) :=
    ((contDiff_id.sub contDiff_const).div_const (b - a)).smul contDiff_const
  exact L.contDiff.comp (hleft.prodMk contDiff_const)

end OTSelector.Geometry

end
end
