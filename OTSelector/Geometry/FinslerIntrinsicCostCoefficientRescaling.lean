import OTSelector.Geometry.FinslerIntrinsicCostCoefficientRelative

/-!
# Rescaled original distance and the same intrinsic quadratic coefficient

The genuine distance deficit divided by the square of a local scale retains its
uniform relative quadratic bound. The original source, basis and coefficient stay
fixed while the actual target displacement is scaled.
-/

open Set MeasureTheory Manifold Module Matrix
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

/-- Dividing an actual relative cost estimate by the square of the same nonzero
scale preserves its relative error and its homogeneous quadratic coefficient. -/
theorem norm_div_sq_sub_quadratic_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (cost q : W → ℝ) (hq : ∀ (s : ℝ) w, q (s • w) = s ^ 2 * q w)
    {η s : ℝ} {v : W} (hs : s ≠ 0)
    (h : ‖cost (s • v) - q (s • v)‖ ≤ η * q (s • v)) :
    ‖cost (s • v) / s ^ 2 - q v‖ ≤ η * q v := by
  rw [hq] at h
  have hs₂ : s ^ 2 ≠ 0 := pow_ne_zero _ hs
  calc
    ‖cost (s • v) / s ^ 2 - q v‖ = ‖(cost (s • v) - s ^ 2 * q v) / s ^ 2‖ := by
      congr 1
      field_simp
    _ = ‖cost (s • v) - s ^ 2 * q v‖ / s ^ 2 := by
      rw [norm_div, Real.norm_of_nonneg (sq_nonneg s)]
    _ ≤ (η * (s ^ 2 * q v)) / s ^ 2 := div_le_div_of_nonneg_right h (sq_nonneg s)
    _ = η * q v := by field_simp

namespace ContinuousFinslerNorm.CalibratedLevelSeedPatch

set_option backward.isDefEq.respectTransparency false

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual uniform source-distance estimate directly controls every local
rescaling in its retained basis. The only size restriction is on the actual scaled
displacement; no bound is imposed on the unscaled coordinate vector. -/
theorem uniform_relative_source_distance_rescaling
    (S : CalibratedLevelSeedPatch F u) (bW : Basis ι ℝ S.covector.ker)
    (K L : Set S.covector.ker) (T : Set (ℝ × ℝ))
    (hrem : ∀ η > 0, ∃ r > 0, ∀ w ∈ K, ∀ t ∈ T, ∀ v : ι → ℝ,
      ‖v‖ < r → w + bW.equivFun.symm v ∈ L →
        ‖(F.lengthEDist (S.curve w t.1) (S.curve (w + bW.equivFun.symm v) t.2)).toReal -
          u (S.curve (w + bW.equivFun.symm v) t.2) + u (S.curve w t.1) -
          OTSelector.Reconstruction.matrixQuadratic
            (∫ a in t.1..t.2,
              (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, a))⁻¹)⁻¹ v‖ ≤
                η * OTSelector.Reconstruction.matrixQuadratic
                  (∫ a in t.1..t.2,
                    (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, a))⁻¹)⁻¹ v) :
    ∀ η > 0, ∃ r > 0, ∀ w ∈ K, ∀ t ∈ T, ∀ (s : ℝ), s ≠ 0 → ∀ v : ι → ℝ,
      |s| * ‖v‖ < r → w + s • bW.equivFun.symm v ∈ L →
        ‖((F.lengthEDist (S.curve w t.1) (S.curve (w + s • bW.equivFun.symm v) t.2)).toReal -
          u (S.curve (w + s • bW.equivFun.symm v) t.2) + u (S.curve w t.1)) / s ^ 2 -
          OTSelector.Reconstruction.matrixQuadratic
            (∫ a in t.1..t.2,
              (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, a))⁻¹)⁻¹ v‖ ≤
                η * OTSelector.Reconstruction.matrixQuadratic
                  (∫ a in t.1..t.2,
                    (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, a))⁻¹)⁻¹ v := by
  intro η hη
  obtain ⟨r, hr, hb⟩ := hrem η hη
  refine ⟨r, hr, ?_⟩
  intro w hw t ht s hs v hv ha
  let cost : (ι → ℝ) → ℝ := fun v ↦
    (F.lengthEDist (S.curve w t.1) (S.curve (w + bW.equivFun.symm v) t.2)).toReal -
      u (S.curve (w + bW.equivFun.symm v) t.2) + u (S.curve w t.1)
  let A := (∫ a in t.1..t.2,
    (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, a))⁻¹)⁻¹
  have hmap : bW.equivFun.symm (s • v) = s • bW.equivFun.symm v :=
    bW.equivFun.symm.map_smul s v
  have he := hb w hw t ht (s • v)
    (by simpa only [norm_smul, Real.norm_eq_abs] using hv)
    (by simpa only [hmap] using ha)
  have hh := norm_div_sq_sub_quadratic_le cost
    (OTSelector.Reconstruction.matrixQuadratic A)
    (OTSelector.Reconstruction.matrixQuadratic_smul A) hs he
  simpa only [cost, A, hmap] using hh

end ContinuousFinslerNorm.CalibratedLevelSeedPatch
end OTSelector.Geometry
