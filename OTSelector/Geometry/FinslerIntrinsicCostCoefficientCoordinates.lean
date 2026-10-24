import OTSelector.Geometry.FinslerIntrinsicCostCoefficientCompact
import OTSelector.Analysis.Calculus.UniformQuadraticLinearCoordinates
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic

/-!
# Actual original distance remainders in the retained coefficient basis

The same original coefficient is evaluated in its fixed basis coordinates. The
basis inverse controls the radius and remainder scale, without an isometry premise.
-/

open Set Filter MeasureTheory Manifold Bundle Module Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The source-fixed intrinsic coefficient is exactly the matrix quadratic form
in the same retained basis, including its Taylor factor one half. -/
theorem intrinsicLengthQuadratic_basis_coordinates (F : ContinuousFinslerNorm E M)
    (bW : Basis ι ℝ W) (Γ : W → ℝ → M) (w : W) (a b : ℝ) (v : ι → ℝ) :
    F.intrinsicLengthQuadratic bW Γ w a b (0, bW.equivFun.symm v) =
      OTSelector.Reconstruction.matrixQuadratic
        (∫ t in a..b, (F.familyLabelHessianMatrix bW (fun q ↦ Γ q.1 q.2) (w, t))⁻¹)⁻¹ v := by
  simp only [intrinsicLengthQuadratic, sub_zero, LinearEquiv.apply_symm_apply,
    OTSelector.Reconstruction.matrixQuadratic]

namespace CalibratedLevelSeedPatch

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M] in
/-- The already-produced uniform source distance remainder transfers to the exact
fixed-basis displacement norm used by matrix coercivity and finite pressure. -/
theorem uniform_source_distance_deficit_in_coordinates
    (S : CalibratedLevelSeedPatch F u) (bW : Basis ι ℝ S.covector.ker)
    (K L : Set S.covector.ker) (T : Set (ℝ × ℝ))
    (hrem : ∀ η > 0, ∃ r > 0, ∀ w ∈ K, ∀ t ∈ T, ∀ v : S.covector.ker,
      ‖v‖ < r → w + v ∈ L →
        ‖(F.lengthEDist (S.curve w t.1) (S.curve (w + v) t.2)).toReal -
          u (S.curve (w + v) t.2) + u (S.curve w t.1) -
          F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 (0, v)‖ ≤ η * ‖v‖ ^ 2) :
    ∀ η > 0, ∃ r > 0, ∀ w ∈ K, ∀ t ∈ T, ∀ v : ι → ℝ,
      ‖v‖ < r → w + bW.equivFun.symm v ∈ L →
        ‖(F.lengthEDist (S.curve w t.1) (S.curve (w + bW.equivFun.symm v) t.2)).toReal -
          u (S.curve (w + bW.equivFun.symm v) t.2) + u (S.curve w t.1) -
          OTSelector.Reconstruction.matrixQuadratic
            (∫ s in t.1..t.2,
              (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, s))⁻¹)⁻¹ v‖ ≤
                η * ‖v‖ ^ 2 := by
  let error : (S.covector.ker × (ℝ × ℝ)) → S.covector.ker → ℝ := fun p v ↦
    (F.lengthEDist (S.curve p.1 p.2.1) (S.curve (p.1 + v) p.2.2)).toReal -
      u (S.curve (p.1 + v) p.2.2) + u (S.curve p.1 p.2.1) -
      F.intrinsicLengthQuadratic bW S.curve p.1 p.2.1 p.2.2 (0, v)
  have hh := uniform_quadratic_remainder_comp_clm bW.equivFunL.symm.toContinuousLinearMap
    (K ×ˢ T) error (fun p v ↦ p.1 + v ∈ L) (by
      intro η hη
      obtain ⟨r, hr, hb⟩ := hrem η hη
      exact ⟨r, hr, fun p hp v hv ha ↦ hb p.1 hp.1 p.2 hp.2 v hv ha⟩)
  intro η hη
  obtain ⟨r, hr, hb⟩ := hh η hη
  refine ⟨r, hr, ?_⟩
  intro w hw t ht v hv ha
  have he := hb (w, t) ⟨hw, ht⟩ v hv ha
  change ‖(F.lengthEDist (S.curve w t.1) (S.curve (w + bW.equivFun.symm v) t.2)).toReal -
    u (S.curve (w + bW.equivFun.symm v) t.2) + u (S.curve w t.1) -
    F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 (0, bW.equivFun.symm v)‖ ≤ _ at he
  rwa [F.intrinsicLengthQuadratic_basis_coordinates] at he


/-- The complete original geometric producer yields one large compact source core
with a uniform actual distance remainder in the unchanged coefficient basis. -/
theorem exists_compact_uniform_source_distance_coordinate_core
    (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCoordinateSourceLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (bW : Basis ι ℝ S.covector.ker)
    {m μ : Measure S.covector.ker} [m.IsAddHaarMeasure] (hμ : μ ≪ m)
    {H L : Set S.covector.ker} (hH : IsCompact H) (hfinite : μ H ≠ (∞ : ℝ≥0∞))
    (hHL : H ⊆ L) (hL : L ⊆ S.labels)
    {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (hactive : ∀ w ∈ H, ∀ t ∈ T, t.1 < t.2 ∧
      t.1 ∈ interior (S.calibrationTimes w) ∧ t.2 ∈ interior (S.calibrationTimes w))
    (hclock : ∀ y ∈ L, ∀ t ∈ T,
      t.1 ∈ S.calibrationTimes y ∧ t.2 ∈ S.calibrationTimes y)
    (hcoeff : ContinuousOn (fun p : S.covector.ker × (ℝ × ℝ) ↦
      (∫ t in p.2.1..p.2.2,
        (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (p.1, t))⁻¹)⁻¹)
      (H ×ˢ T))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ μ (H \ K) < ε ∧
      ∀ η > 0, ∃ r > 0, ∀ w ∈ K, ∀ t ∈ T, ∀ v : ι → ℝ,
        ‖v‖ < r → w + bW.equivFun.symm v ∈ L →
          ‖(F.lengthEDist (S.curve w t.1) (S.curve (w + bW.equivFun.symm v) t.2)).toReal -
            u (S.curve (w + bW.equivFun.symm v) t.2) + u (S.curve w t.1) -
            OTSelector.Reconstruction.matrixQuadratic
              (∫ s in t.1..t.2,
                (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, s))⁻¹)⁻¹ v‖ ≤ η * ‖v‖ ^ 2 := by
  obtain ⟨K, hKH, hK, hmass, hb⟩ := S.exists_compact_uniform_source_distance_core
    hF hcomplete hu bW hμ hH hfinite hHL hL hT hactive hclock hcoeff hε
  exact ⟨K, hKH, hK, hmass, S.uniform_source_distance_deficit_in_coordinates bW K L T hb⟩

end CalibratedLevelSeedPatch
end OTSelector.Geometry.ContinuousFinslerNorm
