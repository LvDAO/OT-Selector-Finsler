import OTSelector.Geometry.FinslerIntrinsicCostCoefficientCoordinates

/-!
# Relative original distance errors on compact intrinsic coefficient cores

The actual positive inverse compliance gives its own uniform lower bound.
Combining it with the original distance expansion yields relative quadratic
errors for all sufficiently small allowed displacements in the retained basis.
-/

open Set Filter MeasureTheory Manifold Bundle Module Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- On one arbitrarily accurate compact core, the actual source distance cost
has uniformly small relative error against its own intrinsic quadratic coefficient.
Coercivity is produced from this same actual coefficient field. -/
theorem exists_compact_uniform_relative_source_distance_core
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
    (hpos : ∀ w ∈ H, ∀ t ∈ T,
      ((∫ s in t.1..t.2,
        (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, s))⁻¹)⁻¹).PosDef)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ μ (H \ K) < ε ∧
      ∀ η > 0, ∃ r > 0, ∀ w ∈ K, ∀ t ∈ T, ∀ v : ι → ℝ,
        ‖v‖ < r → w + bW.equivFun.symm v ∈ L →
          ‖(F.lengthEDist (S.curve w t.1) (S.curve (w + bW.equivFun.symm v) t.2)).toReal -
            u (S.curve (w + bW.equivFun.symm v) t.2) + u (S.curve w t.1) -
            OTSelector.Reconstruction.matrixQuadratic
              (∫ s in t.1..t.2,
                (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, s))⁻¹)⁻¹ v‖ ≤ η *
                OTSelector.Reconstruction.matrixQuadratic
                  (∫ s in t.1..t.2,
                    (F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, s))⁻¹)⁻¹ v := by
  obtain ⟨K, hKH, hK, hmass, hb⟩ := S.exists_compact_uniform_source_distance_coordinate_core
    hF hcomplete hu bW hμ hH hfinite hHL hL hT hactive hclock hcoeff hε
  obtain ⟨c, hc, hbound⟩ :=
    OTSelector.Reconstruction.exists_uniform_matrixQuadratic_lower_bound (hH.prod hT)
      hcoeff (fun p hp ↦ hpos p.1 hp.1 p.2 hp.2)
  refine ⟨K, hKH, hK, hmass, ?_⟩
  intro η hη
  obtain ⟨r, hr, hh⟩ := hb (η * c) (mul_pos hη hc)
  refine ⟨r, hr, ?_⟩
  intro w hw t ht v hv ha
  have he := hh w hw t ht v hv ha
  have hl := mul_le_mul_of_nonneg_left (hbound (w, t) ⟨hKH hw, ht⟩ v) hη.le
  exact he.trans (by simpa only [mul_assoc] using hl)

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
