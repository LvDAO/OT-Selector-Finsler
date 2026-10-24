import OTSelector.Geometry.FinslerIntrinsicCostCoefficientSeedUniform
import OTSelector.Analysis.Calculus.CompactUniformQuadraticCore

/-!
# Uniform original distance remainders on compact label cores

The actual distance expansion is uniformized on large compact subsets of any
compact coefficient core. Absolute allowed endpoints stay fixed throughout the
compact approximation; the original label law is retained.
-/

open Set Filter MeasureTheory Manifold Bundle Module Asymptotics Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Actual pair-coefficient continuity gives a compact core with a common distance
remainder radius for every accuracy, every calibrated time pair and every allowed
absolute endpoint pair. The core loses arbitrarily little of the original law. -/
theorem exists_compact_uniform_distance_core
    (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCompactDistanceLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
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
      ∀ η > 0, ∃ r > 0, ∀ w ∈ K, ∀ t ∈ T, ∀ y₁ ∈ L, ∀ y₂ ∈ L,
        ‖(y₁ - w, y₂ - w)‖ < r →
          ‖(F.lengthEDist (S.curve y₁ t.1) (S.curve y₂ t.2)).toReal -
            u (S.curve y₂ t.2) + u (S.curve y₁ t.1) -
            F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 (y₁ - w, y₂ - w)‖ ≤
              η * ‖(y₁ - w, y₂ - w)‖ ^ 2 := by
  let cost : (ℝ × ℝ) → S.covector.ker × S.covector.ker → ℝ := fun t y ↦
    (F.lengthEDist (S.curve y.1 t.1) (S.curve y.2 t.2)).toReal -
      u (S.curve y.2 t.2) + u (S.curve y.1 t.1)
  let q : S.covector.ker → (ℝ × ℝ) → S.covector.ker × S.covector.ker → ℝ :=
    fun w t ξ ↦ F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 ξ
  have hq : ∀ t ∈ T, ∀ y₁ ∈ L, ∀ y₂ ∈ L,
      ContinuousOn (fun w ↦ q w t (y₁ - w, y₂ - w)) H := by
    intro t ht y₁ _ y₂ _
    let v := bW.equivFun (y₂ - y₁)
    have hc : Continuous (fun A : Matrix ι ι ℝ ↦ (1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v))) := by
      unfold dotProduct Matrix.mulVec
      fun_prop
    have hsection := hcoeff.comp (continuous_id.prodMk continuous_const).continuousOn
      (show MapsTo (fun w : S.covector.ker ↦ (w, t)) H (H ×ˢ T) from fun w hw ↦ ⟨hw, ht⟩)
    have hh := hc.comp_continuousOn hsection
    simpa only [q, intrinsicLengthQuadratic, sub_sub_sub_cancel_right, v] using! hh
  have hae := Filter.Eventually.filter_mono (hμ.restrict H).ae_le
    (ae_restrict_of_ae_restrict_of_subset (hHL.trans hL)
      (S.ae_uniform_distance_deficit_intrinsic_quadratic hF hcomplete hu m bW))
  have hpoint : ∀ᵐ w ∂μ.restrict H, ∀ η > 0, ∃ r > 0,
      ∀ t ∈ T, ∀ y₁ ∈ L, ∀ y₂ ∈ L, ‖(y₁ - w, y₂ - w)‖ < r →
        |cost t (y₁, y₂) - q w t (y₁ - w, y₂ - w)| ≤ η * ‖(y₁ - w, y₂ - w)‖ ^ 2 := by
    filter_upwards [hae, ae_restrict_mem hH.measurableSet] with w hw hwH
    intro η hη
    obtain ⟨r, hr, hb⟩ := hw.2 T hT (hactive w hwH) η hη
    refine ⟨r, hr, ?_⟩
    intro t ht y₁ h₁ y₂ h₂ hdist
    have hξ₁ : y₁ - w ∈ S.distanceExpansionLabels w t.1 t.2 := by
      have he : w + (y₁ - w) = y₁ := by abel
      simpa only [distanceExpansionLabels, mem_ofPred_eq, he] using
        And.intro (hL h₁) (hclock y₁ h₁ t ht)
    have hξ₂ : y₂ - w ∈ S.distanceExpansionLabels w t.1 t.2 := by
      have he : w + (y₂ - w) = y₂ := by abel
      simpa only [distanceExpansionLabels, mem_ofPred_eq, he] using
        And.intro (hL h₂) (hclock y₂ h₂ t ht)
    have hh := hb t ht (y₁ - w, y₂ - w) hdist ⟨hξ₁, hξ₂⟩
    have he₁ : w + (y₁ - w) = y₁ := by abel
    have he₂ : w + (y₂ - w) = y₂ := by abel
    simpa only [he₁, he₂, Real.norm_eq_abs, cost, q] using hh
  obtain ⟨K, hKH, hK, hmass, hb⟩ :=
    OTSelector.Reconstruction.exists_compact_uniform_fixedEndpoint_quadratic_remainder
      hH hfinite id continuousOn_id L T cost q hq hpoint hε
  refine ⟨K, hKH, hK, hmass, ?_⟩
  simpa only [id_eq, Real.norm_eq_abs, cost, q] using hb

/-- On the same large compact label core, fixing the actual source yields the
original displacement-squared distance remainder for local pressure comparison. -/
theorem exists_compact_uniform_source_distance_core
    (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCompactSourceLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
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
      ∀ η > 0, ∃ r > 0, ∀ w ∈ K, ∀ t ∈ T, ∀ v : S.covector.ker,
        ‖v‖ < r → w + v ∈ L →
          ‖(F.lengthEDist (S.curve w t.1) (S.curve (w + v) t.2)).toReal -
            u (S.curve (w + v) t.2) + u (S.curve w t.1) -
            F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 (0, v)‖ ≤ η * ‖v‖ ^ 2 := by
  obtain ⟨K, hKH, hK, hmass, hb⟩ := S.exists_compact_uniform_distance_core
    hF hcomplete hu bW hμ hH hfinite hHL hL hT hactive hclock hcoeff hε
  refine ⟨K, hKH, hK, hmass, ?_⟩
  intro η hη
  obtain ⟨r, hr, hh⟩ := hb η hη
  refine ⟨r, hr, ?_⟩
  intro w hw t ht v hv hlabel
  have hn : ‖(w - w, (w + v) - w)‖ = ‖v‖ := by simp
  have hb := hh w hw t ht w (hHL (hKH hw)) (w + v) hlabel (hn ▸ hv)
  simpa only [sub_self, add_sub_cancel_left, Prod.norm_def, norm_zero,
    max_eq_right (norm_nonneg v)] using hb

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
