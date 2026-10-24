import OTSelector.Reconstruction.FinslerOriginalCompletePath

/-!
# Exact endpoint balance along every complete original path

Integration of a test-function derivative along the actual original compliance path gives
exactly the difference between its unchanged target and source values.  The result is the
one-edge distributional divergence identity needed when the full current is summed.
-/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The complete original path is continuous through both actual physical endpoints. -/
theorem continuousOn_originalSeedCompletePath (hF : F.IsSmoothStronglyConvex)
    (hw : w ∈ S.labels) (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) :
    ContinuousOn (originalSeedCompletePath S w x m) (Icc m.1.1 m.1.2) := by
  intro c hc
  exact (D.hasDerivAt_originalSeedCompletePath hF hw x m ha
    ⟨by linarith [ha.1, hc.1], by linarith [hb.2, hc.2]⟩).continuousAt.continuousWithinAt

/-- The chain-rule readout along the full original physical path is interval integrable. -/
theorem intervalIntegrable_originalSeedCompletePath_testDerivative
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 ≤ m.1.2)
    {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    IntervalIntegrable (fun c ↦ fderiv ℝ φ (originalSeedCompletePath S w x m c)
      (originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m))
      volume m.1.1 m.1.2 := by
  have hpath := D.continuousOn_originalSeedCompletePath hF hw x m ha hb
  have hsub : MapsTo (fun c : ℝ ↦ c - (S.level : ℝ))
      (Icc m.1.1 m.1.2) (Ioo D.lo D.hi) := by
    intro c hc
    exact ⟨by linarith [ha.1, hc.1], by linarith [hb.2, hc.2]⟩
  have hK := (D.original_kernel_regular hF hw).1.comp
    (continuous_id.sub continuous_const).continuousOn hsub
  have hv := (completePathMatrixApply (originalSeedPairMomentum S w m)).continuous
    |>.comp_continuousOn hK
  have hd := (hφ.continuous_fderiv (by norm_num)).comp_continuousOn hpath
  have heval : Continuous (fun z :
      ((Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ] ℝ) ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ z.1 z.2) := by fun_prop
  have hc := heval.comp_continuousOn (hd.prodMk hv)
  apply ContinuousOn.intervalIntegrable
  simpa [uIcc_of_le hab, completePathMatrixApply, Function.comp_def] using hc

/-- Restricting the clock interval preserves the original path and its fixed pair momentum. -/
theorem integral_originalSeedCompletePath_testDerivative_eq_sub
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {c d : ℝ} (hac : m.1.1 ≤ c) (hcd : c ≤ d) (hdb : d ≤ m.1.2)
    {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ r in c..d, fderiv ℝ φ (originalSeedCompletePath S w x m r)
      (originalSeedKernel S w (r - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m)) =
      φ (originalSeedCompletePath S w x m d) -
        φ (originalSeedCompletePath S w x m c) := by
  have hab : m.1.1 ≤ m.1.2 := hac.trans (hcd.trans hdb)
  have hInt := (D.intervalIntegrable_originalSeedCompletePath_testDerivative
    hF hw x m ha hb hab hφ).mono_set (c := c) (d := d) (by
      rw [uIcc_of_le hcd, uIcc_of_le hab]
      exact fun r hr ↦ ⟨hac.trans hr.1, hr.2.trans hdb⟩)
  have hd : ∀ r ∈ uIcc c d,
      HasDerivAt (φ ∘ originalSeedCompletePath S w x m)
        (fderiv ℝ φ (originalSeedCompletePath S w x m r)
          (originalSeedKernel S w (r - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m)) r := by
    intro r hr
    rw [uIcc_of_le hcd] at hr
    exact (hφ.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r
      (D.hasDerivAt_originalSeedCompletePath hF hw x m ha
        ⟨by linarith [ha.1, hr.1], by linarith [hb.2, hr.2]⟩)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hInt

/-- The full original path has the exact source/target weak endpoint balance. -/
theorem integral_originalSeedCompletePath_testDerivative_eq_endpoints
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2)
    {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ c in m.1.1..m.1.2, fderiv ℝ φ (originalSeedCompletePath S w x m c)
      (originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m)) =
      φ (x + m.2) - φ x := by
  have h := D.integral_originalSeedCompletePath_testDerivative_eq_sub
    hF hw x m ha hb le_rfl hab.le le_rfl hφ
  simpa only [D.originalSeedCompletePath_target hF hw x m ha hb hab,
    originalSeedCompletePath_source] using h

/-- Every deterministic prefix, including empty and full prefixes, has its literal cut endpoint. -/
theorem integral_originalSeedCompletePath_prefix_eq_endpoints
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2)
    (t : ℝ) {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    (∫ r in m.1.1..max m.1.1 (min t m.1.2),
      fderiv ℝ φ (originalSeedCompletePath S w x m r)
        (originalSeedKernel S w (r - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m)) =
      if t ≤ m.1.1 then 0
      else if m.1.2 ≤ t then φ (x + m.2) - φ x
      else φ (originalSeedCompletePath S w x m t) - φ x := by
  have hc : m.1.1 ≤ max m.1.1 (min t m.1.2) := le_max_left _ _
  have hcb : max m.1.1 (min t m.1.2) ≤ m.1.2 :=
    max_le hab.le (min_le_right _ _)
  have h := D.integral_originalSeedCompletePath_testDerivative_eq_sub
    hF hw x m ha hb le_rfl hc hcb hφ
  rw [originalSeedCompletePath_source] at h
  rw [h]
  split_ifs with hta hbt
  · rw [max_eq_left ((min_le_left _ _).trans hta), originalSeedCompletePath_source,
      sub_self]
  · rw [min_eq_right hbt, max_eq_right hab.le,
      D.originalSeedCompletePath_target hF hw x m ha hb hab]
  · rw [min_eq_left (le_of_not_ge hbt), max_eq_right (le_of_not_ge hta)]

/-- A slab is bounded by the two cut points on the same complete original path. -/
theorem integral_originalSeedCompletePath_slab_eq_endpoints
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 ≤ m.1.2)
    {s t : ℝ} (hst : s ≤ t)
    {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ r in max m.1.1 (min s m.1.2)..max m.1.1 (min t m.1.2),
      fderiv ℝ φ (originalSeedCompletePath S w x m r)
        (originalSeedKernel S w (r - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m)) =
      φ (originalSeedCompletePath S w x m (max m.1.1 (min t m.1.2))) -
        φ (originalSeedCompletePath S w x m (max m.1.1 (min s m.1.2))) := by
  exact D.integral_originalSeedCompletePath_testDerivative_eq_sub hF hw x m ha hb
    (le_max_left _ _) (max_le_max le_rfl (min_le_min hst le_rfl))
    (max_le hab (min_le_right _ _)) hφ

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
