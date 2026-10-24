import OTSelector.Reconstruction.OriginalRetainedFinitePlan

/-! # Every retained finite atom has its own unchanged legal interior path -/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- All occupied atoms of the actual retained finite plan have the original
strictly legal clocks, both original endpoints in the inner cube, and their
entire original compliance path in that same inner cube. -/
theorem ae_originalPathRetainedPlan_legal_inner_paths
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ e ∈ (originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      e.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
      e.2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ e.1.2 < e.2.2 ∧
      e.1.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell) ∧
      e.2.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell) ∧
      ∀ c ∈ Icc e.1.2 e.2.2,
        originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 c ∈
          haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell) := by
  have hA := (measurableSet_originalPathLengthRetained S hF hw R ell).preimage
    measurable_physicalPairAnchor
  filter_upwards [Q.full_matching, D.ae_ae_original_pairKernel_interior_forward Q]
    with scene hfull hclock
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hfull.simple_edges).1
  have hclockEdge : ∀ᵐ e ∂(scene.1.1 : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))),
      e.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
      e.2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ e.1.2 < e.2.2 := by
    rw [physicalScenePairKernel_apply] at hclock
    exact ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hclock
  have hclockAll := forall_support_of_ae_of_legalCounting _ scene.1.1 hcount hclockEdge
  have hcountRet := ((isLegalSimpleCountingMeasure_iff _ _).mp
    (hfull.simple_originalPathRetainedPlan (S := S) (w := w) R ell)).1
  have hretAll := forall_support_of_ae_of_legalCounting _
    (originalPathRetainedPlan S w R ell scene) hcountRet (ae_restrict_mem hA)
  intro e he
  have heOrig : e ∈ (scene.1.1 : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support :=
    Measure.support_mono Measure.restrict_le_self he
  obtain ⟨ha, hb, hforward⟩ := hclockAll e heOrig
  have hret := hretAll e he
  have hpath : ∀ c ∈ Icc e.1.2 e.2.2,
      originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 c ∈
        haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell) := by
    intro c hc
    exact D.originalPathLengthRetained_path_mem_innerCube hF hw hell hR hret ha hb hc
  refine ⟨ha, hb, hforward, ?_, ?_, hpath⟩
  · apply (mem_haarRootCube_iff_norm_le (by linarith) _).mpr
    have hx := (mem_haarRootCube_iff_norm_le (by linarith) e.1.1).mp hret.1
    exact hx.trans (by linarith)
  · have heq : e.1.1 + (e.2.1 - e.1.1) = e.2.1 := by abel
    simpa only [physicalPairAnchor, heq] using
      D.originalPathLengthRetained_target_mem_innerCube hF hw hell hR hret ha hb hforward

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
