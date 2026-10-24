import OTSelector.Reconstruction.OriginalStageClockSlabsLabels
import OTSelector.Reconstruction.OriginalStageClockSlabsConditional
import OTSelector.Reconstruction.OriginalMarkedWindowCounts

/-! The same actual clock supports enforce finite-label monochromaticity. -/
open Set Function Filter MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- Original separated support points cannot enter one short true analytic stage, under
the distinct source Ico / target Ioc conventions. -/
theorem OriginalStageClockGrid.not_same_stage_of_support
    (G : OriginalStageClockGrid) {μ ν : Measure ℝ} {δ D : ℝ}
    (hsep : ConditionalClockSupportBounds μ ν δ D)
    (hwidth : ∀ i : Fin G.count, G.cut (i + 1) - G.cut i < δ)
    {a b : ℝ} (ha : a ∈ μ.support) (hb : b ∈ ν.support) (i : Fin G.count)
    (hca : G.sourceLabel a = i.val) (hcb : G.targetLabel b = i.val) : False := by
  have hsa := (G.sourceLabel_eq_iff a i).mp hca
  have htb := (G.targetLabel_eq_iff b i).mp hcb
  have hg := hsep.separated a ha b hb
  rw [Real.dist_eq] at hg
  have hab : |a - b| ≤ G.cut (i + 1) - G.cut i :=
    abs_le.mpr ⟨by linarith [hsa.1, htb.2], by linarith [hsa.2.le, htb.1.le]⟩
  linarith [hwidth i]

/-- Arbitrary same-original finite endpoint arrays in the actual supports have internally
single-colour stage labels. No nonzero-class, population-count or Hall premise is used. -/
theorem OriginalStageClockGrid.originalAtomLabels_monochrome
    (G : OriginalStageClockGrid) {μ ν : Measure ℝ} {δ D : ℝ}
    (hsep : ConditionalClockSupportBounds μ ν δ D)
    (hwidth : ∀ i : Fin G.count, G.cut (i + 1) - G.cut i < δ)
    {I J : Type*} (source : I → ℝ) (target : J → ℝ)
    (hs : ∀ i, source i ∈ μ.support) (ht : ∀ j, target j ∈ ν.support) :
    ∀ k < G.count,
      (∀ i, G.sourceLabel (source i) ≠ k) ∨ (∀ j, G.targetLabel (target j) ≠ k) := by
  intro k hk
  by_cases he : ∃ i, G.sourceLabel (source i) = k
  · obtain ⟨i, hi⟩ := he
    right
    intro j hj
    exact G.not_same_stage_of_support hsep hwidth (hs i) (ht j) ⟨k, hk⟩ hi hj
  · left
    intro i hi
    exact he ⟨i, hi⟩

/-- The actual stationary original matching transfers both true Palm clock supports to
almost every original edge of almost every same original scene. -/
theorem LegalWeightedStationaryPoissonMatching.ae_ae_originalEdges_clock_support
    {q : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)),
        e.1.2 ∈ μ.support ∧ e.2.2 ∈ ν.support := by
  have ha : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m.1.1 ∈ μ.support :=
    ae_of_ae_map measurable_fst.fst.aemeasurable (by rw [Q.source_clock]; exact μ.support_mem_ae)
  have hb : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m.1.2 ∈ ν.support :=
    ae_of_ae_map measurable_fst.snd.aemeasurable (by rw [Q.target_clock]; exact ν.support_mem_ae)
  have hB : MeasurableSet {m : PhysicalPairPalmMark (Fin q) |
      m.1.1 ∈ μ.support ∧ m.1.2 ∈ ν.support} :=
    (μ.isClosed_support.measurableSet.preimage measurable_fst.fst).inter
      (ν.isClosed_support.measurableSet.preimage measurable_fst.snd)
  filter_upwards [Q.ae_ae_original_pairKernel_of_palm hB (ha.and hb)] with scene hs
  rw [physicalScenePairKernel_apply] at hs
  exact ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hs

end OTSelector.Reconstruction
