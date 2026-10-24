import OTSelector.Reconstruction.OriginalStageResidualDensityCanonical

/-! Actual first and last cut readouts follow from the original full-scene clock support. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Strict and closed prefixes agree at the two outer clocks when the actual clock support
is strictly interior. This retains both endpoint conventions at all proper cuts. -/
theorem originalStageClockPrefix_extremes {q : ℕ} (π : Measure (LegalMarkedPhysicalPoint q))
    {lo hi : ℝ} (hclock : ∀ᵐ p ∂π, lo < p.2 ∧ p.2 < hi) :
    π.real {p | p.2 < lo} = 0 ∧ π.real {p | p.2 ≤ lo} = 0 ∧
    π.real {p | p.2 < hi} = π.real univ ∧ π.real {p | p.2 ≤ hi} = π.real univ := by
  have hlo : π {p | p.2 < lo} = 0 := measure_eq_zero_iff_ae_notMem.mpr
    (hclock.mono (fun p hp ↦ not_lt_of_ge hp.1.le))
  have hlo' : π {p | p.2 ≤ lo} = 0 := measure_eq_zero_iff_ae_notMem.mpr
    (hclock.mono (fun p hp ↦ not_le_of_gt hp.1))
  have hhi : π {p | p.2 < hi} = π univ := measure_congr
    (hclock.mono (fun p hp ↦ propext ⟨fun _ ↦ mem_univ p, fun _ ↦ hp.2⟩))
  have hhi' : π {p | p.2 ≤ hi} = π univ := measure_congr
    (hclock.mono (fun p hp ↦ propext ⟨fun _ ↦ mem_univ p, fun _ ↦ hp.2.le⟩))
  simp only [measureReal_def, hlo, hlo', hhi, hhi', ENNReal.toReal_zero, and_self]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- At the two outer support clocks no actual original path is active. All anchors are
included, including those outside the physical cube. -/
theorem originalStageActiveCut_extremes_eq_zero
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) {lo hi : ℝ}
    (hclock : ∀ᵐ a ∂physicalScenePairKernel scene.1,
      lo < a.2.1.1 ∧ a.2.1.2 < hi) :
    originalSceneActiveCutMeasure S w lo scene = 0 ∧
    originalSceneActiveCutMeasure S w hi scene = 0 := by
  have hlo : physicalScenePairKernel scene.1 {a | a.2.1.1 < lo ∧ lo < a.2.1.2} = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (hclock.mono (fun a ha h ↦ (not_lt_of_ge ha.1.le) h.1))
  have hhi : physicalScenePairKernel scene.1 {a | a.2.1.1 < hi ∧ hi < a.2.1.2} = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (hclock.mono (fun a ha h ↦ (not_lt_of_ge ha.2.le) h.2))
  constructor
  · unfold originalSceneActiveCutMeasure originalSceneMarkedPositionMeasure
    change Measure.map _ ((physicalScenePairKernel scene.1).restrict
      {a | a.2.1.1 < lo ∧ lo < a.2.1.2}) = 0
    rw [Measure.restrict_eq_zero.mpr hlo, Measure.map_zero]
  · unfold originalSceneActiveCutMeasure originalSceneMarkedPositionMeasure
    change Measure.map _ ((physicalScenePairKernel scene.1).restrict
      {a | a.2.1.1 < hi ∧ hi < a.2.1.2}) = 0
    rw [Measure.restrict_eq_zero.mpr hhi, Measure.map_zero]

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The same original full matching produces empty first cut, empty last cut, zero first
main prefix and exactly the full colored-window count difference at the last cut. -/
theorem ae_originalStageEndpointReadouts
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) (R : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalSceneActiveCutMeasure S w (D.lo + (S.level : ℝ)) scene = 0 ∧
      originalSceneActiveCutMeasure S w (D.hi + (S.level : ℝ)) scene = 0 ∧
      originalStageMainInputPrefix R (D.lo + (S.level : ℝ)) scene = 0 ∧
      originalStageMainInputPrefix R (D.hi + (S.level : ℝ)) scene =
        (legalInputColorMeasure _ scene.2 0).real {p | p.1 ∈ haarRootCube _ R} -
        (legalInputColorMeasure _ scene.2 1).real {p | p.1 ∈ haarRootCube _ R} := by
  filter_upwards [Q.full_matching, D.ae_ae_original_pairKernel_interior_forward Q]
    with scene hfull hclock
  have hbounds : ∀ᵐ a ∂physicalScenePairKernel scene.1,
      D.lo + (S.level : ℝ) < a.2.1.1 ∧ a.2.1.2 < D.hi + (S.level : ℝ) :=
    hclock.mono (fun a ha ↦ ⟨by linarith [ha.1.1], by linarith [ha.2.1.2]⟩)
  have hcuts := originalStageActiveCut_extremes_eq_zero S w scene hbounds
  have hedge : ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))),
      D.lo + (S.level : ℝ) < e.1.2 ∧ e.1.2 < D.hi + (S.level : ℝ) ∧
      D.lo + (S.level : ℝ) < e.2.2 ∧ e.2.2 < D.hi + (S.level : ℝ) := by
    rw [physicalScenePairKernel_apply] at hclock
    have hmap := ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hclock
    filter_upwards [hmap] with e he
    change e.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
      e.2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ e.1.2 < e.2.2 at he
    exact ⟨by linarith [he.1.1], by linarith [he.1.2],
      by linarith [he.2.1.1], by linarith [he.2.1.2]⟩
  have hs : ∀ᵐ p ∂legalInputColorMeasure _ scene.2 0,
      D.lo + (S.level : ℝ) < p.2 ∧ p.2 < D.hi + (S.level : ℝ) := by
    rw [← hfull.source_marginal]
    apply (ae_map_iff measurable_fst.aemeasurable
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))).mpr
    exact hedge.mono (fun _ h ↦ ⟨h.1, h.2.1⟩)
  have ht : ∀ᵐ p ∂legalInputColorMeasure _ scene.2 1,
      D.lo + (S.level : ℝ) < p.2 ∧ p.2 < D.hi + (S.level : ℝ) := by
    rw [← hfull.target_marginal]
    apply (ae_map_iff measurable_snd.aemeasurable
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))).mpr
    exact hedge.mono (fun _ h ↦ h.2.2)
  have hsread := originalStageClockPrefix_extremes
    ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R})
    (ae_restrict_of_ae hs)
  have htread := originalStageClockPrefix_extremes
    ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R})
    (ae_restrict_of_ae ht)
  refine ⟨hcuts.1, hcuts.2, ?_, ?_⟩
  · rw [originalStageMainInputPrefix, hsread.1, htread.2.1, sub_self]
  · rw [originalStageMainInputPrefix, hsread.2.2.1, htread.2.2.2]
    simp only [measureReal_def, Measure.restrict_apply_univ]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
