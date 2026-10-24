import OTSelector.Reconstruction.OriginalStageClockSlabsActualArrays
import OTSelector.Reconstruction.OriginalStageClockSlabsWidth

/-! Actual original atom arrays have admissible true clock-stage labels. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal NNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- On a single genuine scene event, all finite endpoint arrays of every actual original
edge restriction have admissible stage labels in any grid with the same original outer
clock thresholds. No restriction or array is fixed before taking the scene event. -/
theorem ae_all_originalRestrictedEndpointArrays_clock_labels_bounded
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (G : OriginalStageClockGrid), G.cut 0 = D.lo + (S.level : ℝ) →
        G.cut G.count = D.hi + (S.level : ℝ) →
      ∀ (B : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) (n : ℕ)
        (points : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)),
      (((scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict B).fst =
        ∑ i, Measure.dirac (points i) → ∀ i, G.sourceLabel (points i).2 < G.count) ∧
      (((scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict B).snd =
        ∑ i, Measure.dirac (points i) → ∀ i, G.targetLabel (points i).2 < G.count) := by
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hs
  rw [physicalScenePairKernel_apply] at hs
  have hedge := ae_of_ae_map measurable_physicalPairAnchor.aemeasurable hs
  intro G hlo hhi B n points
  have he : ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict B,
      G.cut 0 < e.1.2 ∧ e.1.2 < G.cut G.count ∧ G.cut 0 < e.2.2 ∧ e.2.2 < G.cut G.count := by
    filter_upwards [ae_restrict_of_ae hedge] with e he
    change e.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
      e.2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ e.1.2 < e.2.2 at he
    rw [hlo, hhi]
    exact ⟨by linarith [he.1.1], by linarith [he.1.2], by linarith [he.2.1.1], by linarith [he.2.1.2]⟩
  constructor
  · intro harray
    have hlabels : ∀ᵐ p ∂((scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict B).fst,
        p.2 ∈ Ico (G.cut 0) (G.cut G.count) := by
      apply (ae_map_iff measurable_fst.aemeasurable (measurableSet_Ico.preimage measurable_snd)).mpr
      exact he.mono (fun _ h ↦ ⟨h.1.le, h.2.1⟩)
    have hall : ∀ i, (points i).2 ∈ Ico (G.cut 0) (G.cut G.count) := by
      apply originalFiniteAtoms_forall_of_ae points (P := fun p ↦ p.2 ∈ Ico (G.cut 0) (G.cut G.count))
      rwa [← harray]
    exact fun i ↦ G.sourceLabel_lt_count (hall i)
  · intro harray
    have hlabels : ∀ᵐ p ∂((scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict B).snd,
        p.2 ∈ Ioc (G.cut 0) (G.cut G.count) := by
      apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_Ioc.preimage measurable_snd)).mpr
      exact he.mono (fun _ h ↦ ⟨h.2.2.1, h.2.2.2.le⟩)
    have hall : ∀ i, (points i).2 ∈ Ioc (G.cut 0) (G.cut G.count) := by
      apply originalFiniteAtoms_forall_of_ae points (P := fun p ↦ p.2 ∈ Ioc (G.cut 0) (G.cut G.count))
      rwa [← harray]
    exact fun i ↦ G.targetLabel_lt_count (hall i)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
