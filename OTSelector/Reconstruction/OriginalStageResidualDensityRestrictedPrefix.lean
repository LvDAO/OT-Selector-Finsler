import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedData
import OTSelector.Reconstruction.OriginalFullCutOccupation

/-! A shared exact active-cut count for every actual finite original edge restriction. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Literal strict-source minus closed-target prefixes of a finite forward original anchor
measure count exactly its strictly active crossings. This does not use a stage oracle. -/
theorem originalFiniteForwardAnchor_prefix_eq_crossing {q : ℕ}
    (σ : Measure ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) [IsFiniteMeasure σ]
    (hforward : ∀ᵐ a ∂σ, a.2.1.1 < a.2.1.2) (c : ℝ) :
    σ.real {a | a.2.1.1 < c} - σ.real {a | a.2.1.2 ≤ c} =
      σ.real {a | a.2.1.1 < c ∧ c < a.2.1.2} := by
  let A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) := {a | a.2.1.1 < c}
  let B : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) := {a | a.2.1.2 ≤ c}
  have hA : MeasurableSet A := measurableSet_lt measurable_snd.fst.fst measurable_const
  have hB : MeasurableSet B := measurableSet_le measurable_snd.fst.snd measurable_const
  have htarget : σ B = σ (A ∩ B) := by
    apply measure_congr
    filter_upwards [hforward] with a ha
    exact propext ⟨fun hb ↦ ⟨ha.trans_le hb, hb⟩, fun hab ↦ hab.2⟩
  have hdiff := measureReal_sdiff (μ := σ) (show A ∩ B ⊆ A from inter_subset_left) (hA.inter hB)
  have heq : A \ (A ∩ B) = {a | a.2.1.1 < c ∧ c < a.2.1.2} := by
    ext a
    simp only [A, B, Set.mem_sdiff, Set.mem_inter_iff, mem_ofPred_eq, not_and, not_le]
    tauto
  change σ.real A - σ.real B = _
  have htargetreal : σ.real B = σ.real (A ∩ B) := congrArg ENNReal.toReal htarget
  rw [htargetreal]
  rw [heq] at hdiff
  exact hdiff.symm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Actual finite edge restriction endpoint prefixes equal its literal active-cut mass,
for every actual path-anchor set. The original complete paths and endpoint marks are kept. -/
theorem originalStageRestrictedEndpointPrefix_eq_cutMass
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker}
    (hw : w ∈ S.labels)
    {A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))}
    (hA : MeasurableSet A) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    [IsFiniteMeasure (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))]
    (hforward : ∀ᵐ a ∂physicalScenePairKernel scene.1, a.2.1.1 < a.2.1.2) (c : ℝ) :
    (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst.real {p | p.2 < c} -
      (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd.real {p | p.2 ≤ c} =
      (originalRestrictedSceneActiveCutMeasure S w A c scene).real univ := by
  let π : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := originalStageRestrictedPathPlan A scene
  let σ := (physicalScenePairKernel scene.1).restrict A
  have hanchor : σ = π.map physicalPairAnchor := by
    dsimp only [σ, π]
    rw [physicalScenePairKernel_apply, Measure.restrict_map measurable_physicalPairAnchor hA]
    rfl
  let : IsFiniteMeasure σ := by rw [hanchor]; infer_instance
  have hs : π.fst {p | p.2 < c} = σ {a | a.2.1.1 < c} := by
    change (π.map Prod.fst) {p | p.2 < c} = _
    rw [Measure.map_apply measurable_fst (measurableSet_lt measurable_snd measurable_const),
      hanchor, Measure.map_apply measurable_physicalPairAnchor
        (measurableSet_lt measurable_snd.fst.fst measurable_const)]
    rfl
  have ht : π.snd {p | p.2 ≤ c} = σ {a | a.2.1.2 ≤ c} := by
    change (π.map Prod.snd) {p | p.2 ≤ c} = _
    rw [Measure.map_apply measurable_snd (measurableSet_le measurable_snd measurable_const),
      hanchor, Measure.map_apply measurable_physicalPairAnchor
        (measurableSet_le measurable_snd.fst.snd measurable_const)]
    rfl
  have hpos : Measurable (fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      a.1 + originalSeedPathOffset S w c a.2) :=
    measurable_fst.add ((measurable_originalSeedPathOffset S hF hw c).comp measurable_snd)
  have hc : (originalRestrictedSceneActiveCutMeasure S w A c scene).real univ =
      σ.real {a | a.2.1.1 < c ∧ c < a.2.1.2} := by
    unfold originalRestrictedSceneActiveCutMeasure originalRestrictedSceneMarkedPositionMeasure
    rw [measureReal_def, Measure.map_apply hpos MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
    rfl
  change (π.fst {p | p.2 < c}).toReal - (π.snd {p | p.2 ≤ c}).toReal = _
  rw [hs, ht, hc]
  exact originalFiniteForwardAnchor_prefix_eq_crossing σ (ae_restrict_of_ae hforward) c

end OTSelector.Reconstruction
