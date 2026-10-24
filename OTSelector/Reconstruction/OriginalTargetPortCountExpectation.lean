import OTSelector.Reconstruction.OriginalPortCountExpectation

/-! # Both original colors have vanishing-density ports after path retention -/
open Set Function Matrix Module Manifold MeasureTheory ProbabilityTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Every original pair in a genuine matching has the actual interior legal clocks,
for almost every scene and almost every atom of its unchanged pair kernel. -/
theorem ae_ae_original_pairKernel_interior_forward
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ᵐ a ∂physicalScenePairKernel scene.1,
        a.2.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
        a.2.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a.2.1.1 < a.2.1.2 := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have ha : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    have h : ∀ᵐ a ∂η.map (fun m ↦ m.1.1), a - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
      rw [Q.source_clock]
      exact D.support.source.ae_open
    exact ae_of_ae_map measurable_fst.fst.aemeasurable h
  have hb : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    have h : ∀ᵐ b ∂η.map (fun m ↦ m.1.2), b - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
      rw [Q.target_clock]
      exact D.support.target.ae_open
    exact ae_of_ae_map measurable_fst.snd.aemeasurable h
  apply Q.ae_ae_original_pairKernel_of_palm
    ((measurableSet_Ioo.preimage (measurable_fst.fst.sub_const _)).inter
      ((measurableSet_Ioo.preimage (measurable_fst.snd.sub_const _)).inter
        (measurableSet_lt measurable_fst.fst measurable_fst.snd)))
  exact ha.and (hb.and Q.ae_palm_forward)

/-- The target ports of the same retained original matching are bounded by its
own target collar and the same true-Palm full-path tail. -/
theorem lintegral_original_targetPorts_le_boundary_and_pathTail
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 3 * ell ≤ R) :
    (∫⁻ scene, physicalScenePairKernel scene.1 (originalPathTargetPorts S w R ell)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      volume (haarRootCube (Fin (finrank ℝ S.covector.ker)) R \
        haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell)) +
      volume (haarRootCube (Fin (finrank ℝ S.covector.ker)) R) *
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
          {m | ell < originalSeedPairPathLength S w m} := by
  have : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    Q.palm_probability
  let W := haarRootCube (Fin (finrank ℝ S.covector.ker)) R
  let W₀ := haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell)
  let B := {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) |
    ell < originalSeedPairPathLength S w m}
  let A₀ : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
    PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) := {a | a.1 + a.2.2 ∈ W \ W₀}
  let A₁ : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
    PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :=
      {a | a.1 + a.2.2 ∈ W ∧ a.2 ∈ B}
  have hW : MeasurableSet W := measurableSet_Icc
  have hW₀ : MeasurableSet W₀ := measurableSet_Icc
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const (measurable_originalSeedPairPathLength S hF hw)
  have hA₀ : MeasurableSet A₀ :=
    (hW.diff hW₀).preimage (measurable_fst.add measurable_snd.snd)
  have hmean₀ : (∫⁻ scene, physicalScenePairKernel scene.1 A₀
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      volume (W \ W₀) := by
    simpa only [mem_univ, and_true, measure_univ, mul_one, A₀] using
      Q.lintegral_original_markedWindow_count Prod.snd measurable_snd
        (hW.diff hW₀) MeasurableSet.univ
  have hmean₁ : (∫⁻ scene, physicalScenePairKernel scene.1 A₁
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      volume W * (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) B := by
    exact Q.lintegral_original_markedWindow_count Prod.snd measurable_snd hW hB
  calc
    _ ≤ ∫⁻ scene, (physicalScenePairKernel scene.1 A₀ + physicalScenePairKernel scene.1 A₁)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
      apply lintegral_mono_ae
      filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hscene
      apply le_trans (measure_mono_ae ?_) (measure_union_le A₀ A₁)
      filter_upwards [hscene] with a ha
      intro hport
      exact D.originalPathTargetPort_mem_boundary_or_long hF hw hell hR ha.1 ha.2.1 ha.2.2 hport
    _ = (∫⁻ scene, physicalScenePairKernel scene.1 A₀
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) +
        ∫⁻ scene, physicalScenePairKernel scene.1 A₁
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
      lintegral_add_left ((Kernel.measurable_coe physicalScenePairKernel hA₀).comp measurable_fst) _
    _ = _ := by rw [hmean₀, hmean₁]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
