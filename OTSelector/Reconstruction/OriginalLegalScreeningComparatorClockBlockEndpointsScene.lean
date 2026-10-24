import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsFlow
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabOriginalPlan
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedOmittedCut

/-! True tight block clocks have no original, retained or omitted cut occupation. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- One original-scene event covers all actual tight grid cuts. The actual Palm clock
coupling, strict-flow zero crossing and Campbell transfer are constructed internally. -/
theorem LegalWeightedStationaryPoissonMatching.ae_ae_originalPairKernel_not_cross_tight_clockSlabCuts
    {q : ℕ} {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (G : OriginalStageClockGrid) {δ D : ℝ} (hδ : 0 < δ)
    (hsep : ConditionalClockSupportBounds μ ν δ D)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i)
    (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ k : Fin (G.count+1), G.clockSlabSurplus μ ν k.val = 0 →
        ∀ᵐ a ∂physicalScenePairKernel scene.1,
          ¬ (a.2.1.1 < G.cut k.val ∧ G.cut k.val < a.2.1.2) := by
  let η := legalMarkedJointPalm q Q.law
  let π := η.map Prod.fst
  have : IsProbabilityMeasure η := Q.palm_probability
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hπ : Vlasov.IsCoupling π μ ν := by
    constructor
    · simpa only [π,η,Measure.map_map measurable_fst measurable_fst,Function.comp_def]
        using Q.source_clock
    · simpa only [π,η,Measure.map_map measurable_snd measurable_fst,Function.comp_def]
        using Q.target_clock
  have hweak : ∀ᵐ p ∂π, p.1 ≤ p.2 :=
    (ae_map_iff measurable_fst.aemeasurable (measurableSet_le measurable_fst measurable_snd)).mpr
      (Q.ae_palm_forward.mono fun _ hp ↦ hp.le)
  apply ae_all_iff.mpr
  intro k
  by_cases hk : G.clockSlabSurplus μ ν k.val = 0
  · have hclock := G.ae_not_cross_tight_clockSlabCut hδ hsep π hπ hs ht hmono hweak
      k.val (Nat.le_of_lt_succ k.isLt) hk
    have hpalm : ∀ᵐ m ∂η, ¬ (m.1.1 < G.cut k.val ∧ G.cut k.val < m.1.2) :=
      ae_of_ae_map measurable_fst.aemeasurable hclock
    have hB : MeasurableSet {m : PhysicalPairPalmMark (Fin q) |
        ¬ (m.1.1 < G.cut k.val ∧ G.cut k.val < m.1.2)} :=
      ((measurableSet_lt measurable_fst.fst measurable_const).inter
        (measurableSet_lt measurable_const measurable_fst.snd)).compl
    exact (Q.ae_ae_original_pairKernel_of_palm hB hpalm).mono (fun _ h _ ↦ h)
  · exact ae_of_all _ (fun _ h ↦ (hk h).elim)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}

omit [BorelSpace E] in
/-- Absence of true pair crossing kills every actual positive cut restriction,
without any new retained or omitted plan assumption. -/
theorem originalActiveCuts_zero_of_pairKernel_not_cross
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) (c : ℝ)
    (h : ∀ᵐ a ∂physicalScenePairKernel scene.1, ¬ (a.2.1.1 < c ∧ c < a.2.1.2)) :
    originalSceneActiveCutMeasure S w c scene = 0 ∧
      ∀ A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
          PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))),
        originalRestrictedSceneActiveCutMeasure S w A c scene = 0 := by
  have hz : physicalScenePairKernel scene.1 {a | a.2.1.1 < c ∧ c < a.2.1.2} = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr h
  constructor
  · unfold originalSceneActiveCutMeasure originalSceneMarkedPositionMeasure
    change Measure.map _ ((physicalScenePairKernel scene.1).restrict
      {a | a.2.1.1 < c ∧ c < a.2.1.2}) = 0
    rw [Measure.restrict_eq_zero.mpr hz,Measure.map_zero]
  · intro A
    have hAz : ((physicalScenePairKernel scene.1).restrict A)
        {a | a.2.1.1 < c ∧ c < a.2.1.2} = 0 :=
      le_antisymm ((Measure.restrict_le_self _).trans_eq hz) bot_le
    unfold originalRestrictedSceneActiveCutMeasure originalRestrictedSceneMarkedPositionMeasure
    change Measure.map _ (((physicalScenePairKernel scene.1).restrict A).restrict
      {a | a.2.1.1 < c ∧ c < a.2.1.2}) = 0
    rw [Measure.restrict_eq_zero.mpr hAz,Measure.map_zero]

omit [BorelSpace E] in
/-- Every true zero Hall cut has zero full occupation and zero same-frame omitted
density for all physical orientations and retention scales on a single scene event. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_originalActiveCuts_zero_at_tight_clockSlabCuts
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) {δ D : ℝ} (hδ : 0 < δ)
    (hsep : ConditionalClockSupportBounds μ ν δ D)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i)
    (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ k : Fin (G.count+1), G.clockSlabSurplus μ ν k.val = 0 →
        originalSceneActiveCutMeasure S w (G.cut k.val) scene = 0 ∧
        (∀ A, originalRestrictedSceneActiveCutMeasure S w A (G.cut k.val) scene = 0) ∧
        ∀ (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
          (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ),
          originalOrientedOmittedSceneActiveCutMeasure S w b R ell (G.cut k.val) scene = 0 ∧
          ∀ z, originalOrientedOmittedCutDensity S w b R ell (G.cut k.val) scene z = 0 := by
  filter_upwards [Q.ae_ae_originalPairKernel_not_cross_tight_clockSlabCuts G hδ hsep hs ht hmono]
    with scene hscene
  intro k hk
  have hz := originalActiveCuts_zero_of_pairKernel_not_cross (S := S) (w := w) scene (G.cut k.val) (hscene k hk)
  refine ⟨hz.1,hz.2,?_⟩
  intro b R ell
  have hom := hz.2 (originalOrientedPathLengthRetained S w b R ell)ᶜ
  refine ⟨hom,?_⟩
  intro z
  simp only [originalOrientedOmittedCutDensity,show originalOrientedOmittedSceneActiveCutMeasure
    S w b R ell (G.cut k.val) scene = 0 from hom,integral_zero_measure]

end OTSelector.Reconstruction
