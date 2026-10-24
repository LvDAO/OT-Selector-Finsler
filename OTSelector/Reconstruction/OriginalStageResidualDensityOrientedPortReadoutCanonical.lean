import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedPortDecomposition
import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutEndpoints
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedCurrentDivergence

/-! Actual same-frame ports equal omitted raw endpoints plus the same full-input reflection. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
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

/-- Actual original port class densities are their literal omitted raw endpoint smoothing
plus the same full-input physical reflection response. Both original half-open clock
conventions, the chosen orientation and unchanged original endpoints are retained. -/
theorem ae_all_originalOrientedStagePortDensities_eq_omittedRaw_add_reflectedInput
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R)
    (hRone : 1 ≤ R) (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      let A := originalOrientedPathLengthRetained S w b R ell
      let K := originalCenteredPhysicalCubeRegion b (2 * R)
      ∀ z ∈ K,
      originalOrientedStageReflectedClassDensity b R (Ico s t)
        (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst z =
        originalOrientedOmittedRawSlabSourceDensity S w b R ell s t z scene +
          originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier _) (2 * R) (Ico s t)
            (legalInputColorMeasure _ scene.2 0) z ∧
      originalOrientedStageReflectedClassDensity b R (Ioc s t)
        (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd z =
        originalOrientedOmittedRawSlabTargetDensity S w b R ell s t z scene +
          originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier _) (2 * R) (Ioc s t)
            (legalInputColorMeasure _ scene.2 1) z := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  have hA := measurableSet_originalOrientedPathLengthRetained S hF hw b R ell
  have hAe := hA.preimage measurable_physicalPairAnchor
  have hCS : MeasurableSet {p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) | p.2 ∈ Ico s t} :=
    measurableSet_Ico.preimage measurable_snd
  have hCT : MeasurableSet {p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) | p.2 ∈ Ioc s t} :=
    measurableSet_Ioc.preimage measurable_snd
  filter_upwards [Q.full_matching,
    D.ae_originalOriented_windows_eq_retained_add_ports hF hw Q b (by linarith) hR,
    D.ae_originalOrientedStagePlans_finite hF hw Q b (by linarith) hR,
    D.ae_all_originalOrientedRetainedEndpoints_reflectedSmoothing_eq_raw hF hw Q b hell hR,
    Q.ae_originalStageWindowColors_finite (isCompact_originalStagePhysicalCube b (2 * R + 2))]
    with scene hfull hwindow hfinite hret houter
  dsimp only
  intro z hz
  let A := originalOrientedPathLengthRetained S w b R ell
  let K := originalCenteredPhysicalCubeRegion b (2 * R)
  let π : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := scene.1.1
  let ρ : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := originalStageRestrictedPathPlan A scene
  let τ := π.restrict (physicalPairAnchor ⁻¹' Aᶜ)
  let πs : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := originalStageWindowSourcePortPlan A K scene
  let πt : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := originalStageWindowTargetPortPlan A K scene
  let : IsFiniteMeasure ρ := hfinite.1
  let : IsFiniteMeasure πs := hfinite.2.1
  let : IsFiniteMeasure πt := hfinite.2.2
  let : IsFiniteMeasure ρ.fst := by change IsFiniteMeasure (ρ.map Prod.fst); infer_instance
  let : IsFiniteMeasure ρ.snd := by change IsFiniteMeasure (ρ.map Prod.snd); infer_instance
  let : IsFiniteMeasure πs.fst := by change IsFiniteMeasure (πs.map Prod.fst); infer_instance
  let : IsFiniteMeasure πt.snd := by change IsFiniteMeasure (πt.map Prod.snd); infer_instance
  have hdec : ρ + τ = π := by exact Measure.restrict_add_restrict_compl hAe
  have hdecS : ρ.fst + τ.fst = legalInputColorMeasure _ scene.2 0 := by
    rw [← Measure.fst_add, hdec]
    exact hfull.source_marginal
  have hdecT : ρ.snd + τ.snd = legalInputColorMeasure _ scene.2 1 := by
    rw [← Measure.snd_add, hdec]
    exact hfull.target_marginal
  have hmap : Measurable (fun p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) ↦ (z, p.1)) :=
    measurable_const.prodMk measurable_fst
  have hK : Measurable (fun p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) ↦ originalCanonicalOrientedReflectedKernel b R z p.1) := by
    simpa only [Function.comp_def] using (measurable_originalCanonicalOrientedReflectedKernel b R).comp hmap
  have hraw : Measurable (fun p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) ↦ originalEuclideanMollifier _ (z - p.1)) :=
    (contDiff_originalEuclideanMollifier _).continuous.measurable.comp (measurable_const.sub measurable_fst)
  have hrS : (∫ p in {p | p.2 ∈ Ico s t}, originalCanonicalOrientedReflectedKernel b R z p.1 ∂ρ.fst) =
      ∫ p in {p | p.2 ∈ Ico s t}, originalEuclideanMollifier _ (z - p.1) ∂ρ.fst := by
    change (∫ p in {p | p.2 ∈ Ico s t}, originalCanonicalOrientedReflectedKernel b R z p.1 ∂ρ.map Prod.fst) =
      ∫ p in {p | p.2 ∈ Ico s t}, originalEuclideanMollifier _ (z - p.1) ∂ρ.map Prod.fst
    rw [setIntegral_map hCS hK.aestronglyMeasurable measurable_fst.aemeasurable,
      setIntegral_map hCS hraw.aestronglyMeasurable measurable_fst.aemeasurable]
    exact (hret {e | e.1.2 ∈ Ico s t} z hz).1
  have hrT : (∫ p in {p | p.2 ∈ Ioc s t}, originalCanonicalOrientedReflectedKernel b R z p.1 ∂ρ.snd) =
      ∫ p in {p | p.2 ∈ Ioc s t}, originalEuclideanMollifier _ (z - p.1) ∂ρ.snd := by
    change (∫ p in {p | p.2 ∈ Ioc s t}, originalCanonicalOrientedReflectedKernel b R z p.1 ∂ρ.map Prod.snd) =
      ∫ p in {p | p.2 ∈ Ioc s t}, originalEuclideanMollifier _ (z - p.1) ∂ρ.map Prod.snd
    rw [setIntegral_map hCT hK.aestronglyMeasurable measurable_snd.aemeasurable,
      setIntegral_map hCT hraw.aestronglyMeasurable measurable_snd.aemeasurable]
    exact (hret {e | e.2.2 ∈ Ioc s t} z hz).2
  have hneg (v : Fin (finrank ℝ S.covector.ker) → ℝ) : originalEuclideanMollifier _ (z - v) = originalEuclideanMollifier _ (v - z) :=
    coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial _) _ _ (fun i ↦ abs_sub_comm (z i) (v i))
  have hshift : Measurable (fun x : Fin (finrank ℝ S.covector.ker) → ℝ ↦ originalEuclideanMollifier _ (x - z)) :=
    (contDiff_originalEuclideanMollifier _).continuous.measurable.comp (measurable_id.sub_const z)
  have hrawS : (∫ p in {p | p.2 ∈ Ico s t}, originalEuclideanMollifier _ (z - p.1) ∂τ.fst) =
      originalOrientedOmittedRawSlabSourceDensity S w b R ell s t z scene := by
    rw [originalOrientedOmittedRawSlabSourceDensity, originalRestrictedSceneSlabSourceMeasure_eq_edgeSource hA.compl s t scene]
    change (∫ p in {p | p.2 ∈ Ico s t}, originalEuclideanMollifier _ (z - p.1) ∂τ.fst) =
      ∫ x, originalEuclideanMollifier _ (x - z) ∂(τ.fst.restrict {p | p.2 ∈ Ico s t}).map Prod.fst
    rw [integral_map measurable_fst.aemeasurable hshift.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall (fun p ↦ hneg p.1))
  have hrawT : (∫ p in {p | p.2 ∈ Ioc s t}, originalEuclideanMollifier _ (z - p.1) ∂τ.snd) =
      originalOrientedOmittedRawSlabTargetDensity S w b R ell s t z scene := by
    rw [originalOrientedOmittedRawSlabTargetDensity, originalRestrictedSceneSlabTargetMeasure_eq_edgeTarget hA.compl s t scene]
    change (∫ p in {p | p.2 ∈ Ioc s t}, originalEuclideanMollifier _ (z - p.1) ∂τ.snd) =
      ∫ x, originalEuclideanMollifier _ (x - z) ∂(τ.snd.restrict {p | p.2 ∈ Ioc s t}).map Prod.fst
    rw [integral_map measurable_fst.aemeasurable hshift.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall (fun p ↦ hneg p.1))
  have houter' (c : Fin 2) : legalInputColorMeasure _ scene.2 c
      (originalCenteredPhysicalCubeRegion b (2 * R + 2) ×ˢ (univ : Set ℝ)) < (∞ : ℝ≥0∞) := by
    simpa only [show originalCenteredPhysicalCubeRegion b (2 * R + 2) ×ˢ (univ : Set ℝ) =
      {p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) | p.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R + 2)} by ext p; simp] using houter c
  have hS := originalOrientedPortClassDensity_eq_omittedRaw_add_response b hRone measurableSet_Ico _ ρ.fst τ.fst πs.fst
    (houter' 0) hdecS hwindow.1.symm hz hrS
  have hT := originalOrientedPortClassDensity_eq_omittedRaw_add_response b hRone measurableSet_Ioc _ ρ.snd τ.snd πt.snd
    (houter' 1) hdecT hwindow.2.symm hz hrT
  rw [hrawS] at hS
  rw [hrawT] at hT
  exact ⟨hS, hT⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
