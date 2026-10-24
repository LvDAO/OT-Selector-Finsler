import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutPositiveSmoothing
import OTSelector.Reconstruction.OriginalStageResidualDensityActualPorts
import OTSelector.Reconstruction.OriginalCubeReflectedInputFubini
import OTSelector.Reconstruction.MarkedStationaryValuePalmMarginals
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedPoissonDual

/-! Literal endpoint projections of the unchanged original paired-edge measure. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Restricting actual anchored pairs and reading their source gives the same original
source marginal as restricting the unchanged original edges. -/
theorem originalRestrictedPairSourceMeasure_eq_edgeSource {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    (scene : LegalMarkedOptimalInputScene q) :
    ((physicalScenePairKernel scene.1).restrict A).map physicalPairSourcePoint =
      ((scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
        (physicalPairAnchor ⁻¹' A)).fst := by
  rw [physicalScenePairKernel_apply, Measure.restrict_map measurable_physicalPairAnchor hA,
    Measure.map_map measurable_physicalPairSourcePoint measurable_physicalPairAnchor]
  rfl

/-- The target projection reconstructs the full true displacement before reading the
original target clock; it is exactly the unchanged edge target marginal. -/
theorem originalRestrictedPairTargetMeasure_eq_edgeTarget {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    (scene : LegalMarkedOptimalInputScene q) :
    ((physicalScenePairKernel scene.1).restrict A).map physicalPairTargetPoint =
      ((scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
        (physicalPairAnchor ⁻¹' A)).snd := by
  rw [physicalScenePairKernel_apply, Measure.restrict_map measurable_physicalPairAnchor hA,
    Measure.map_map measurable_physicalPairTargetPoint measurable_physicalPairAnchor]
  congr 1
  funext e
  change (e.1.1 + (e.2.1 - e.1.1), e.2.2) = e.2
  congr 1
  abel

/-- A true source-clock slab and its actual spatial endpoint are obtained by class
restriction of the original marked source marginal. -/
theorem originalRestrictedSceneSlabSourceMeasure_eq_edgeSource {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    (s t : ℝ) (scene : LegalMarkedOptimalInputScene q) :
    originalRestrictedSceneSlabSourceMeasure A s t scene =
      ((((scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
        (physicalPairAnchor ⁻¹' A)).fst).restrict {p | p.2 ∈ Ico s t}).map Prod.fst := by
  have hC : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ Ico s t} :=
    measurableSet_Ico.preimage measurable_snd
  rw [← originalRestrictedPairSourceMeasure_eq_edgeSource hA scene,
    Measure.restrict_map measurable_physicalPairSourcePoint hC,
    Measure.map_map measurable_fst measurable_physicalPairSourcePoint]
  simp only [originalRestrictedSceneSlabSourceMeasure,
    originalRestrictedSceneMarkedPositionMeasure, physicalPairSourcePoint,
    Function.comp_def, add_zero, Set.preimage_ofPred_eq, Set.mem_ofPred_eq, Set.mem_Ico]

/-- The target slab keeps the original `(s,t]` convention under the true target projection. -/
theorem originalRestrictedSceneSlabTargetMeasure_eq_edgeTarget {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    (s t : ℝ) (scene : LegalMarkedOptimalInputScene q) :
    originalRestrictedSceneSlabTargetMeasure A s t scene =
      ((((scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
        (physicalPairAnchor ⁻¹' A)).snd).restrict {p | p.2 ∈ Ioc s t}).map Prod.fst := by
  have hC : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ Ioc s t} :=
    measurableSet_Ioc.preimage measurable_snd
  rw [← originalRestrictedPairTargetMeasure_eq_edgeTarget hA scene,
    Measure.restrict_map measurable_physicalPairTargetPoint hC,
    Measure.map_map measurable_fst measurable_physicalPairTargetPoint]
  rfl

private theorem integrable_of_finite_spatial_window {q : ℕ}
    {σ : Measure (LegalMarkedPhysicalPoint q)} {W : Set (Fin q → ℝ)}
    (hW : MeasurableSet W) (hσ : σ {p | p.1 ∈ W} < (∞ : ℝ≥0∞))
    {f : LegalMarkedPhysicalPoint q → ℝ} (hf : Measurable f)
    (B : ℝ) (hB : ∀ p, ‖f p‖ ≤ B) (hzero : ∀ p, p.1 ∉ W → f p = 0) :
    Integrable f σ := by
  have hWin : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ W} :=
    hW.preimage measurable_fst
  let : IsFiniteMeasure (σ.restrict {p | p.1 ∈ W}) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hσ⟩
  have hi : Integrable f (σ.restrict {p | p.1 ∈ W}) :=
    Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hB)
  have h := (integrable_indicator_iff hWin).mpr hi
  apply h.congr
  apply Eventually.of_forall
  intro p
  by_cases hp : p ∈ {p : LegalMarkedPhysicalPoint q | p.1 ∈ W}
  · exact Set.indicator_of_mem hp f
  · rw [Set.indicator_of_notMem hp, hzero p hp]

private theorem port_reflection_integral_decomposition {X : Type*} [MeasurableSpace X]
    {μ ρ τ π : Measure X} {W : Set X} (hW : MeasurableSet W)
    (hfull : ρ + τ = μ) (hwindow : ρ + π = μ.restrict W)
    {f g : X → ℝ} (hf : Integrable f (μ.restrict W)) (hg : Integrable g μ)
    (hret : ∫ p, f p ∂ρ = ∫ p, g p ∂ρ) :
    (∫ p, f p ∂π) = (∫ p, g p ∂τ) +
      ∫ p, (W.indicator f p - g p) ∂μ := by
  have hρf : Integrable f ρ := hf.mono_measure (by rw [← hwindow]; exact Measure.le_add_right le_rfl)
  have hπf : Integrable f π := hf.mono_measure (by rw [← hwindow]; exact Measure.le_add_left le_rfl)
  have hρg : Integrable g ρ := hg.mono_measure (by rw [← hfull]; exact Measure.le_add_right le_rfl)
  have hτg : Integrable g τ := hg.mono_measure (by rw [← hfull]; exact Measure.le_add_left le_rfl)
  rw [integral_sub ((integrable_indicator_iff hW).mpr hf) hg, integral_indicator hW,
    ← hwindow, integral_add_measure hρf hπf, ← hfull, integral_add_measure hρg hτg]
  linarith

private theorem reflected_class_port_eq_raw_add_response {q : ℕ}
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) {M R : ℝ}
    (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (hR : 1 ≤ R)
    {C : Set ℝ} (hC : MeasurableSet C)
    {μ ρ τ π : Measure (LegalMarkedPhysicalPoint q)}
    (hfinite : μ {p | p.1 ∈ haarRootCube (Fin q) (R+1)} < (∞ : ℝ≥0∞))
    (hfull : ρ + τ = μ)
    (hwindow : ρ + π = μ.restrict {p | p.1 ∈ haarRootCube (Fin q) R})
    {z : Fin q → ℝ} (hz : z ∈ haarRootCube (Fin q) R)
    (hret : (∫ p in {p | p.2 ∈ C}, originalCubeReflectedKernel η R z p.1 ∂ρ) =
      ∫ p in {p | p.2 ∈ C}, η (z-p.1) ∂ρ) :
    originalStageReflectedClassDensity η R C π z =
      (∫ p in {p | p.2 ∈ C}, η (z-p.1) ∂τ) +
        originalClassReflectedInputScalarField η R C μ z := by
  let W : Set (LegalMarkedPhysicalPoint q) := {p | p.1 ∈ haarRootCube (Fin q) R}
  let B : Set (LegalMarkedPhysicalPoint q) := {p | p.2 ∈ C}
  let f := B.indicator (fun p ↦ originalCubeReflectedKernel η R z p.1)
  let g := B.indicator (fun p ↦ η (z-p.1))
  have hW : MeasurableSet W := measurableSet_Icc.preimage measurable_fst
  have hB : MeasurableSet B := hC.preimage measurable_snd
  have hf : Measurable f :=
    ((measurable_originalCubeReflectedKernel hη R).comp (measurable_const.prodMk measurable_fst)).indicator hB
  have hg : Measurable g := (hη.comp (measurable_const.sub measurable_fst)).indicator hB
  have hfg : Measurable (W.indicator f) := hf.indicator hW
  have hfI : Integrable f (μ.restrict W) := by
    apply (integrable_indicator_iff hW).mp
    apply integrable_of_finite_spatial_window measurableSet_Icc hfinite hfg
      ((3:ℝ)^q*M)
    · intro p
      by_cases hp : p ∈ W
      · rw [indicator_of_mem hp]
        by_cases hc : p ∈ B
        · rw [show f p = originalCubeReflectedKernel η R z p.1 from indicator_of_mem hc _]
          simpa only [Real.norm_eq_abs, Fintype.card_fin] using abs_originalCubeReflectedKernel_le hηM R z p.1
        · rw [show f p = 0 from indicator_of_notMem hc _, norm_zero]
          positivity
      · rw [indicator_of_notMem hp, norm_zero]
        positivity
    · intro p hp
      have hn : p ∉ W := by
        intro hw
        apply hp
        exact ⟨fun i ↦ by linarith [hw.1 i], fun i ↦ by linarith [hw.2 i]⟩
      exact indicator_of_notMem hn _
  have hgI : Integrable g μ := by
    apply integrable_of_finite_spatial_window measurableSet_Icc hfinite hg M
    · intro p
      by_cases hc : p ∈ B
      · rw [show g p = η (z-p.1) from indicator_of_mem hc _]
        exact hηM _
      · rw [show g p = 0 from indicator_of_notMem hc _, norm_zero]
        exact hM
    · intro p hp
      by_cases hc : p ∈ B
      · rw [show g p = η (z-p.1) from indicator_of_mem hc _]
        apply hηsupport
        by_contra! hn
        apply hp
        apply (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R+1) p.1).mpr
        have hzn := (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R) z).mp hz
        calc
          ‖p.1‖ = ‖z-(z-p.1)‖ := by congr 1; abel
          _ ≤ ‖z‖ + ‖z-p.1‖ := norm_sub_le _ _
          _ ≤ R+1 := by linarith
      · exact indicator_of_notMem hc _
  have hret' : ∫ p, f p ∂ρ = ∫ p, g p ∂ρ := by
    simpa only [f, g, integral_indicator hB] using hret
  have h := port_reflection_integral_decomposition hW hfull hwindow hfI hgI hret'
  have hresp : (fun p ↦ W.indicator f p - g p) =
      fun p ↦ C.indicator (fun _ ↦ (1:ℝ)) p.2 * originalCubeReflectedInputResponse η R z p.1 := by
    funext p
    by_cases hc : p.2 ∈ C <;> by_cases hw : p.1 ∈ haarRootCube (Fin q) R <;>
      simp [W, B, f, g, originalCubeReflectedInputResponse, hc, hw]
  rw [hresp] at h
  simpa only [f, g, integral_indicator hB, originalStageReflectedClassDensity,
    originalClassReflectedInputScalarField] using h

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- On one original-scene event the actual reflected source and target port densities
are their omitted raw endpoint densities plus the unchanged full-input reflected responses.
The source uses `[s,t)` and the target `(s,t]` throughout. -/
theorem ae_all_originalStagePortDensities_eq_omittedRaw_add_reflectedInput
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*ell ≤ R) (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        Measurable η → ∀ B : ℝ, 0 ≤ B → (∀ v, |η v| ≤ B) →
        (∀ v, 1 ≤ ‖v‖ → η v = 0) → (∀ v, η (-v) = η v) →
      ∀ z ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R,
        originalStageSourcePortDensity S w R ell η (Ico s t) scene z =
          originalOmittedRawSlabSourceDensity S w R ell s t η z scene +
          originalClassReflectedInputScalarField η R (Ico s t)
            (legalInputColorMeasure _ scene.2 0) z ∧
        originalStageTargetPortDensity S w R ell η (Ioc s t) scene z =
          originalOmittedRawSlabTargetDensity S w R ell s t η z scene +
          originalClassReflectedInputScalarField η R (Ioc s t)
            (legalInputColorMeasure _ scene.2 1) z := by
  have : IsProbabilityMeasure μ := D.support.source.probability
  have : IsProbabilityMeasure ν := D.support.target.probability
  have hA := measurableSet_originalPathLengthRetained S hF hw R ell
  have hAe := hA.preimage measurable_physicalPairAnchor
  have hCS : MeasurableSet {p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) | p.2 ∈ Ico s t} :=
    measurableSet_Ico.preimage measurable_snd
  have hCT : MeasurableSet {p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) | p.2 ∈ Ioc s t} :=
    measurableSet_Ioc.preimage measurable_snd
  filter_upwards [Q.full_matching,
    D.ae_original_windows_eq_retained_add_ports hF hw Q (by linarith) hR,
    D.ae_all_originalRetainedEndpoints_reflectedSmoothing_eq_raw hF hw Q hell hR,
    Q.ae_finite_reflectedInputOuterWindow R 0,
    Q.ae_finite_reflectedInputOuterWindow R 1]
      with scene hfull hwindow hret hfinS hfinT
  intro η hη B hB hηB hsupport heven z hz
  let π : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) := scene.1.1
  let ρ : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
    originalPathRetainedPlan S w R ell scene
  let τ := π.restrict (physicalPairAnchor ⁻¹' (originalPathLengthRetained S w R ell)ᶜ)
  have hdec : ρ + τ = π := by
    change π.restrict (physicalPairAnchor ⁻¹' originalPathLengthRetained S w R ell) +
      π.restrict (physicalPairAnchor ⁻¹' (originalPathLengthRetained S w R ell)ᶜ) = π
    exact Measure.restrict_add_restrict_compl hAe
  have hdecS : ρ.fst + τ.fst = legalInputColorMeasure _ scene.2 0 := by
    rw [← Measure.fst_add, hdec]
    exact hfull.source_marginal
  have hdecT : ρ.snd + τ.snd = legalInputColorMeasure _ scene.2 1 := by
    rw [← Measure.snd_add, hdec]
    exact hfull.target_marginal
  have hK : Measurable (fun p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) ↦
      originalCubeReflectedKernel η R z p.1) :=
    (measurable_originalCubeReflectedKernel hη R).comp (measurable_const.prodMk measurable_fst)
  have hraw : Measurable (fun p : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker) ↦ η (z-p.1)) :=
    hη.comp (measurable_const.sub measurable_fst)
  have hrS : (∫ p in {p | p.2 ∈ Ico s t}, originalCubeReflectedKernel η R z p.1 ∂ρ.fst) =
      ∫ p in {p | p.2 ∈ Ico s t}, η (z-p.1) ∂ρ.fst := by
    change (∫ p in {p | p.2 ∈ Ico s t}, originalCubeReflectedKernel η R z p.1 ∂ρ.map Prod.fst) =
      ∫ p in {p | p.2 ∈ Ico s t}, η (z-p.1) ∂ρ.map Prod.fst
    rw [setIntegral_map hCS hK.aestronglyMeasurable measurable_fst.aemeasurable,
      setIntegral_map hCS hraw.aestronglyMeasurable measurable_fst.aemeasurable]
    exact (hret η hsupport {e | e.1.2 ∈ Ico s t} z hz).1
  have hrT : (∫ p in {p | p.2 ∈ Ioc s t}, originalCubeReflectedKernel η R z p.1 ∂ρ.snd) =
      ∫ p in {p | p.2 ∈ Ioc s t}, η (z-p.1) ∂ρ.snd := by
    change (∫ p in {p | p.2 ∈ Ioc s t}, originalCubeReflectedKernel η R z p.1 ∂ρ.map Prod.snd) =
      ∫ p in {p | p.2 ∈ Ioc s t}, η (z-p.1) ∂ρ.map Prod.snd
    rw [setIntegral_map hCT hK.aestronglyMeasurable measurable_snd.aemeasurable,
      setIntegral_map hCT hraw.aestronglyMeasurable measurable_snd.aemeasurable]
    exact (hret η hsupport {e | e.2.2 ∈ Ioc s t} z hz).2
  have hneg (v : Fin (finrank ℝ S.covector.ker) → ℝ) : η (z-v) = η (v-z) := by
    simpa only [neg_sub] using (heven (z-v)).symm
  have hshift : Measurable (fun x : Fin (finrank ℝ S.covector.ker) → ℝ ↦ η (x-z)) :=
    hη.comp (measurable_id.sub measurable_const)
  have hrawS : (∫ p in {p | p.2 ∈ Ico s t}, η (z-p.1) ∂τ.fst) =
      originalOmittedRawSlabSourceDensity S w R ell s t η z scene := by
    rw [originalOmittedRawSlabSourceDensity,
      originalRestrictedSceneSlabSourceMeasure_eq_edgeSource hA.compl s t scene]
    change (∫ p in {p | p.2 ∈ Ico s t}, η (z-p.1) ∂τ.fst) =
      ∫ x, η (x-z) ∂(τ.fst.restrict {p | p.2 ∈ Ico s t}).map Prod.fst
    rw [integral_map measurable_fst.aemeasurable hshift.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall (fun p ↦ hneg p.1))
  have hrawT : (∫ p in {p | p.2 ∈ Ioc s t}, η (z-p.1) ∂τ.snd) =
      originalOmittedRawSlabTargetDensity S w R ell s t η z scene := by
    rw [originalOmittedRawSlabTargetDensity,
      originalRestrictedSceneSlabTargetMeasure_eq_edgeTarget hA.compl s t scene]
    change (∫ p in {p | p.2 ∈ Ioc s t}, η (z-p.1) ∂τ.snd) =
      ∫ x, η (x-z) ∂(τ.snd.restrict {p | p.2 ∈ Ioc s t}).map Prod.fst
    rw [integral_map measurable_fst.aemeasurable hshift.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall (fun p ↦ hneg p.1))
  have hS := reflected_class_port_eq_raw_add_response hη hB hηB hsupport
    (by linarith : 1 ≤ R) measurableSet_Ico
    (lt_of_le_of_lt (measure_mono (by intro p hp; exact ⟨hp, mem_univ _⟩)) hfinS)
    hdecS hwindow.1.symm hz hrS
  have hT := reflected_class_port_eq_raw_add_response hη hB hηB hsupport
    (by linarith : 1 ≤ R) measurableSet_Ioc
    (lt_of_le_of_lt (measure_mono (by intro p hp; exact ⟨hp, mem_univ _⟩)) hfinT)
    hdecT hwindow.2.symm hz hrT
  rw [hrawS] at hS
  rw [hrawT] at hT
  exact ⟨hS, hT⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
