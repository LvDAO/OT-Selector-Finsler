import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicLabelGeometry
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedRetainedCoreCarrierInclusion
import OTSelector.Reconstruction.FinslerQuadraticCostDifferenceCore

/-!
# One original macroscopic coefficient, independent of auxiliary core accuracy

The macro tag is read in the fixed original seed basis. Its original population
root and inverse-compliance coefficient are measurable total functions, using
the existing physical-map completion outside genuine labels. On every actual
retained core label image these are exactly the original root and coefficient.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section CompactInverse
variable {Z V : Type*} [TopologicalSpace Z] [TopologicalSpace V] [T2Space V]

/-- A left inverse on the image of an actual compact continuous map is
continuous there, without ambient continuity of the inverse. -/
theorem continuousOn_leftInverse_image_of_compact
    {K : Set Z} (hK : IsCompact K) (f : Z → V) (hf : ContinuousOn f K)
    (g : V → Z) (hgf : ∀ z ∈ K, g (f z) = z) : ContinuousOn g (f '' K) := by
  apply continuousOn_iff_isClosed.mpr
  intro L hL
  refine ⟨f '' (K ∩ L), ((hK.inter_right hL).image_of_continuousOn
    (hf.mono inter_subset_left)).isClosed, ?_⟩
  ext w
  constructor
  · rintro ⟨hwL, z, hz, rfl⟩
    refine ⟨⟨z, ⟨hz, ?_⟩, rfl⟩, z, hz, rfl⟩
    simpa only [Set.mem_preimage, hgf z hz] using hwL
  · rintro ⟨⟨z, ⟨hz, hzL⟩, rfl⟩, _⟩
    exact ⟨by simpa only [Set.mem_preimage, hgf z hz] using hzL, z, hz, rfl⟩
end CompactInverse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}

/-- The original macroscopic coordinate of an actual population root in the
fixed original seed basis; this definition contains no auxiliary core. -/
def physicalSceneOriginalMacroLabel (j : ℕ) (z : ℚ → M) :
    Fin (finrank ℝ (P j).seed.covector.ker) → ℝ :=
  (Module.finBasis ℝ (P j).seed.covector.ker).equivFun
    (populationSeedRootLabelValue (P j).seed a z)

/-- The original population root read from its actual macro tag, measurably
completed using the existing original seed physical map. -/
def physicalSceneOriginalMacroRootValue (j : ℕ)
    (w : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) : ℚ → M :=
  a (populationSeedPhysicalMap (P j).seed
    ((Module.finBasis ℝ (P j).seed.covector.ker).equivFun.symm w, (P j).seed.level))

/-- The total macro-root readout is Borel from the actual original physical map. -/
theorem measurable_physicalSceneOriginalMacroRootValue (ha : Measurable a) (j : ℕ) :
    Measurable (physicalSceneOriginalMacroRootValue (P := P) (a := a) j) := by
  exact ha.comp ((measurable_populationSeedPhysicalMap (P j).seed).comp
    ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm.continuous.measurable.prodMk
      measurable_const))

/-- The original inverse-compliance field at the original macro tag and clocks.
Both the tag map and the coefficient are independent of auxiliary core accuracy. -/
def physicalSceneOriginalMacroCoefficient (j : ℕ)
    (q : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ)) :
    Matrix (Fin (finrank ℝ (P j).seed.covector.ker))
      (Fin (finrank ℝ (P j).seed.covector.ker)) ℝ :=
  populationSeedRootCoefficient (P j).seed a
    (Module.finBasis ℝ (P j).seed.covector.ker)
    (physicalSceneOriginalMacroRootValue (P := P) (a := a) j q.1, q.2)

/-- One original coefficient cost on the fixed macro-tagged physical carrier. -/
def physicalSceneOriginalMacroCost (j : ℕ)
    (w : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)
    (x y : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) : ℝ :=
  matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j
    (w, x.2, y.2)) (y.1 - x.1)

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj in
/-- Every actual root in the fixed original seed piece is recovered from the
same macro tag, before any choice of retained core. -/
theorem physicalSceneOriginalMacroRootValue_at_label (j : ℕ) {z : ℚ → M}
    (hz : z ∈ populationSeedRootPiece P a κ lambda j) :
    physicalSceneOriginalMacroRootValue (P := P) (a := a) j
      (physicalSceneOriginalMacroLabel (P := P) (a := a) j z) = z := by
  obtain ⟨hw, hr⟩ := fixed_seed_rootLabel_recovery hF hcomplete hu ha hinj j hz
  unfold physicalSceneOriginalMacroRootValue physicalSceneOriginalMacroLabel
  rw [LinearEquiv.symm_apply_apply]
  change a (populationSeedPhysicalMap (P j).seed
    ((⟨populationSeedRootLabelValue (P j).seed a z, hw⟩ : (P j).seed.labels),
      (P j).seed.level)) = z
  rw [populationSeedPhysicalMap_at_label]
  simpa only [sub_self] using hr

include hF hcomplete hu ha hinj in
/-- The fixed original macro coefficient is Borel jointly in tag and clock pair. -/
theorem measurable_physicalSceneOriginalMacroCoefficient (j : ℕ) :
    Measurable (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  exact (measurable_populationSeedRootCoefficient (P j).seed hF hcomplete hu ha hinj
    (Module.finBasis ℝ (P j).seed.covector.ker)).comp
      (((measurable_physicalSceneOriginalMacroRootValue ha j).comp measurable_fst).prodMk
        measurable_snd)

include hF hcomplete hu ha hinj in
/-- The same fixed original cost is Borel jointly in the actual macro tag and
both physical marked endpoints, with their original separate clocks. -/
theorem measurable_physicalSceneOriginalMacroCost (j : ℕ) :
    Measurable (fun q : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) ×
      (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ×
        ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)) ↦
      physicalSceneOriginalMacroCost (P := P) (a := a) j q.1 q.2.1 q.2.2) := by
  exact continuous_matrixQuadratic.measurable.comp
    (((measurable_physicalSceneOriginalMacroCoefficient hF hcomplete hu ha hinj j).comp
      (measurable_fst.prodMk (measurable_snd.fst.snd.prodMk measurable_snd.snd.snd))).prodMk
      (measurable_snd.snd.fst.sub measurable_snd.fst.fst))

namespace OriginalPopulationCoefficientCore
variable {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}
variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

include hF hcomplete hu ha hinj in
/-- An auxiliary core reads exactly the same original coefficient cost on its
actual macro label image, so its local reference never changes the global cost. -/
theorem frozenQuadraticCost_eq_originalMacroCost {z : ℚ → M} (hz : z ∈ C.roots)
    (x y : (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) :
    C.frozenQuadraticCost z x y =
      physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex
        (physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex z) x y := by
  unfold physicalSceneOriginalMacroCost physicalSceneOriginalMacroCoefficient
  rw [physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj C.seedIndex
    (C.roots_subset_piece hz)]
  rfl

include hF hcomplete hu ha hinj in
/-- Compact original label continuity supplies inverse continuity on the
actual image, requiring no ambient continuity of the original population labels. -/
theorem continuousOn_originalMacroRootValue_image
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots) :
    ContinuousOn (physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex)
      (physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots) := by
  apply continuousOn_leftInverse_image_of_compact C.roots_compact
  · exact (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL.continuous.comp_continuousOn
      hlabel
  · intro z hz
    exact physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj C.seedIndex
      (C.roots_subset_piece hz)

include hF hcomplete hu ha hinj in
/-- The same original macro coefficient is continuous on each actual compact
core label image and the original complete legal clock-pair region. -/
theorem continuousOn_originalMacroCoefficient_image
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots) :
    ContinuousOn (physicalSceneOriginalMacroCoefficient (P := P) (a := a) C.seedIndex)
      ((physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots) ×ˢ
        C.window.region) := by
  let V := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ
  let W : Set V := physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots
  have hroot := C.continuousOn_originalMacroRootValue_image hF hcomplete hu ha hinj hlabel
  have hg : ContinuousOn (fun q : V × (ℝ × ℝ) ↦
      (physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex q.1, q.2))
      (W ×ˢ C.window.region) :=
    (hroot.comp continuous_fst.continuousOn (fun _ hq ↦ hq.1)).prodMk
      continuous_snd.continuousOn
  apply C.coefficient_continuous.comp hg
  rintro q ⟨⟨z, hz, hq⟩, hp⟩
  refine ⟨?_, hp⟩
  change physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex q.1 ∈ C.roots
  rw [← hq, physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj C.seedIndex
    (C.roots_subset_piece hz)]
  exact hz

include hF hcomplete hu ha hinj in
/-- Joint original tag/endpoints continuity is obtained on actual retained core
images. The globally defined cost still contains no core index or approximation. -/
theorem continuousOn_originalMacroCost_image
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots) :
    ContinuousOn (fun q : (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) ×
      (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) ×
        ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)) ↦
      physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex q.1 q.2.1 q.2.2)
      {q | q.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots ∧
        (q.2.1.2, q.2.2.2) ∈ C.window.region} := by
  let V := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ
  have hg : Continuous (fun q : V × ((V × ℝ) × (V × ℝ)) ↦ (q.1, q.2.1.2, q.2.2.2)) := by
    fun_prop
  have hc := (C.continuousOn_originalMacroCoefficient_image hF hcomplete hu ha hinj hlabel).comp
    hg.continuousOn (fun _ hq ↦ hq)
  have hd : Continuous (fun q : V × ((V × ℝ) × (V × ℝ)) ↦ q.2.2.1 - q.2.1.1) := by
    fun_prop
  exact continuous_matrixQuadratic.comp_continuousOn (hc.prodMk hd.continuousOn)

end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
