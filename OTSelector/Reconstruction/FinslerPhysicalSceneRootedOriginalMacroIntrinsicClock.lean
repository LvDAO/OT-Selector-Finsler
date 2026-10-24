import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalIntrinsicClockRigidity
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicOriginalCoefficient

/-! The actual original macro cost equals the literal original compliance cost
throughout every clock pair on its genuine original seed label. Closed original
coefficient windows lie inside that same intrinsic clock domain. -/
open Set Function Matrix Module Manifold MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- At every genuine original label, the macro root reads that same original root. -/
theorem physicalSceneOriginalMacroRootValue_at_seedLabel (j : ℕ)
    (w : (P j).seed.labels) :
    physicalSceneOriginalMacroRootValue (P := P) (a := a) j
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFun w.val) =
        a ((P j).seed.curve w 0) := by
  unfold physicalSceneOriginalMacroRootValue
  rw [LinearEquiv.symm_apply_apply]
  rw [populationSeedPhysicalMap_at_label]
  simp only [sub_self]

/-- The cost identity holds on ALL clock pairs, at the same genuine macro tag. -/
theorem physicalSceneOriginalMacroCost_eq_intrinsicClockCost (j : ℕ)
    {w : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ}
    (hw : (Module.finBasis ℝ (P j).seed.covector.ker).equivFun.symm w ∈
      (P j).seed.labels) :
    physicalSceneOriginalMacroCost (P := P) (a := a) j w =
      physicalSceneOriginalIntrinsicClockCost (P j).seed
        ((Module.finBasis ℝ (P j).seed.covector.ker).equivFun.symm w) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let label : (P j).seed.labels := ⟨_, hw⟩
  have hroot := physicalSceneOriginalMacroRootValue_at_seedLabel hF hcomplete hu ha hinj j label
  simp only [label, LinearEquiv.apply_symm_apply] at hroot
  funext x y
  unfold physicalSceneOriginalMacroCost physicalSceneOriginalMacroCoefficient
  rw [hroot]
  change matrixQuadratic (populationSeedRootCoefficient (P j).seed a
    (Module.finBasis ℝ (P j).seed.covector.ker) (a ((P j).seed.curve label 0), x.2, y.2))
      (y.1 - x.1) = _
  rw [populationSeedRootCoefficient_at_label (P j).seed hF hcomplete hu ha hinj
    (Module.finBasis ℝ (P j).seed.covector.ker) label x.2 y.2]
  rfl

namespace OriginalPopulationCoefficientCore
variable {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}
  (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- One nonempty original core label image supplies actual moments at the
unchanged basis-inverse macro label, with its original conditional clock laws. -/
theorem exists_intrinsicClockMoments_of_macroLabel
    {w : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ}
    (hw : w ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots) :
    ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun.symm w ∈
      (P C.seedIndex).seed.labels) ∧
    ∃ μ ν : Measure ℝ, Nonempty (OriginalSeedConditionalMoments (P C.seedIndex).seed
      ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun.symm w) μ ν) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨z, hz, rfl⟩ := hw
  obtain ⟨label, hlabel, D, _, _⟩ := C.original_window z hz
  have heq : (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun.symm
      (physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex z) = label.val := by
    unfold physicalSceneOriginalMacroLabel
    rw [LinearEquiv.symm_apply_apply, ← hlabel,
      populationSeedRootLabelValue_at_label (P C.seedIndex).seed hF hcomplete hu ha hinj]
  rw [heq]
  exact ⟨label.property, _, _, ⟨D⟩⟩

/-- A closed original pair window is already inside the true open calibrated
clock domain. Its positive original gap supplies the strict forward inequality. -/
theorem mem_intrinsicClockDomain_of_macroLabel_region
    {w : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ}
    (hw : w ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots)
    {p : (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) ×
      ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ))}
    (hp : (p.1.2, p.2.2) ∈ C.window.region) :
    p ∈ physicalSceneOriginalIntrinsicClockDomain (P C.seedIndex).seed
      ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun.symm w) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨z, hz, rfl⟩ := hw
  have ht := C.calibrated_label_interval hF hcomplete hu ha hinj hz
  have hp' := C.window.region_subset hp
  unfold physicalSceneOriginalMacroLabel
  rw [LinearEquiv.symm_apply_apply]
  exact ⟨ht ⟨sub_le_sub_right hp'.1.1 _, sub_le_sub_right hp'.1.2 _⟩,
    ht ⟨sub_le_sub_right hp'.2.1.1 _, sub_le_sub_right hp'.2.1.2 _⟩, hp'.2.2⟩
end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
