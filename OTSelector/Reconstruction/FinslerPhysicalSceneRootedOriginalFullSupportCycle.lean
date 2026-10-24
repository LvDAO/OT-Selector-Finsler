import OTSelector.Transport.CyclicMonotonicity.MeasureSupport
import OTSelector.MeasureTheory.PairWeakCycleSupport
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicOriginalCoefficient
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedStrictClockExhaustion

/-!
# Full-plan support cycles at the original varying macroscopic coefficient

The almost-everywhere four-edge inequality of the SAME full arithmetic average
extends to its actual support on each original strict clock window. Continuity
comes from the original coefficient on the actual compact core label image.
The cost retains its actual macro tag, independently of the auxiliary core index.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

section StrictClock
variable {ι : Type*} [Fintype ι]

/-- The original strict scalar-pair clock domain is open in marked endpoints. -/
theorem isOpen_physicalSceneStrictClockRegion (q : RationalScalarPairWindow) :
    IsOpen (physicalSceneStrictClockRegion (ι := ι) q) := by
  exact (isOpen_Ioo.preimage continuous_fst.snd).inter
    ((isOpen_Ioo.preimage continuous_snd.snd).inter
      (isOpen_lt continuous_const (continuous_snd.snd.sub continuous_fst.snd)))

/-- Every strict clock-legal edge lies in the original closed scalar-pair
region where the original coefficient has its given continuity. -/
theorem clocks_mem_region_of_mem_physicalSceneStrictClockRegion
    (q : RationalScalarPairWindow) {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (he : e ∈ physicalSceneStrictClockRegion q) : (e.1.2, e.2.2) ∈ q.region := by
  rcases he with ⟨hs, ht, hg⟩
  exact ⟨⟨⟨hs.1.le, hs.2.le⟩, ⟨ht.1.le, ht.2.le⟩⟩, hg.le⟩
end StrictClock

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore
variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- At an actual original macro label in the compact core image, the SAME
original macro cost is continuous on the whole original strict clock domain. -/
theorem continuousOn_originalMacroCost_strictClock
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots)
    {w : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ}
    (hw : w ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots) :
    ContinuousOn
      (Function.uncurry (physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w))
      (physicalSceneStrictClockRegion C.window) := by
  let X := (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ
  have hf : Continuous (fun e : X × X ↦ (w, e)) :=
    continuous_const.prodMk continuous_id
  exact (C.continuousOn_originalMacroCost_image hF hcomplete hu ha hinj hlabel).comp
    (f := fun e : X × X ↦ (w, e)) hf.continuousOn
    (fun e he ↦ ⟨hw, clocks_mem_region_of_mem_physicalSceneStrictClockRegion C.window he⟩)

/-- The original full-plan almost-everywhere inequality upgrades to a pointwise
support relation at this actual macro tag. No frozen global coefficient is used. -/
theorem isTwoCycleMonotoneOn_originalMacroCost_full_support_of_ae
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots)
    {w : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ}
    (hw : w ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots)
    (π : Measure
      (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) ×
        ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ))) [SFinite π]
    (hcycle : ∀ᵐ p ∂π.prod π,
      p.1 ∈ physicalSceneStrictClockRegion C.window →
      p.2 ∈ physicalSceneStrictClockRegion C.window →
      (p.1.1, p.2.2) ∈ physicalSceneStrictClockRegion C.window →
      (p.2.1, p.1.2) ∈ physicalSceneStrictClockRegion C.window →
      physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w p.1.1 p.1.2 +
        physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w p.2.1 p.2.2 ≤
      physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w p.1.1 p.2.2 +
        physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w p.2.1 p.1.2) :
    IsTwoCycleMonotoneOn
      (physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w)
      (physicalSceneStrictClockRegion C.window)
      (π.support ∩ physicalSceneStrictClockRegion C.window) :=
  isTwoCycleMonotoneOn_support_of_ae π
    (physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex w)
    (isOpen_physicalSceneStrictClockRegion C.window)
    (C.continuousOn_originalMacroCost_strictClock hF hcomplete hu ha hinj hlabel hw) hcycle

end OriginalPopulationCoefficientCore

variable [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
variable (j : ℕ)
set_option quotPrecheck false
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Edge" => (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
local notation "PairScene" => CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "MacroScene" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (PairScene × LocalConfiguration base)

/-- On one probability-one event of the SAME full macroscopic scene law,
every original core in the fixed seed frame has the pointwise full-support
cycle relation whenever the actual tag belongs to its original label image.
Original Haar-core label continuity is supplied internally. -/
theorem ae_original_full_support_strictClock_twoCycle_of_ae
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (Rlaw : ProbabilityMeasure MacroScene)
    (hcycle : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).seedIndex = j →
      ∀ᵐ s ∂(Rlaw : Measure MacroScene),
        s.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
          (D.haar.continuous.coefficient i).roots →
        ∀ᵐ p ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).prod
          (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
          p.1 ∈ physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window →
          p.2 ∈ physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window →
          (p.1.1, p.2.2) ∈ physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window →
          (p.2.1, p.1.2) ∈ physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window →
          physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.1.1 p.1.2 +
            physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.2.1 p.2.2 ≤
          physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.1.1 p.2.2 +
            physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.2.1 p.1.2) :
    ∀ᵐ s ∂(Rlaw : Measure MacroScene), ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).seedIndex = j →
      s.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
        (D.haar.continuous.coefficient i).roots →
      IsTwoCycleMonotoneOn (physicalSceneOriginalMacroCost (P := P) (a := a) j s.1)
        (physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window)
        ((LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).support ∩
          physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window) := by
  classical
  have hlocal (i : Fin D.haar.continuous.count)
      (hi : (D.haar.continuous.coefficient i).seedIndex = j) :
      ∀ᵐ s ∂(Rlaw : Measure MacroScene),
        s.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
          (D.haar.continuous.coefficient i).roots →
        IsTwoCycleMonotoneOn (physicalSceneOriginalMacroCost (P := P) (a := a) j s.1)
          (physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window)
          ((LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).support ∩
            physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window) := by
    filter_upwards [hcycle i hi] with s hs htag
    subst j
    have hlabel : ContinuousOn
        (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a)
        (D.haar.continuous.coefficient i).roots := by
      rw [← D.haar.intensity_roots i]
      exact (D.haar.intensity i).continuous_label
    exact (D.haar.continuous.coefficient i).isTwoCycleMonotoneOn_originalMacroCost_full_support_of_ae
      hF hcomplete hu ha hinj hlabel htag
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure _) (hs htag)
  apply ae_all_iff.mpr
  intro i
  by_cases hi : (D.haar.continuous.coefficient i).seedIndex = j
  · exact (hlocal i hi).mono fun _ hs _ ↦ hs
  · exact ae_of_all _ fun _ h ↦ False.elim (hi h)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
