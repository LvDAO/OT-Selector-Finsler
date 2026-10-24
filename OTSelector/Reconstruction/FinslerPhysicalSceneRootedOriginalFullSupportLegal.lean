import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalFullSupportCycle

/-!
# One global original legal inequality supplies every full-support core

The SAME full average's global four-clock legal inequality implies each original
core-window inequality. Strict core legality is strictly forward because the
original rational window has a positive gap. No per-core callback remains.
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

/-- Strict legality in an original positive-gap window is strictly forward in
its actual separate source and target clocks. -/
theorem clock_lt_of_mem_physicalSceneStrictClockRegion
    {ι : Type*} [Fintype ι] (q : RationalScalarPairWindow)
    {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (he : e ∈ physicalSceneStrictClockRegion q) : e.1.2 < e.2.2 := by
  have hd : 0 < (q.val.2.2 : ℝ) := by exact_mod_cast q.property.2
  exact sub_pos.mp (hd.trans he.2.2)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

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

/-- A single full-average AE original legal-cycle inequality supplies the
pointwise support relation on every original core in the same fixed seed frame.
The actual canonical cost continues to vary with the macro tag. -/
theorem ae_original_full_support_strictClock_twoCycle_of_legal
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (Rlaw : ProbabilityMeasure MacroScene)
    (hcycle : ∀ᵐ s ∂(Rlaw : Measure MacroScene),
      ∀ᵐ p ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).prod
        (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
        (p.1.1.2 < p.1.2.2 ∧ p.2.1.2 < p.2.2.2 ∧
          p.1.1.2 < p.2.2.2 ∧ p.2.1.2 < p.1.2.2) →
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
  apply D.ae_original_full_support_strictClock_twoCycle_of_ae j base
    hF hcomplete hu ha hinj Rlaw
  intro i hi
  filter_upwards [hcycle] with s hs htag
  filter_upwards [hs] with p hp h₀₀ h₁₁ h₀₁ h₁₀
  exact hp ⟨clock_lt_of_mem_physicalSceneStrictClockRegion _ h₀₀,
    clock_lt_of_mem_physicalSceneStrictClockRegion _ h₁₁,
    clock_lt_of_mem_physicalSceneStrictClockRegion _ h₀₁,
    clock_lt_of_mem_physicalSceneStrictClockRegion _ h₁₀⟩

end PopulationLocalPressureCore
end OTSelector.Reconstruction
