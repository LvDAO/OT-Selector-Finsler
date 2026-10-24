import OTSelector.Geometry.Finsler.Calibration.SeedPairReadout
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Original bounded physical probes for actual seed compact readouts

A compact test of the actual seed basis and the two original potential clocks is multiplied by
the indicator of that unchanged original source seed. The resulting original physical probe is
measurable and bounded. Its full integral is exactly the compact readout on the seed restriction.
-/

open Set Function MeasureTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff CompactlySupported

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}

/-- A compact seed readout test expressed as a bounded original physical probe. -/
def physicalSceneOriginalSeedCompactProbe (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ))
    (x y : M) : ℝ :=
  (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
    (lambda := lambda) j).indicator
      (fun x ↦ g (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j x,
        (u x, u y))) x

/-- Uncurrying the physical probe gives the literal indicator of the original seed pair set. -/
theorem uncurry_physicalSceneOriginalSeedCompactProbe (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)) :
    Function.uncurry (physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
      (lambda := lambda) j g) =
      (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ
        (univ : Set M)).indicator
          (fun p ↦ g (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)) := by
  funext p
  dsimp only [Function.uncurry, physicalSceneOriginalSeedCompactProbe]
  by_cases hx : p.1 ∈ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j
  · have hp : p ∈ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
        (lambda := lambda) j ×ˢ (univ : Set M) := ⟨hx, mem_univ _⟩
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hp]
    rfl
  · have hp : p ∉ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
        (lambda := lambda) j ×ˢ (univ : Set M) := fun hp ↦ hx hp.1
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hp]

/-- Every original physical probe value is bounded by its compact test's sup norm. -/
theorem abs_physicalSceneOriginalSeedCompactProbe_le (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ))
    (x y : M) :
    |physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
      (lambda := lambda) j g x y| ≤ ‖g.toBoundedContinuousFunction‖ := by
  by_cases hx : x ∈ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j
  · simpa [physicalSceneOriginalSeedCompactProbe, hx, Real.norm_eq_abs,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction] using
      g.toBoundedContinuousFunction.norm_coe_le_norm
        (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j x, (u x, u y))
  · simp only [physicalSceneOriginalSeedCompactProbe, Set.indicator_of_notMem hx, abs_zero]
    exact norm_nonneg _

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
include hF hcomplete hu ha hinj

/-- The same original compact physical probe is jointly measurable in both endpoints. -/
theorem measurable_uncurry_physicalSceneOriginalSeedCompactProbe (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)) :
    Measurable (Function.uncurry (physicalSceneOriginalSeedCompactProbe (P := P) (a := a)
      (κ := κ) (lambda := lambda) j g)) := by
  rw [uncurry_physicalSceneOriginalSeedCompactProbe]
  exact (g.continuous.measurable.comp
    (measurable_physicalSceneOriginalSeedPairReadout hF hcomplete hu ha hinj j)).indicator
      ((measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j).prod
        MeasurableSet.univ)

/-- A bounded original compact physical probe is integrable under every finite original plan. -/
theorem integrable_uncurry_physicalSceneOriginalSeedCompactProbe (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ))
    (π : Measure (M × M)) [IsFiniteMeasure π] :
    Integrable (Function.uncurry (physicalSceneOriginalSeedCompactProbe (P := P) (a := a)
      (κ := κ) (lambda := lambda) j g)) π := by
  refine Integrable.of_bound
    (measurable_uncurry_physicalSceneOriginalSeedCompactProbe
      hF hcomplete hu ha hinj j g).aestronglyMeasurable
    ‖g.toBoundedContinuousFunction‖ (ae_of_all _ fun p ↦ ?_)
  simpa only [Function.uncurry, Real.norm_eq_abs] using
    abs_physicalSceneOriginalSeedCompactProbe_le (P := P) (a := a) (κ := κ)
      (lambda := lambda) j g p.1 p.2

/-- The full original physical integral is exactly the compact readout of its seed restriction. -/
theorem integral_physicalSceneOriginalSeedCompactProbe_eq_restrict_readout (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ))
    (π : Measure (M × M)) :
    (∫ p, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
      (lambda := lambda) j g p.1 p.2 ∂π) =
      ∫ p, g (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂π.restrict (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
          (lambda := lambda) j ×ˢ (univ : Set M)) := by
  change (∫ p, Function.uncurry (physicalSceneOriginalSeedCompactProbe (P := P) (a := a)
    (κ := κ) (lambda := lambda) j g) p ∂π) = _
  rw [uncurry_physicalSceneOriginalSeedCompactProbe]
  exact integral_indicator
    ((measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j).prod
      MeasurableSet.univ)

end OTSelector.Reconstruction
