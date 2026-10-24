import OTSelector.Reconstruction.OriginalPathLengthRetention
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # Actual full-path length tails vanish without a diameter moment -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Any real measurable readout has vanishing upper-level mass under its own finite law. -/
theorem tendsto_measure_real_readout_gt_atTop
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) :
    Tendsto (fun R : ℝ ↦ μ {x | R < f x}) atTop (𝓝 0) := by
  have hanti : Antitone (fun R : ℝ ↦ {x | R < f x}) := by
    intro R S hRS x hx
    exact hRS.trans_lt hx
  have hcap : (⋂ R : ℝ, {x | R < f x}) = ∅ := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro h
    exact (lt_irrefl (f x)) (h (f x))
  have h := tendsto_measure_iInter_atTop
    (μ := μ) (fun R : ℝ ↦ (measurableSet_lt measurable_const hf).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ _⟩
  simpa only [hcap, measure_empty, Function.comp_def] using h

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The same original true-Palm path length has vanishing tail probability, with
no second displacement or path-diameter moment assumed. -/
theorem tendsto_original_truePalm_pathLength_tail
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) :
    Tendsto (fun R : ℝ ↦ (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
      {m | R < originalSeedPairPathLength S w m}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    Q.palm_probability
  exact tendsto_measure_real_readout_gt_atTop _ (measurable_originalSeedPairPathLength S hF hw)

/-- The original tail probability also vanishes as a real expectation factor. -/
theorem tendsto_original_truePalm_pathLength_tail_real
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) :
    Tendsto (fun R : ℝ ↦ (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).real
      {m | R < originalSeedPairPathLength S w m}) atTop (𝓝 0) := by
  simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_original_truePalm_pathLength_tail hF hw Q)

end OTSelector.Reconstruction
