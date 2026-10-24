import OTSelector.Reconstruction.FinslerCoefficientPressureFreezing
import OTSelector.Reconstruction.FinslerCoefficientCoreLabel
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
The original compact scalar region supplies the modulus for finite clock-class
resampling. Both the relative kinetic error and the physical probe error are
produced from the actual coefficient, ellipticity and original complete curve.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry
open scoped ENNReal Topology ContDiff Matrix.Norms.Operator BoundedContinuousFunction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The actual reference-root physical pair probe in the original potential clock. -/
def originalReferenceClockProbe
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M → ℝ) (p : ℝ × ℝ) : ℝ :=
  let S := (P C.seedIndex).seed
  let w := populationSeedPieceLabel P a κ lambda C.seedIndex ⟨z₀, C.roots_subset_piece hz₀⟩
  f (S.curve w.val (p.1 - S.level), S.curve w.val (p.2 - S.level))

/-- Any desired finite-class kinetic and probe tolerances are obtained from the
actual original coefficient. Only legal pairs inside the retained compact
scalar region are compared. -/
theorem OriginalPopulationCoefficientCore.exists_uniform_clock_resampling
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex) (z₀ : Z) (hz₀ : z₀ ∈ C.roots)
    (f : M × M → ℝ) (hf : Continuous f) {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ p ∈ C.window.region, ∀ p₀ ∈ C.window.region,
      |p.1 - p₀.1| < mesh → |p.2 - p₀.2| < mesh →
      (∀ v, |matrixQuadratic (C.matrix z₀ p) v - matrixQuadratic (C.matrix z₀ p₀) v| ≤
        ε * matrixQuadratic (C.matrix z₀ p₀) v) ∧
      |originalReferenceClockProbe C z₀ hz₀ f p -
        originalReferenceClockProbe C z₀ hz₀ f p₀| ≤ B := by
  have hA : ContinuousOn (C.matrix z₀) C.window.region :=
    C.coefficient_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp ↦ ⟨hz₀, hp⟩)
  obtain ⟨meshA, hmeshA, hrelative⟩ := exists_uniform_relative_matrixQuadratic
    C.window.isCompact_region hA (fun p hp ↦ C.coefficient_posDef z₀ hz₀ p hp) hε
  let S := (P C.seedIndex).seed
  let w := populationSeedPieceLabel P a κ lambda C.seedIndex ⟨z₀, C.roots_subset_piece hz₀⟩
  have hc : Continuous (S.curve w.val) := continuous_iff_continuousAt.mpr fun t ↦
    (hF.contMDiffAt_of_isEulerLagrangeAt (S.complete w.val w.property t (mem_univ _))).continuousAt
  have hprobe : Continuous (originalReferenceClockProbe C z₀ hz₀ f) :=
    hf.comp ((hc.comp (continuous_fst.sub continuous_const)).prodMk
      (hc.comp (continuous_snd.sub continuous_const)))
  obtain ⟨meshP, hmeshP, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (C.window.isCompact_region.uniformContinuousOn_of_continuous hprobe.continuousOn) B hB
  refine ⟨min meshA meshP, lt_min hmeshA hmeshP, fun p hp p₀ hp₀ hs ht ↦ ?_⟩
  have hdist : dist p p₀ < min meshA meshP := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using And.intro hs ht
  refine ⟨hrelative p hp p₀ hp₀ (hdist.trans_le (min_le_left _ _)), ?_⟩
  exact (show |originalReferenceClockProbe C z₀ hz₀ f p -
      originalReferenceClockProbe C z₀ hz₀ f p₀| < B by
    simpa only [Real.dist_eq] using hclose p hp p₀ hp₀
      (hdist.trans_le (min_le_right _ _))).le

end OTSelector.Reconstruction
