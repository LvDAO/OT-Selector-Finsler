import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import OTSelector.Topology.UniformContinuousApproximation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneFixedSourceProbeWeakContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneFixedSourceProbeWeakContinuity`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.FixedSourceWeakReadout

## Lemma skeleton

* **Conditions:** A fixed first marginal and physical readouts uniformly approximable on that carrier by bounded continuous tests; a pointwise bound is required for the bounded extension.
* **Objects:** Closed fixed-source probability carrier and a continuous readout there with a norm-controlled bounded continuous extension.
* **Proof detail:** Use continuity of pushforward for closedness, uniform approximation for continuity of the actual integral and Tietze plus clipping for its bounded extension.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=14): Section 4A2F(d-ix), p. 14 (Tietze extension theorem).
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=235): Section 6.2.1, Theorem 6.2.2, p. 235.

Source relation (composition): Fixed-source approximation/extension theorem; the original probe itself need not be continuous.
-/

/-!
# Weakly continuous readouts on the same fixed-source probability carrier

Uniform bounded continuous approximations on the original fixed-source family
produce a continuous readout there. Its bounded extension then applies directly
to weak laws without assuming continuity of the original physical probe.
-/
open Set Function MeasureTheory Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option linter.unusedSectionVars false

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The full probability plans with one unchanged original source law form a
closed carrier for the ordinary weak topology of original physical plans. -/
theorem isClosed_probability_fixed_source (μ : Measure X) [IsProbabilityMeasure μ] :
    IsClosed {π : ProbabilityMeasure (X × Y) | (π : Measure (X × Y)).fst = μ} := by
  let μprob : ProbabilityMeasure X := ⟨μ, inferInstance⟩
  have hclosed := isClosed_eq
    (ProbabilityMeasure.continuous_map (continuous_fst : Continuous (Prod.fst : X × Y → X)))
    (continuous_const : Continuous (fun _ : ProbabilityMeasure (X × Y) ↦ μprob))
  convert hclosed using 1
  ext π
  constructor
  · intro h
    exact ProbabilityMeasure.toMeasure_injective h
  · intro h
    exact congrArg (fun ν : ProbabilityMeasure X ↦ (ν : Measure X)) h

/-- Uniform approximations control continuity on the fixed original source
carrier, although the original probe may only be measurable. -/
theorem continuousOn_probability_integral_of_uniform_source_approx
    (μ : Measure X) (f : X × Y → ℝ)
    (happrox : ∀ ε > 0, ∃ G : (X × Y) →ᵇ ℝ,
      ∀ π : ProbabilityMeasure (X × Y), (π : Measure (X × Y)).fst = μ →
        |(∫ p, f p ∂(π : Measure (X × Y))) - ∫ p, G p ∂(π : Measure (X × Y))| ≤ ε) :
    ContinuousOn (fun π : ProbabilityMeasure (X × Y) ↦
      ∫ p, f p ∂(π : Measure (X × Y))) {π | (π : Measure (X × Y)).fst = μ} := by
  apply continuousOn_of_uniform_real_continuous_approx
  intro ε hε
  obtain ⟨G, hG⟩ := happrox ε hε
  exact ⟨fun π ↦ ∫ p, G p ∂(π : Measure (X × Y)),
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).continuousOn, hG⟩

/-- A bounded original readout has one globally bounded continuous extension
from the same closed fixed-source family. -/
theorem exists_boundedContinuous_probability_integral_extension_of_source_approx
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X × Y → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hfBound : ∀ p, |f p| ≤ B)
    (happrox : ∀ ε > 0, ∃ G : (X × Y) →ᵇ ℝ,
      ∀ π : ProbabilityMeasure (X × Y), (π : Measure (X × Y)).fst = μ →
        |(∫ p, f p ∂(π : Measure (X × Y))) - ∫ p, G p ∂(π : Measure (X × Y))| ≤ ε) :
    ∃ L : ProbabilityMeasure (X × Y) →ᵇ ℝ, ‖L‖ ≤ B ∧
      ∀ π : ProbabilityMeasure (X × Y), (π : Measure (X × Y)).fst = μ →
        L π = ∫ p, f p ∂(π : Measure (X × Y)) := by
  let C : Set (ProbabilityMeasure (X × Y)) :=
    {π | (π : Measure (X × Y)).fst = μ}
  let readout : ProbabilityMeasure (X × Y) → ℝ := fun π ↦
    ∫ p, f p ∂(π : Measure (X × Y))
  have hcont : ContinuousOn readout C :=
    continuousOn_probability_integral_of_uniform_source_approx μ f happrox
  have hbound (π : ProbabilityMeasure (X × Y)) : |readout π| ≤ B := by
    have h := norm_integral_le_of_norm_le_const
      (μ := (π : Measure (X × Y))) (f := f)
      (ae_of_all _ fun p ↦ (Real.norm_eq_abs (f p)).symm ▸ hfBound p)
    simpa only [readout, Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h
  let LC : C →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun π ↦ readout π, continuousOn_iff_continuous_domRestrict.mp hcont⟩
    (2 * B) (fun π τ ↦ by
      change dist (readout π) (readout τ) ≤ 2 * B
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hbound π, hbound τ]))
  obtain ⟨L, hLbound, hLeq⟩ :=
    LC.exists_extension_forall_mem_Icc_of_isClosedEmbedding
      (fun π ↦ abs_le.mp (hbound π)) (by linarith : -B ≤ B)
      (isClosed_probability_fixed_source μ).isClosedEmbedding_subtypeVal
  refine ⟨L, ?_, ?_⟩
  · apply (BoundedContinuousFunction.norm_le hB).mpr
    intro π
    simpa only [Real.norm_eq_abs] using abs_le.mpr (hLbound π)
  · intro π hπ
    exact congrFun hLeq ⟨π, hπ⟩

end OTSelector.Reconstruction

end
end
