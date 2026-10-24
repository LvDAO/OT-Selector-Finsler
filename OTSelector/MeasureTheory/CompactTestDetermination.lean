import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.MeasureCompactTestDetermination.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.MeasureCompactTestDetermination`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.CompactTestDetermination

## Lemma skeleton

* **Conditions:** A sigma-compact locally compact Hausdorff pseudometrizable Borel carrier and equality of all nonnegative compact lower-integral tests against a reference finite on compacts.
* **Objects:** Equality of the whole measures, while producing the needed local mass control for the other measure.
* **Proof detail:** Use compact cutoffs to show finite mass on compact sets, then compare open-set masses via nonnegative compact tests and regularity/RMK uniqueness.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47): Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3): Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Nonnegative compact-test determination with local finiteness derived, not assumed for both inputs.
-/

/-! Nonnegative compact tests determine a whole measure and produce its local finiteness. -/
open Set MeasureTheory TopologicalSpace
open scoped CompactlySupported ENNReal
noncomputable section
namespace OTSelector.Probability

/-- Nonnegative compact-test means determine the whole measure and supply its local finiteness. -/
theorem measure_eq_of_nonnegative_compact_lintegrals
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (μ ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (h : ∀ (f : C_c(X, ℝ)), (∀ x, 0 ≤ f x) →
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂ν) : μ = ν := by
  have hμ : IsFiniteMeasureOnCompacts μ := by
    constructor
    intro K hK
    obtain ⟨f, hfK, hfb⟩ := LocalFiniteMeasure.exists_compact_cutoff hK
    calc
      μ K = ∫⁻ x, K.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μ := by
        rw [lintegral_indicator hK.measurableSet, lintegral_one, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ K
        · rw [indicator_of_mem hx]
          change 1 ≤ ENNReal.ofReal (f x)
          rw [hfK hx]
          norm_num
        · rw [indicator_of_notMem hx]
          exact bot_le
      _ = ∫⁻ x, ENNReal.ofReal (f x) ∂ν := h f (fun x ↦ (hfb x).1)
      _ < ∞ := by
        rw [← ofReal_integral_eq_lintegral_ofReal f.integrable (.of_forall (fun x ↦ (hfb x).1))]
        exact ENNReal.ofReal_lt_top
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  let g : C_c(X, ℝ) := f.toReal
  have hgn : ∀ x, 0 ≤ g x := fun x ↦ by simpa only [g, CompactlySupportedContinuousMap.toReal_apply] using (f x).coe_nonneg
  have he := h g hgn
  rw [← ofReal_integral_eq_lintegral_ofReal g.integrable (.of_forall hgn),
    ← ofReal_integral_eq_lintegral_ofReal g.integrable (.of_forall hgn)] at he
  have ht := congrArg ENNReal.toReal he
  simp only [g, CompactlySupportedContinuousMap.toReal_apply] at ht
  have hμn : 0 ≤ ∫ x, (f x : ℝ) ∂μ := integral_nonneg (fun x ↦ (f x).coe_nonneg)
  have hνn : 0 ≤ ∫ x, (f x : ℝ) ∂ν := integral_nonneg (fun x ↦ (f x).coe_nonneg)
  simpa only [ENNReal.toReal_ofReal hμn, ENNReal.toReal_ofReal hνn] using ht

end OTSelector.Probability

end
end
