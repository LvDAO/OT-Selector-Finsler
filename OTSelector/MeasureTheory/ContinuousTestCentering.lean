import Mathlib.MeasureTheory.Integral.DominatedConvergence
import OTSelector.Topology.CompactCutoffExhaustion
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.ContinuousClockCentering.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.ContinuousClockCentering`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ContinuousTestCentering

## Lemma skeleton

* **Conditions:** An integrable signed observable, measurable clock into a locally compact second-countable Hausdorff Borel target and zero pairing with every continuous clock test.
* **Objects:** Exact zero integrals on pulled-back open and Borel clock sets.
* **Proof detail:** Approximate open-set indicators by continuous functions and use dominated convergence; extend the zero identity to the generated Borel sigma-algebra.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=107): Section 3B, Theorem 3.31, p. 92 (Dominated Convergence).
- [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=254): Appendix A.1, Theorem A.5, p. 242.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.

Source relation (composition): Continuous-test determination of the signed clock pushforward; exact target setup is in the frozen source.
-/

/-! Continuous first-variation tests imply exact Borel-clock centering. -/
open Set Function Filter MeasureTheory
open scoped Topology CompactlySupported
noncomputable section
namespace OTSelector.Probability

variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
  [LocallyCompactSpace Y] [SecondCountableTopology Y]

/-- An integrable original momentum centered against continuous clock tests
has zero integral over every original open clock event. -/
theorem setIntegral_preimage_eq_zero_of_continuous_tests_of_isOpen
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ)
    (clock : X → Y) (hclock : Measurable clock)
    (htest : ∀ g : C(Y, ℝ), (∫ x, f x * g (clock x) ∂μ) = 0)
    (U : Set Y) (hU : IsOpen U) : ∫ x in clock ⁻¹' U, f x ∂μ = 0 := by
  obtain ⟨χ, hb, hs, he⟩ := exists_compact_cutoffs_eventually_one_of_isOpen U hU
  have hz (n : ℕ) (y : Y) (hy : y ∉ U) : χ n y = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hy' ↦ hy (hs n hy')
  have hconv := tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
    (F := fun n x ↦ f x * χ n (clock x))
    (f := (clock ⁻¹' U).indicator f)
    (fun n ↦ hf.aestronglyMeasurable.mul
      ((χ n).continuous.measurable.comp hclock).aestronglyMeasurable)
    hf.norm (fun n ↦ ae_of_all _ fun x ↦ by
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (hb n (clock x)).1]
      exact (hb n (clock x)).2)
    (ae_of_all _ fun x ↦ by
      by_cases hx : clock x ∈ U
      · have hlim : ∀ᶠ n in atTop, f x * χ n (clock x) = f x := by
          filter_upwards [he (clock x) hx] with n hn
          simp only [hn, mul_one]
        rw [Set.indicator_of_mem (show x ∈ clock ⁻¹' U from hx)]
        exact tendsto_const_nhds.congr' (hlim.mono fun _ hn ↦ hn.symm)
      · have hx' : x ∉ clock ⁻¹' U := hx
        simp only [Set.indicator_of_notMem hx']
        have hzero : (fun n ↦ f x * χ n (clock x)) = fun _ ↦ (0 : ℝ) := by
          funext n
          rw [hz n (clock x) hx, mul_zero]
        rw [hzero]
        exact tendsto_const_nhds)
  have hzero : (fun n ↦ ∫ x, f x * χ n (clock x) ∂μ) = fun _ ↦ (0 : ℝ) := by
    funext n
    exact htest (χ n).toContinuousMap
  rw [hzero] at hconv
  have hI : (∫ x, (clock ⁻¹' U).indicator f x ∂μ) = 0 :=
    tendsto_nhds_unique hconv tendsto_const_nhds
  rwa [integral_indicator (hU.measurableSet.preimage hclock)] at hI

/-- Continuous clock tests already determine every Borel-clock integral of
the same integrable momentum. No conditional law or density is supplied. -/
theorem setIntegral_preimage_eq_zero_of_continuous_tests
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ)
    (clock : X → Y) (hclock : Measurable clock)
    (htest : ∀ g : C(Y, ℝ), (∫ x, f x * g (clock x) ∂μ) = 0)
    (B : Set Y) (hB : MeasurableSet B) : ∫ x in clock ⁻¹' B, f x ∂μ = 0 := by
  have hwhole : (∫ x, f x ∂μ) = 0 := by
    simpa using htest (ContinuousMap.const Y (1 : ℝ))
  induction B, hB using MeasurableSet.induction_on_open with
  | isOpen U hU =>
    exact setIntegral_preimage_eq_zero_of_continuous_tests_of_isOpen
      μ f hf clock hclock htest U hU
  | compl B hB ih =>
    have h := integral_add_compl (hB.preimage hclock) hf
    rw [ih, hwhole, zero_add] at h
    simpa only [preimage_compl] using h
  | iUnion B hdisj hm ih =>
    rw [preimage_iUnion]
    rw [integral_iUnion (fun n ↦ (hm n).preimage hclock)
      (fun i j hij ↦ (hdisj hij).preimage clock) hf.integrableOn]
    simp only [ih, tsum_zero]

end OTSelector.Probability

end
end
