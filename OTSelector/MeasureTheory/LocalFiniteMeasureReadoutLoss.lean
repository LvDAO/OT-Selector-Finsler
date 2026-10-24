import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Semicontinuity.Basic
import OTSelector.MeasureTheory.LocalFiniteMeasure

/-!
## Lemma skeleton

* **Conditions:** Positive locally finite full/retained/lost measures satisfy an exact additive decomposition. A compactly supported continuous real test is supported inside a measurable carrier. For the integrated bound, decomposition holds almost everywhere under an arbitrary sample measure.
* **Objects:** A compact-test discrepancy bounded by sup norm times actual lost carrier mass, and the corresponding extended nonnegative integral bound.
* **Proof detail:** Linearity reduces the discrepancy to the lost-measure integral. Bound its absolute value by the integral of the absolute test, then by the carrier indicator times the sup norm, and integrate the pointwise inequality.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99

**Relationship to the sources:** Local support form of the ordinary bounded-integral inequality. Lost mass on the chosen carrier may be infinite; compact support still makes each test integral finite. The final lower-integral inequality does not add measurability assumptions on the random maps.
-/

/-!
# Exact lost-plan bounds for compact test readouts

An exact retained-plus-lost decomposition bounds the original full test error
by the lost mass on any measurable carrier of that test. The same pointwise
bound integrates on the unchanged joint law; no marginal finiteness is needed.
-/
open Set MeasureTheory
open scoped ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Probability
namespace LocalFiniteMeasure
set_option backward.isDefEq.respectTransparency false

variable {Z Ω : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- The full compact-test error costs only actual lost mass on its carrier,
even when that source-window mass is infinite. -/
theorem ofReal_abs_testIntegral_sub_le_lost_mass
    (full retained lost : LocalFiniteMeasure Z)
    (hdecomp : (full : Measure Z) = (retained : Measure Z) + (lost : Measure Z))
    (χ : C_c(Z, ℝ)) (U : Set Z) (hU : MeasurableSet U) (hχU : tsupport χ ⊆ U) :
    ENNReal.ofReal |testIntegral full χ - testIntegral retained χ| ≤
      ENNReal.ofReal ‖χ.toBoundedContinuousFunction‖ * (lost : Measure Z) U := by
  have heq : testIntegral full χ = testIntegral retained χ + testIntegral lost χ := by
    unfold testIntegral
    rw [hdecomp, integral_add_measure χ.integrable χ.integrable]
  rw [heq, add_sub_cancel_left]
  have hnorm : ENNReal.ofReal |testIntegral lost χ| ≤
      ∫⁻ z, ENNReal.ofReal |χ z| ∂(lost : Measure Z) := by
    simpa only [testIntegral, Real.enorm_eq_ofReal_abs] using
      (enorm_integral_le_lintegral_enorm (μ := (lost : Measure Z)) (fun z ↦ χ z))
  refine hnorm.trans ?_
  calc
    (∫⁻ z, ENNReal.ofReal |χ z| ∂(lost : Measure Z)) ≤
        ∫⁻ z, U.indicator (fun _ ↦ ENNReal.ofReal ‖χ.toBoundedContinuousFunction‖) z
          ∂(lost : Measure Z) := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ U
      · rw [indicator_of_mem hz]
        apply ENNReal.ofReal_le_ofReal
        have hzbound := χ.toBoundedContinuousFunction.norm_coe_le_norm z
        change ‖χ z‖ ≤ ‖χ.toBoundedContinuousFunction‖ at hzbound
        simpa only [Real.norm_eq_abs] using hzbound
      · rw [indicator_of_notMem hz]
        change ENNReal.ofReal |χ z| ≤ 0
        rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hz (hχU ht))]
        simp
    _ = _ := lintegral_indicator_const hU _

variable [MeasurableSpace Ω]

/-- The same full/retained/lost joint law keeps the compact-test error bound
in expectation. A scalar lost-mass expectation bound can be inserted directly. -/
theorem lintegral_abs_testIntegral_sub_le_lost_mass
    (R : Measure Ω) (full retained lost : Ω → LocalFiniteMeasure Z)
    (hdecomp : ∀ᵐ s ∂R, (full s : Measure Z) =
      (retained s : Measure Z) + (lost s : Measure Z))
    (χ : C_c(Z, ℝ)) (U : Set Z) (hU : MeasurableSet U) (hχU : tsupport χ ⊆ U) :
    (∫⁻ s, ENNReal.ofReal |testIntegral (full s) χ - testIntegral (retained s) χ| ∂R) ≤
      ENNReal.ofReal ‖χ.toBoundedContinuousFunction‖ * ∫⁻ s, (lost s : Measure Z) U ∂R := by
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal ‖χ.toBoundedContinuousFunction‖ *
        (lost s : Measure Z) U ∂R := by
      apply lintegral_mono_ae
      filter_upwards [hdecomp] with s hs
      exact ofReal_abs_testIntegral_sub_le_lost_mass (full s) (retained s) (lost s)
        hs χ U hU hχU
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end LocalFiniteMeasure
end OTSelector.Probability
