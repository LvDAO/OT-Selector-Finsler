import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Semicontinuity.Basic
import OTSelector.MeasureTheory.LocalFiniteMeasure

/-!
## Lemma skeleton

* **Conditions:** An open exhaustion dominating every compact set and finite local mass bounds.
* **Objects:** A compact set of locally finite measures.
* **Proof detail:** Bound all compact-test integrals and close the constraints using open-set lower semicontinuity.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47
* Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*, Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
  https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4

**Relationship to the sources:** The open-exhaustion constants and exact sublevel set are a locally proved compact-containment form of vague compactness.
-/

/-!
# Compact containment from actual local mass bounds

Bounds on an open exhaustion control every compact-test integral. Lower
semicontinuity of open-window mass makes the resulting family closed, hence
compact in the actual vague topology, without an atomicity assumption.
-/

open MeasureTheory Set Function Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal

noncomputable section
namespace OTSelector.Probability.LocalFiniteMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X]

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] in
/-- The actual integral is bounded by the window mass times the test supremum. -/
theorem abs_testIntegral_le_localMass (μ : LocalFiniteMeasure X) (f : C_c(X, ℝ))
    {U : Set X} (hsupport : tsupport f ⊆ U) {C : ℝ≥0}
    (hmass : (μ : Measure X) U ≤ C) :
    |testIntegral μ f| ≤ ‖f.toBoundedContinuousFunction‖ * C := by
  have hfinite : (μ : Measure X) U < ∞ := hmass.trans_lt ENNReal.coe_lt_top
  have heq : (∫ x in U, f x ∂(μ : Measure X)) = ∫ x, f x ∂(μ : Measure X) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsupport h)))
  unfold testIntegral
  rw [← heq]
  calc
    _ ≤ ‖f.toBoundedContinuousFunction‖ * (μ : Measure X).real U := by
      simpa only [Real.norm_eq_abs, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using norm_setIntegral_le_of_norm_le_const_ae hfinite
        (Filter.Eventually.of_forall (fun x ↦ f.toBoundedContinuousFunction.norm_coe_le_norm x))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by simpa only [measureReal_def, ENNReal.coe_toReal] using
        ENNReal.toReal_mono ENNReal.coe_ne_top hmass) (norm_nonneg _)

/-- Uniform finite bounds on an open exhaustion form a compact family of actual
locally finite measures. The bounds may vary arbitrarily with the window. -/
theorem isCompact_localMass_le (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hcover : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ U n) (C : ℕ → ℝ≥0) :
    IsCompact {μ : LocalFiniteMeasure X | ∀ n, (μ : Measure X) (U n) ≤ C n} := by
  choose index hindex using fun f : C_c(X, ℝ) ↦ hcover (tsupport f) f.hasCompactSupport
  let bound : C_c(X, ℝ) → ℝ := fun f ↦ ‖f.toBoundedContinuousFunction‖ * C (index f)
  have hclosed : IsClosed {μ : LocalFiniteMeasure X |
      ∀ n, (μ : Measure X) (U n) ≤ C n} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun n ↦ (lowerSemicontinuous_measure_open (hU n)).isClosed_preimage _)
  apply (isCompact_testIntegral_bounds bound).of_isClosed_subset hclosed
  intro μ hμ f
  exact abs_le.mp (abs_testIntegral_le_localMass μ f (hindex f) (hμ (index f)))

/-- A compact exhaustion supplies the open windows internally. -/
theorem isCompact_exhaustionMass_le (K : CompactExhaustion X) (C : ℕ → ℝ≥0) :
    IsCompact {μ : LocalFiniteMeasure X |
      ∀ n, (μ : Measure X) (interior (K n)) ≤ C n} := by
  apply isCompact_localMass_le _ (fun _ ↦ isOpen_interior) _ C
  intro A hA
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hA
  exact ⟨n + 1, hn.trans (K.subset_interior_succ n)⟩

end OTSelector.Probability.LocalFiniteMeasure
