import OTSelector.PointProcess.LocalConfigurationTuple
import OTSelector.PointProcess.MatchingScenePerfect

/-!
# Deterministically masked original tuples as local configurations

The constructor filters original sample indices and then uses the existing tuple
encoding. Every retained observation and its multiplicity is preserved, including
coincident observations. Masks need only be measurable for the measurable-map
result; no interior, positive-mass or injectivity assumption is used.
-/

open MeasureTheory Set Function
open scoped BigOperators Classical CompactlySupported

noncomputable section
namespace OTSelector.PointProcess.LocalConfiguration

variable {X Ω : Type*} [MetricSpace X] {base : X}

/-- Retain exactly the original indices selected by the endpoint mask, then encode
those original observations using the existing finite-tuple constructor. -/
def ofMaskedTuple {n : ℕ} (base : X) (H : Set Ω) (obs : Ω → X)
    (sample : Fin n → Ω) : LocalConfiguration base :=
  let s := Finset.univ.filter (fun i : Fin n ↦ sample i ∈ H)
  ofTuple base (fun j : Fin s.card ↦ obs (sample (s.orderIsoOfFin rfl j).1))

private theorem sum_retainedIndices {n : ℕ} {M : Type*} [AddCommMonoid M]
    (s : Finset (Fin n)) (w : Fin n → M) :
    (∑ j : Fin s.card, w (s.orderIsoOfFin rfl j).1) = ∑ i ∈ s, w i :=
  ((s.orderIsoOfFin rfl).toEquiv.sum_comp (fun i : s ↦ w i.1)).trans
    (Finset.sum_coe_sort s w)

/-- The actual counting measure contains one Dirac mass for each selected original
label. Repeated observed points contribute repeated masses. -/
@[simp]
theorem countingMeasure_ofMaskedTuple [MeasurableSpace X] {n : ℕ}
    (H : Set Ω) (obs : Ω → X) (sample : Fin n → Ω) :
    countingMeasure (ofMaskedTuple base H obs sample) =
      ∑ i : Fin n, if sample i ∈ H then Measure.dirac (obs (sample i)) else 0 := by
  unfold ofMaskedTuple
  rw [countingMeasure_ofTuple,
    sum_retainedIndices (Finset.univ.filter (fun i : Fin n ↦ sample i ∈ H))
      (fun i ↦ Measure.dirac (obs (sample i))), Finset.sum_filter]

/-- A measurable mask and original observation map give a measurable configuration
map under the full original sample space. -/
@[fun_prop]
theorem measurable_ofMaskedTuple [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [MeasurableSpace Ω] (base : X) {H : Set Ω} (hH : MeasurableSet H)
    {obs : Ω → X} (hobs : Measurable obs) (n : ℕ) :
    Measurable (ofMaskedTuple (n := n) base H obs) := by
  apply measurable_iff_countingMeasure_comp.mpr
  simp_rw [countingMeasure_ofMaskedTuple]
  apply Finset.measurable_sum
  intro i hi
  exact ((Measure.measurable_dirac.comp hobs).comp (measurable_pi_apply i)).ite
    (hH.preimage (measurable_pi_apply i)) measurable_const

/-- Compact test integrals are exactly the sum of masked original observations. -/
@[simp]
theorem testIntegral_ofMaskedTuple [MeasurableSpace X] [BorelSpace X] {n : ℕ}
    (base : X) (H : Set Ω) (obs : Ω → X) (sample : Fin n → Ω) (F : C_c(X, ℝ)) :
    testIntegral (ofMaskedTuple base H obs sample) F =
      ∑ i : Fin n, H.indicator (fun x ↦ F (obs x)) (sample i) := by
  unfold ofMaskedTuple
  rw [testIntegral_ofTuple,
    sum_retainedIndices (Finset.univ.filter (fun i : Fin n ↦ sample i ∈ H))
      (fun i ↦ F (obs (sample i))), Finset.sum_filter]
  rfl

end OTSelector.PointProcess.LocalConfiguration
