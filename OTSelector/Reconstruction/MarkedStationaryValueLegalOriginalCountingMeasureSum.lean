import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoEdgeSwap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Countable locally finite unions of the actual integer plans

A locally finite sum of actual integer measures remains an actual integer
measure. Finite partial sums converge in the original vague topology through
the genuine summable compact-test integrals, and the proved integer carrier
is closed. This assembles disjoint-cell exchanges without a new carrier axiom.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Classical BigOperators CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
set_option linter.unusedSectionVars false

variable {X ι : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

/-- The literal finite sum of original locally finite measures. -/
def originalFinitePlanSum (μ : ι → LocalFiniteMeasure X) (S : Finset ι) :
    LocalFiniteMeasure X :=
  ⟨∑ i ∈ S, (μ i : Measure X), ⟨by
    intro K hK
    rw [Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr (fun i _ ↦ hK.measure_lt_top)⟩⟩

/-- Finite sums of original integer carriers remain integer. -/
theorem isLegalCountingMeasure_originalFinitePlanSum (base : X)
    (μ : ι → LocalFiniteMeasure X) (hμ : ∀ i, IsLegalCountingMeasure base (μ i))
    (S : Finset ι) : IsLegalCountingMeasure base (originalFinitePlanSum μ S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨LocalConfiguration.ofTuple base (fun i : Fin 0 ↦ Fin.elim0 i), ?_⟩
    apply Subtype.ext
    change LocalConfiguration.countingMeasure
      (LocalConfiguration.ofTuple base (fun i : Fin 0 ↦ Fin.elim0 i)) = _
    simp [LocalConfiguration.countingMeasure_ofTuple, originalFinitePlanSum]
  | @insert i S hi ih =>
    convert isLegalCountingMeasure_add base (μ i) (originalFinitePlanSum μ S) (hμ i) ih using 1
    apply Subtype.ext
    simp [originalFinitePlanSum, Finset.sum_insert, hi]

/-- Finite partial sums converge as actual locally finite measures whenever
their literal full measure sum is finite on compact sets. -/
theorem tendsto_originalFinitePlanSum (μ : ι → LocalFiniteMeasure X)
    [IsFiniteMeasureOnCompacts (Measure.sum (fun i ↦ (μ i : Measure X)))] :
    Tendsto (originalFinitePlanSum μ) atTop
      (𝓝 (⟨Measure.sum (fun i ↦ (μ i : Measure X)), inferInstance⟩ : LocalFiniteMeasure X)) := by
  rw [nhds_induced, Filter.tendsto_comap_iff]
  apply tendsto_pi_nhds.mpr
  intro F
  change Tendsto (fun S ↦ ∫ x, F x ∂(∑ i ∈ S, (μ i : Measure X))) atTop
    (𝓝 (∫ x, F x ∂Measure.sum (fun i ↦ (μ i : Measure X))))
  have hf : Integrable F (Measure.sum (fun i ↦ (μ i : Measure X))) := F.integrable
  have hsum := hasSum_integral_measure hf
  change Tendsto (fun S : Finset ι ↦ ∑ i ∈ S, ∫ x, F x ∂(μ i : Measure X)) atTop
    (𝓝 (∫ x, F x ∂Measure.sum (fun i ↦ (μ i : Measure X)))) at hsum
  simpa only [integral_finsetSum_measure (fun i _ ↦ F.integrable)] using hsum

/-- The original closed integer carrier contains every genuinely locally finite
countable superposition of its original integer pieces. -/
theorem isLegalCountingMeasure_sum (base : X) (μ : ι → LocalFiniteMeasure X)
    (hμ : ∀ i, IsLegalCountingMeasure base (μ i))
    [IsFiniteMeasureOnCompacts (Measure.sum (fun i ↦ (μ i : Measure X)))] :
    IsLegalCountingMeasure base
      ⟨Measure.sum (fun i ↦ (μ i : Measure X)), inferInstance⟩ := by
  exact (isClosed_isLegalCountingMeasure base).mem_of_tendsto
    (tendsto_originalFinitePlanSum μ)
    (.of_forall (fun S ↦ isLegalCountingMeasure_originalFinitePlanSum base μ hμ S))

/-- A locally finite family of actual support windows makes the literal
superposition finite on every compact set, without any global moment premise. -/
theorem originalPlanSum_finiteOnCompacts_of_locallyFinite
    (μ : ι → LocalFiniteMeasure X) (K : ι → Set X) (hK : LocallyFinite K)
    (hsupport : ∀ i, (μ i : Measure X).support ⊆ K i) :
    IsFiniteMeasureOnCompacts (Measure.sum (fun i ↦ (μ i : Measure X))) := by
  classical
  constructor
  intro A hA
  let S := (hK.finite_nonempty_inter_compact hA).toFinset
  have hzero (i : ι) (hi : i ∉ S) : (μ i : Measure X) A = 0 := by
    apply measure_mono_null ?_ (Measure.measure_compl_support (μ := (μ i : Measure X)))
    intro x hx hs
    exact hi ((hK.finite_nonempty_inter_compact hA).mem_toFinset.mpr
      ⟨x, hsupport i hs, hx⟩)
  rw [Measure.sum_apply _ hA.measurableSet, tsum_eq_sum (s := S) hzero]
  exact ENNReal.sum_lt_top.mpr (fun i _ ↦ hA.measure_lt_top)

/-- Locally finite disjoint-cell integer pieces assemble on the actual carrier. -/
theorem isLegalCountingMeasure_sum_of_locallyFinite (base : X)
    (μ : ι → LocalFiniteMeasure X) (hc : ∀ i, IsLegalCountingMeasure base (μ i))
    (K : ι → Set X) (hK : LocallyFinite K)
    (hsupport : ∀ i, (μ i : Measure X).support ⊆ K i) :
    ∃ hsum : IsFiniteMeasureOnCompacts (Measure.sum (fun i ↦ (μ i : Measure X))),
      IsLegalCountingMeasure base ⟨Measure.sum (fun i ↦ (μ i : Measure X)), hsum⟩ := by
  let := originalPlanSum_finiteOnCompacts_of_locallyFinite μ K hK hsupport
  exact ⟨inferInstance, isLegalCountingMeasure_sum base μ hc⟩

end OTSelector.Reconstruction
