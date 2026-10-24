import OTSelector.Transport.Calibration.CompactClockGap
import OTSelector.Probability.CavitySemidiscreteRootedEnergy

/-!
# Rooted clock events in the actual physical plan

An arbitrary actual physical plan is observed in a measurable spatial coordinate
and its original potential clock.  Translating both spatial endpoints preserves
both clocks exactly.  The actual root-window bad-clock mass is therefore a Haar
window readout of the original physical bad-clock event, with its original mass.
-/

open Set Function MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal Classical

noncomputable section
namespace OTSelector.Reconstruction

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

/-- The actual spatial observation of both physical endpoints at one root,
retaining the original potential clock without any change of clock law. -/
def physicalSceneRootedObservation (coord : M → (ι → ℝ)) (u : M → ℝ) (z : ι → ℝ)
    (p : M × M) : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
  ((coord p.1 - z, u p.1), (coord p.2 - z, u p.2))

/-- The actual physical plan, observed at the spatial root and scaled by its
original total-mass factor.  No new source or target law is introduced. -/
def physicalSceneRootedPlan (Γ : Measure (M × M)) (coord : M → (ι → ℝ))
    (u : M → ℝ) (N : ℝ) (z : ι → ℝ) :
    Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
  ENNReal.ofReal N • Γ.map (physicalSceneRootedObservation coord u z)

/-- A source spatial window whose original target clock fails to exceed the
source clock by half the original support-distance gap. -/
def physicalSceneClockBadWindow (U : Set (ι → ℝ)) (gap : ℝ) :
    Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
  {e | e.1.1 ∈ U ∧ e.2.2 - e.1.2 ≤ gap / 2}

omit [Fintype ι] in
/-- The physical rooted observation is measurable in the actual endpoint pair. -/
theorem measurable_physicalSceneRootedObservation
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (z : ι → ℝ) :
    Measurable (physicalSceneRootedObservation coord u z) :=
  (((hcoord.comp measurable_fst).sub measurable_const).prodMk
    (hu.comp measurable_fst)).prodMk
    (((hcoord.comp measurable_snd).sub measurable_const).prodMk
      (hu.comp measurable_snd))

omit [Fintype ι] in
/-- The bad-clock window is measurable in the two actual observed endpoints. -/
theorem measurableSet_physicalSceneClockBadWindow
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) (gap : ℝ) :
    MeasurableSet (physicalSceneClockBadWindow U gap) :=
  (hU.preimage measurable_fst.fst).inter
    (measurableSet_le (measurable_snd.snd.sub measurable_fst.snd) measurable_const)

/-- A measurable original clock suffices to measure the original bad-clock event. -/
theorem measurableSet_originalClockBadEvent_of_measurable
    (u : M → ℝ) (hu : Measurable u) (gap : ℝ) :
    MeasurableSet (originalClockBadEvent u gap) :=
  measurableSet_le ((hu.comp measurable_snd).sub (hu.comp measurable_fst)) measurable_const

omit [Fintype ι] in
/-- The actual rooted bad-clock window reads exactly the original physical
plan's bad-clock indicator in its translated source window. -/
theorem physicalSceneRootedPlan_clockBadWindow
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) (gap : ℝ) :
    physicalSceneRootedPlan Γ coord u N z (physicalSceneClockBadWindow U gap) =
      ENNReal.ofReal N * cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ if p ∈ originalClockBadEvent u gap then 1 else 0) U z := by
  let f := physicalSceneRootedObservation coord u z
  have hf : Measurable f := measurable_physicalSceneRootedObservation coord hcoord u hu z
  have hwindow := measurableSet_physicalSceneClockBadWindow hU gap
  change (ENNReal.ofReal N • Γ.map f) _ = _
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf hwindow,
    ← lintegral_indicator_one (hwindow.preimage hf)]
  congr 1
  apply lintegral_congr
  intro p
  simp only [Set.indicator_apply, mem_preimage, f, physicalSceneRootedObservation,
    physicalSceneClockBadWindow, mem_ofPred_eq, originalClockBadEvent]
  change (if coord p.1 - z ∈ U ∧ u p.2 - u p.1 ≤ gap / 2 then 1 else 0) =
    if coord p.1 - z ∈ U then (if u p.2 - u p.1 ≤ gap / 2 then 1 else 0) else 0
  by_cases hx : coord p.1 - z ∈ U <;>
    simp only [hx, ite_true, ite_false, true_and, false_and]

/-- Haar root averaging bounds actual local bad-clock mass by the original
physical bad-clock mass times the source-window volume.  The original scale
cancels exactly with the actual root-measure normalization. -/
theorem lintegral_physicalSceneRootedPlan_clockBadWindow_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) (gap : ℝ) :
    (∫⁻ z, physicalSceneRootedPlan Γ coord u N z (physicalSceneClockBadWindow U gap)
      ∂cavityRootMeasure volume D N) ≤ volume U * Γ (originalClockBadEvent u gap) := by
  have hbad := measurableSet_originalClockBadEvent_of_measurable u hu gap
  have hw : Measurable (fun p : M × M ↦
      if p ∈ originalClockBadEvent u gap then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite hbad measurable_const measurable_const
  simp_rw [physicalSceneRootedPlan_clockBadWindow Γ coord hcoord u hu N _ U hU gap]
  have h := lintegral_cavityRoot_scaled_window_le volume Γ
    (fun p ↦ coord p.1) (hcoord.comp measurable_fst)
    (fun p ↦ if p ∈ originalClockBadEvent u gap then 1 else 0) hw U hU D N hN
  change (∫⁻ z, ENNReal.ofReal N * cavityRootWindowReadout Γ (fun p ↦ coord p.1)
    (fun p ↦ if p ∈ originalClockBadEvent u gap then 1 else 0) U z
    ∂cavityRootMeasure volume D N) ≤
      volume U * ∫⁻ p, (originalClockBadEvent u gap).indicator (fun _ ↦ 1) p ∂Γ at h
  have hind : (∫⁻ p, (originalClockBadEvent u gap).indicator (fun _ ↦ 1) p ∂Γ) =
      Γ (originalClockBadEvent u gap) := lintegral_indicator_one hbad
  rwa [hind] at h

end OTSelector.Reconstruction
