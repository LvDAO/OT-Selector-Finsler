import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationPlanLaw
import OTSelector.Probability.ProbabilityMeasureWeakSecondCountable
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Complete continuous probes retain the original allocation experiment

The probability completion changes only an original null event. Bounded continuous
probes on the original endpoint pair therefore have identical real and extended
absolute-gap expectations under the original paired law and the original raw plans.
-/
open Set Function MeasureTheory ProbabilityTheory TopologicalSpace
open OTSelector.Probability
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {M Ω : Type*} [MetricSpace M] [ProperSpace M] [PolishSpace M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace Ω] {n : ℕ}

/-- A complete original bounded continuous endpoint probe has exactly its original
raw allocation expected absolute gap under the unchanged paired probability law. -/
theorem integral_originalAllocationPlanPairLaw_continuous_probe_eq
    (Renv : Measure Ω) [IsProbabilityMeasure Renv]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hpm : ∀ k, Measurable (fun z : Ω × M ↦ ap z.1 z.2 k))
    (hmm : ∀ k, Measurable (fun z : Ω × M ↦ am z.1 z.2 k))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ k, Measurable (fun w ↦ Y w k))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂Renv, IsSemidiscreteAllocation μ (p w) (ap w))
    (hfm : ∀ᵐ w ∂Renv, IsSemidiscreteAllocation μ (p w) (am w))
    (f : (M × M) →ᵇ ℝ) :
    (∫ s, |(∫ e, f e ∂(s.1 : Measure (M × M))) -
      ∫ e, f e ∂(s.2 : Measure (M × M))|
      ∂(physicalSceneOriginalAllocationPlanPairLaw Renv μ ν ap am hpm hmm Y hY :
        Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))) =
    ∫ w, |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ ap Y w) -
      ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ am Y w| ∂Renv := by
  let _instPlanBorel : BorelSpace (ProbabilityMeasure (M × M)) :=
    probabilityMeasure_weakBorelSpace
  let _instPlanSecond : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
    probabilityMeasure_weakSecondCountable
  let S := ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)
  let pair : Ω → S := fun w ↦
    (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Y w,
      physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Y w)
  have hpair : Measurable pair :=
    (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap hpm Y hY).prodMk
      (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am hmm Y hY)
  let obs : S → ℝ := fun s ↦ |(∫ e, f e ∂(s.1 : Measure (M × M))) -
    ∫ e, f e ∂(s.2 : Measure (M × M))|
  have hobs : Continuous obs :=
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp continuous_fst |>.sub
      ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp continuous_snd)).abs
  change (∫ s, obs s ∂Renv.map pair) = _
  rw [integral_map hpair.aemeasurable hobs.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
    Renv μ ν ap Y p hfp, physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
    Renv μ ν am Y p hfm] with w hp hm
  change |(∫ e, f e ∂(physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Y w :
    Measure (M × M))) - ∫ e, f e ∂(physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Y w :
    Measure (M × M))| = _
  rw [hp, hm]

/-- Extended nonnegative continuous-probe gaps use the same original raw plans. -/
theorem lintegral_originalAllocationPlanPairLaw_continuous_probe_eq
    (Renv : Measure Ω) [IsProbabilityMeasure Renv]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hpm : ∀ k, Measurable (fun z : Ω × M ↦ ap z.1 z.2 k))
    (hmm : ∀ k, Measurable (fun z : Ω × M ↦ am z.1 z.2 k))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ k, Measurable (fun w ↦ Y w k))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂Renv, IsSemidiscreteAllocation μ (p w) (ap w))
    (hfm : ∀ᵐ w ∂Renv, IsSemidiscreteAllocation μ (p w) (am w))
    (f : (M × M) →ᵇ ℝ) :
    (∫⁻ s, ENNReal.ofReal |(∫ e, f e ∂(s.1 : Measure (M × M))) -
      ∫ e, f e ∂(s.2 : Measure (M × M))|
      ∂(physicalSceneOriginalAllocationPlanPairLaw Renv μ ν ap am hpm hmm Y hY :
        Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))) =
    ∫⁻ w, ENNReal.ofReal |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ ap Y w) -
      ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ am Y w| ∂Renv := by
  let _instPlanBorel : BorelSpace (ProbabilityMeasure (M × M)) :=
    probabilityMeasure_weakBorelSpace
  let _instPlanSecond : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
    probabilityMeasure_weakSecondCountable
  let S := ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)
  let pair : Ω → S := fun w ↦
    (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Y w,
      physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Y w)
  have hpair : Measurable pair :=
    (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap hpm Y hY).prodMk
      (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am hmm Y hY)
  let obs : S → ℝ := fun s ↦ |(∫ e, f e ∂(s.1 : Measure (M × M))) -
    ∫ e, f e ∂(s.2 : Measure (M × M))|
  have hobs : Continuous obs :=
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp continuous_fst |>.sub
      ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp continuous_snd)).abs
  change (∫⁻ s, ENNReal.ofReal (obs s) ∂Renv.map pair) = _
  have hobsMeas : Measurable (fun s : S ↦ ENNReal.ofReal (obs s)) :=
    (ENNReal.continuous_ofReal.comp hobs).measurable
  rw [lintegral_map hobsMeas hpair]
  apply lintegral_congr_ae
  filter_upwards [physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
    Renv μ ν ap Y p hfp, physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
    Renv μ ν am Y p hfm] with w hp hm
  change ENNReal.ofReal |(∫ e, f e ∂(physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Y w :
    Measure (M × M))) - ∫ e, f e ∂(physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Y w :
    Measure (M × M))| = _
  rw [hp, hm]

end OTSelector.Reconstruction
