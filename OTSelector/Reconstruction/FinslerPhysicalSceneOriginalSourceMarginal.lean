import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationPlanLaw
import OTSelector.Probability.ProbabilityMeasureWeakSecondCountable
import OTSelector.MeasureTheory.FixedSourceWeakReadout
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutMacroscopicMarginals

/-!
# Original source marginals in actual paired-plan weak laws

The probability realization retains the original deterministic source almost
surely. Its exact paired pushforward therefore lies in the closed fixed-source
carrier, and both separate weak-limit stages preserve the same source.
-/

open Set Function Filter MeasureTheory OTSelector.Probability
open scoped Topology

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ProperSpace M] [PolishSpace M]

local instance : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
  probabilityMeasure_weakSecondCountable
local instance : BorelSpace (ProbabilityMeasure (M × M)) :=
  probabilityMeasure_weakBorelSpace

/-- Both members of the actual original paired-plan law have exactly the
original source population, on the same original feasible experiment. -/
theorem ae_fst_originalAllocationPlanPairLaw
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (R : Measure Ω) [IsProbabilityMeasure R]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hpm : ∀ k, Measurable (fun z : Ω × M ↦ ap z.1 z.2 k))
    (hmm : ∀ k, Measurable (fun z : Ω × M ↦ am z.1 z.2 k))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ k, Measurable (fun w ↦ Y w k))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (ap w))
    (hfm : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (am w)) :
    ∀ᵐ q ∂(physicalSceneOriginalAllocationPlanPairLaw R μ ν ap am hpm hmm Y hY :
      Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (q.1 : Measure (M × M)).fst = μ ∧ (q.2 : Measure (M × M)).fst = μ := by
  let pair := fun w ↦
    (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Y w,
      physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Y w)
  have hm : Measurable pair :=
    (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap hpm Y hY).prodMk
      (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am hmm Y hY)
  let C : Set (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)) :=
    {q | (q.1 : Measure (M × M)).fst = μ ∧ (q.2 : Measure (M × M)).fst = μ}
  have hC : MeasurableSet C :=
    ((isClosed_probability_fixed_source μ).measurableSet.preimage measurable_fst).inter
      ((isClosed_probability_fixed_source μ).measurableSet.preimage measurable_snd)
  change ∀ᵐ q ∂Measure.map pair R, q ∈ C
  apply (ae_map_iff hm.aemeasurable hC).mpr
  filter_upwards [ae_fst_physicalSceneOriginalAllocationProbabilityPlanFamily
      R μ ν ap Y p hfp,
    ae_fst_physicalSceneOriginalAllocationProbabilityPlanFamily
      R μ ν am Y p hfm] with w hp hm using ⟨hp, hm⟩

/-- A further weak limit of paired probability-plan laws retains the same
almost-sure source marginal in both coordinates. -/
theorem ae_fst_pair_eq_of_tendsto_of_ae
    (P : ℕ → ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (Q : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hweak : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n, ∀ᵐ q ∂(P n :
      Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (q.1 : Measure (M × M)).fst = μ ∧ (q.2 : Measure (M × M)).fst = μ) :
    ∀ᵐ q ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (q.1 : Measure (M × M)).fst = μ ∧ (q.2 : Measure (M × M)).fst = μ := by
  let C : Set (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)) :=
    {q | (q.1 : Measure (M × M)).fst = μ ∧ (q.2 : Measure (M × M)).fst = μ}
  have hC : IsClosed C :=
    ((isClosed_probability_fixed_source μ).preimage continuous_fst).inter
      ((isClosed_probability_fixed_source μ).preimage continuous_snd)
  exact ae_closed_set_of_physicalScene_weak_tendsto Q P hweak C hC hP

/-- Any weak limit of actual original paired allocation laws has exactly the
original source in both plans. No sample-size or iid hypothesis is required. -/
theorem ae_fst_eq_of_originalAllocationPlanPairLaw_tendsto
    {Ωn : ℕ → Type*} [∀ k, MeasurableSpace (Ωn k)]
    (m : ℕ → ℕ) (R : ∀ k, Measure (Ωn k)) [∀ k, IsProbabilityMeasure (R k)]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : ∀ k, Ωn k → M → Fin (m k + 1) → ℝ)
    (hpm : ∀ k i, Measurable (fun z : Ωn k × M ↦ ap k z.1 z.2 i))
    (hmm : ∀ k i, Measurable (fun z : Ωn k × M ↦ am k z.1 z.2 i))
    (Y : ∀ k, Ωn k → Fin (m k + 1) → M)
    (hY : ∀ k i, Measurable (fun w ↦ Y k w i))
    (p : ∀ k, Ωn k → Fin (m k + 1) → ℝ)
    (hfp : ∀ k, ∀ᵐ w ∂R k, IsSemidiscreteAllocation μ (p k w) (ap k w))
    (hfm : ∀ k, ∀ᵐ w ∂R k, IsSemidiscreteAllocation μ (p k w) (am k w))
    (Q : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (hweak : Tendsto (fun k ↦ physicalSceneOriginalAllocationPlanPairLaw
      (R k) μ ν (ap k) (am k) (hpm k) (hmm k) (Y k) (hY k)) atTop (𝓝 Q)) :
    ∀ᵐ q ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (q.1 : Measure (M × M)).fst = μ ∧ (q.2 : Measure (M × M)).fst = μ :=
  ae_fst_pair_eq_of_tendsto_of_ae _ Q μ hweak (fun k ↦
    ae_fst_originalAllocationPlanPairLaw (R k) μ ν (ap k) (am k) (hpm k) (hmm k)
      (Y k) (hY k) (p k) (hfp k) (hfm k))

end OTSelector.Reconstruction
