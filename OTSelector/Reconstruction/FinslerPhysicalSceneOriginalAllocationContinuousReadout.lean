import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationContinuousProbeLaw
import OTSelector.Probability.DiagonalIteratedWeakReadout

/-!
# Complete original continuous probes after agreement of the limiting law

The real and extended nonnegative readouts remain the actual original finite
allocation experiment. The sample limit is taken at fixed tilt before the
outer tilt limit; bounded continuity supplies integrability internally.
-/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open OTSelector.Probability
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {M Ω : Type*} [MetricSpace M] [ProperSpace M] [PolishSpace M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace Ω] {n : ℕ}

/-- A bounded continuous original endpoint probe has an integrable actual raw
allocation gap. The actual feasible allocation rows supply its probability mass. -/
theorem integrable_originalAllocation_continuous_probe_gap
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
    Integrable (fun w ↦ |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ ap Y w) -
      ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ am Y w|) Renv := by
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
  let obs := physicalSceneProbabilityPlanProbeGap f
  have hInt : Integrable obs (Renv.map pair) :=
    integrable_physicalSceneProbabilityPlanProbeGap f (Renv.map pair)
  have hcomp : Integrable (fun w ↦ obs (pair w)) Renv :=
    (integrable_map_measure (continuous_physicalSceneProbabilityPlanProbeGap f).aestronglyMeasurable
      hpair.aemeasurable).1 hInt
  apply hcomp.congr
  filter_upwards [physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
    Renv μ ν ap Y p hfp, physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
    Renv μ ν am Y p hfm] with w hp hm
  change |(∫ e, f e ∂(physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Y w :
    Measure (M × M))) - ∫ e, f e ∂(physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Y w :
    Measure (M × M))| = _
  rw [hp, hm]

/-- Agreement under the same final original paired law gives vanishing complete
bounded continuous probe gaps in the actual finite allocation experiments. -/
theorem tendsto_originalAllocation_continuous_probe_gap_curry_zero_of_iterated_diagonal
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (Renv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Renv n)]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ ap ℓ n z.1 z.2 k))
    (hmm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ am ℓ n z.1 z.2 k))
    (Y : ∀ n, Ωn n → Fin (n + 1) → M)
    (hY : ∀ n k, Measurable (fun w ↦ Y n w k))
    (p : ∀ n, Ωn n → Fin (n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂Renv n, IsSemidiscreteAllocation μ (p n w) (ap ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂Renv n, IsSemidiscreteAllocation μ (p n w) (am ℓ n w))
    (φ : ℕ → ℕ → ℕ) (ψ : ℕ → ℕ) :
    let _instPlanBorel : BorelSpace (ProbabilityMeasure (M × M)) :=
      probabilityMeasure_weakBorelSpace
    let _instPlanSecond : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
      probabilityMeasure_weakSecondCountable
    let laws := fun ℓ n ↦ physicalSceneOriginalAllocationPlanPairLaw (Renv n) μ ν
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n)
    ∀ (Q : ℕ → ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
      (R : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
      (_hinner : ∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
      (_houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
      (_hdiag : ∀ᵐ s ∂(R : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
        (s.1 : Measure (M × M)) = (s.2 : Measure (M × M)))
      (f : (M × M) →ᵇ ℝ),
      (∀ ℓ n, Integrable (fun w ↦
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) (Y n) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) (Y n) w|) (Renv n)) ∧
      Tendsto (fun z : ℕ × ℕ ↦ ∫ w,
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap (ψ z.1) (φ (ψ z.1) z.2))
            (Y (φ (ψ z.1) z.2)) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am (ψ z.1) (φ (ψ z.1) z.2))
            (Y (φ (ψ z.1) z.2)) w| ∂Renv (φ (ψ z.1) z.2))
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) ∧
      Tendsto (fun z : ℕ × ℕ ↦ ∫⁻ w, ENNReal.ofReal
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap (ψ z.1) (φ (ψ z.1) z.2))
            (Y (φ (ψ z.1) z.2)) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am (ψ z.1) (φ (ψ z.1) z.2))
            (Y (φ (ψ z.1) z.2)) w| ∂Renv (φ (ψ z.1) z.2))
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  let _instPlanBorel : BorelSpace (ProbabilityMeasure (M × M)) :=
    probabilityMeasure_weakBorelSpace
  let _instPlanSecond : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
    probabilityMeasure_weakSecondCountable
  let laws := fun ℓ n ↦ physicalSceneOriginalAllocationPlanPairLaw (Renv n) μ ν
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n)
  dsimp only
  intro Q R hinner houter hdiag f
  have hdiag' : ∀ᵐ s ∂(R : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      s.1 = s.2 := hdiag.mono fun _ hs ↦ Subtype.ext hs
  obtain ⟨_, _, _, _, _, _, _, hreal, _, _, henn⟩ :=
    physicalSceneProbabilityPlanProbeGap_limits_of_iterated_weak
      (fun ℓ n ↦ laws ℓ (φ ℓ n)) Q R ψ hinner houter hdiag' f
  refine ⟨fun ℓ n ↦ integrable_originalAllocation_continuous_probe_gap
    (Renv n) μ ν (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
      (Y n) (hY n) (p n) (hfp ℓ n) (hfm ℓ n) f, ?_, ?_⟩
  · apply hreal.congr'
    apply Eventually.of_forall
    intro z
    exact integral_originalAllocationPlanPairLaw_continuous_probe_eq
      (Renv (φ (ψ z.1) z.2)) μ ν
      (ap (ψ z.1) (φ (ψ z.1) z.2)) (am (ψ z.1) (φ (ψ z.1) z.2))
      (hpm (ψ z.1) (φ (ψ z.1) z.2)) (hmm (ψ z.1) (φ (ψ z.1) z.2))
      (Y (φ (ψ z.1) z.2)) (hY (φ (ψ z.1) z.2)) (p (φ (ψ z.1) z.2))
      (hfp (ψ z.1) (φ (ψ z.1) z.2)) (hfm (ψ z.1) (φ (ψ z.1) z.2)) f
  · apply henn.congr'
    apply Eventually.of_forall
    intro z
    exact lintegral_originalAllocationPlanPairLaw_continuous_probe_eq
      (Renv (φ (ψ z.1) z.2)) μ ν
      (ap (ψ z.1) (φ (ψ z.1) z.2)) (am (ψ z.1) (φ (ψ z.1) z.2))
      (hpm (ψ z.1) (φ (ψ z.1) z.2)) (hmm (ψ z.1) (φ (ψ z.1) z.2))
      (Y (φ (ψ z.1) z.2)) (hY (φ (ψ z.1) z.2)) (p (φ (ψ z.1) z.2))
      (hfp (ψ z.1) (φ (ψ z.1) z.2)) (hfm (ψ z.1) (φ (ψ z.1) z.2)) f

end OTSelector.Reconstruction
